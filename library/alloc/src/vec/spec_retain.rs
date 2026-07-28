//! Specialization of `Vec::retain_mut` for trivially-movable element types.
//!
//! The generic algorithm in `retain_mut` is a single scalar pass with a
//! data-dependent write cursor, which no vectorizer can model. The specialized
//! path splits the work into two phases per fixed-size chunk:
//!
//! * phase A evaluates the predicate for every element of the chunk, exactly
//!   once and in order, recording the answers into a `bool` mask. The API
//!   contract of `retain_mut` constrains only this phase.
//! * phase B compacts the kept elements towards the write cursor using the
//!   mask. Nothing about how elements move is observable, so this phase is
//!   free to use explicit SIMD (SVE `compact`).
//!
//! The specialization is restricted to element types that are `Copy` with no
//! drop glue, so removed elements need no `drop_in_place` and phase B may
//! overwrite whole blocks. It pays for its extra mask traffic with a vector
//! compaction kernel; without one the generic single-pass algorithm wins, so
//! the whole specialized path only exists when SVE is statically available.

use crate::alloc::Allocator;
use crate::vec::Vec;

pub(super) trait SpecRetain<T, A: Allocator> {
    fn spec_retain_mut<F: FnMut(&mut T) -> bool>(&mut self, f: F);
}

impl<T, A: Allocator> SpecRetain<T, A> for Vec<T, A> {
    #[inline]
    default fn spec_retain_mut<F: FnMut(&mut T) -> bool>(&mut self, f: F) {
        self.retain_mut_fallback(f)
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "sve"))]
mod simd {
    use core::arch::aarch64::*;
    use core::{cmp, hint, mem, ptr};

    use crate::alloc::Allocator;
    use crate::vec::Vec;

    /// Number of elements whose predicate results are buffered before
    /// compacting.
    const CHUNK: usize = 64;

    impl<T: CompactElem, A: Allocator> super::SpecRetain<T, A> for Vec<T, A> {
        #[inline]
        fn spec_retain_mut<F: FnMut(&mut T) -> bool>(&mut self, f: F) {
            chunked_retain(self, f)
        }
    }

    /// Element types with a vector compaction kernel.
    ///
    /// # Safety
    ///
    /// Implementors must have the same size and alignment as the kernel's lane
    /// type and no provenance (this rules out references and raw pointers,
    /// which the kernel would round-trip through integer lanes).
    #[rustc_specialization_trait]
    unsafe trait CompactElem: Copy {
        /// Moves the elements of `src[..len]` whose `mask` byte is non-zero to
        /// `dst`, preserving order, and returns how many were moved.
        ///
        /// # Safety
        ///
        /// `src[..len]`, `mask[..len]` must be valid for reads and `dst` valid
        /// for `len` writes. `dst` may overlap `src` only if `dst <= src`.
        unsafe fn compact(
            src: *const Self,
            dst: *mut Self,
            mask: *const bool,
            len: usize,
        ) -> usize;
    }

    macro_rules! compact_impls {
        ($word:ty, $kernel:ident, $($t:ty)*) => ($(
            // SAFETY: `$t` has the same size and alignment as `$word` and no
            // provenance, and compaction only moves bytes around, so
            // reinterpreting the element type is sound.
            unsafe impl CompactElem for $t {
                #[inline]
                unsafe fn compact(
                    src: *const Self,
                    dst: *mut Self,
                    mask: *const bool,
                    len: usize,
                ) -> usize {
                    // SAFETY: forwarded from the caller.
                    unsafe { $kernel(src as *const $word, dst as *mut $word, mask, len) }
                }
            }
        )*)
    }

    // SVE `compact` only exists for 32- and 64-bit lanes; narrower types stay
    // on the generic algorithm. `usize`/`isize` are 64-bit on aarch64.
    compact_impls! { u32, compact32, u32 i32 f32 }
    compact_impls! { u64, compact64, u64 i64 f64 usize isize }

    /// Order-preserving scalar compaction, used by the panic path.
    #[inline]
    unsafe fn scalar_compact<T: Copy>(
        src: *const T,
        dst: *mut T,
        mask: *const bool,
        len: usize,
    ) -> usize {
        let mut write = 0;
        for i in 0..len {
            // SAFETY: `i < len` and both ranges are valid per the caller's
            // contract.
            unsafe {
                if *mask.add(i) {
                    *dst.add(write) = *src.add(i);
                    write += 1;
                }
            }
        }
        write
    }

    macro_rules! sve_compact_kernel {
        ($name:ident, $elem:ty, $cnt:ident, $whilelt:ident, $ld1ub:ident,
         $cmpne:ident, $cntp:ident, $ld1:ident, $compact:ident, $st1:ident) => {
            /// Compacts lanes with `svcompact`, one vector per iteration.
            ///
            /// # Safety
            ///
            /// Same contract as [`CompactElem::compact`].
            #[inline]
            #[target_feature(enable = "sve")]
            unsafe fn $name(
                src: *const $elem,
                dst: *mut $elem,
                mask: *const bool,
                len: usize,
            ) -> usize {
                let len = len as u64;
                let mut read = 0u64;
                let mut write = 0u64;
                let vl = $cnt();

                while read < len {
                    // SAFETY: the predicate keeps every access inside `..len`,
                    // which the caller guarantees is readable/writable.
                    unsafe {
                        let pg = $whilelt(read, len);
                        let flags = $ld1ub(pg, mask.add(read as usize) as *const u8);
                        let keep = $cmpne(pg, flags, 0);
                        let kept = $cntp(pg, keep);
                        let data = $ld1(pg, src.add(read as usize));
                        let compacted = $compact(keep, data);
                        $st1($whilelt(0, kept), dst.add(write as usize), compacted);
                        write += kept;
                    }
                    read += vl;
                }

                write as usize
            }
        };
    }

    sve_compact_kernel!(
        compact32, u32, svcntw, svwhilelt_b32_u64, svld1ub_u32, svcmpne_n_u32, svcntp_b32,
        svld1_u32, svcompact_u32, svst1_u32
    );
    sve_compact_kernel!(
        compact64, u64, svcntd, svwhilelt_b64_u64, svld1ub_u64, svcmpne_n_u64, svcntp_b64,
        svld1_u64, svcompact_u64, svst1_u64
    );

    /// Two-phase `retain_mut` for `Copy` elements without drop glue.
    fn chunked_retain<T, A, F>(v: &mut Vec<T, A>, mut f: F)
    where
        T: CompactElem,
        A: Allocator,
        F: FnMut(&mut T) -> bool,
    {
        let original_len = v.len();
        if original_len == 0 {
            return;
        }

        // All-kept prefix fast path, mirroring `Vec::retain_mut_fallback`:
        // while the predicate keeps saying "keep", nothing has to move at all.
        let mut read = 0;
        loop {
            // SAFETY: `read < original_len`.
            let cur = unsafe { v.get_unchecked_mut(read) };
            if hint::unlikely(!f(cur)) {
                break;
            }
            read += 1;
            if read == original_len {
                return;
            }
        }

        // At least one element is removed. `write` trails `read` from here on,
        // so compaction always stores to a strictly lower address.
        let write = read;
        read += 1;

        // On a panic inside the predicate the observable state must match the
        // generic implementation: elements already decided are compacted, the
        // element that panicked and everything after it are kept, and the
        // `Vec` stays valid. `decided` counts the mask entries filled for the
        // chunk starting at `read`; no element needs dropping because
        // `T: Copy`. The `Vec`'s length is only changed after the guard is
        // disarmed, so `v.len()` is still the original length in `drop`.
        struct PanicGuard<'a, T: Copy, A: Allocator> {
            v: &'a mut Vec<T, A>,
            read: usize,
            write: usize,
            mask: *mut bool,
            decided: usize,
        }

        impl<T: Copy, A: Allocator> Drop for PanicGuard<'_, T, A> {
            #[cold]
            fn drop(&mut self) {
                // SAFETY: `read + decided <= v.len()`, the mask holds `decided`
                // initialized entries, and `write <= read`, so the compaction
                // and the following shift both stay in bounds and only ever
                // copy downwards.
                unsafe {
                    let kept = scalar_compact(
                        self.v.as_ptr().add(self.read),
                        self.v.as_mut_ptr().add(self.write),
                        self.mask,
                        self.decided,
                    );
                    let undecided = self.read + self.decided;
                    let remaining = self.v.len() - undecided;
                    ptr::copy(
                        self.v.as_ptr().add(undecided),
                        self.v.as_mut_ptr().add(self.write + kept),
                        remaining,
                    );
                    self.v.set_len(self.write + kept + remaining);
                }
            }
        }

        let mut mask = [false; CHUNK];
        let mut g = PanicGuard { v, read, write, mask: mask.as_mut_ptr(), decided: 0 };

        while g.read < original_len {
            let chunk = cmp::min(CHUNK, original_len - g.read);
            let base = g.read;
            let elems = g.v.as_mut_ptr();

            // Phase A: evaluate the predicate exactly once per element, in
            // order. Writing the answers to a `bool` array removes the
            // data-dependent write cursor, so this loop is itself vectorizable
            // once the predicate inlines. `decided` is published to the guard
            // as we go.
            for i in 0..chunk {
                // SAFETY: `base + i < original_len` and `i < CHUNK`.
                unsafe {
                    let keep = f(&mut *elems.add(base + i));
                    g.mask.add(i).write(keep);
                }
                g.decided = i + 1;
            }

            // Phase B: move the kept elements down to the write cursor. How
            // they move is not observable, which is what lets an explicit SIMD
            // kernel reorder the copies.
            // SAFETY: `write <= base`, both ranges lie within the allocation,
            // and `dst <= src` so the overlapping case is the permitted one.
            let kept = unsafe { T::compact(elems.add(base), elems.add(g.write), g.mask, chunk) };
            g.write += kept;
            g.read = base + chunk;
            g.decided = 0;
        }

        // No panic happened: commit the length and disarm the guard. In this
        // terminal state the guard's `drop` would compute the same length, but
        // it is `#[cold]` and never inlined, so the hot exit sets the length
        // directly instead of dropping `g`.
        // SAFETY: `write <= original_len` and every slot below it holds a
        // moved element.
        unsafe { g.v.set_len(g.write) };
        mem::forget(g);
    }
}
