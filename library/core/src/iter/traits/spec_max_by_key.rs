//! Specialization of `Iterator::max_by_key` for primitive keys, on aarch64
//! builds with SVE statically available.
//!
//! The generic `max_by_key` maps every element to a `(key, element)` pair and
//! reduces with `max_by`. The resulting coupled max+index reduction is a shape
//! LLVM only vectorizes by accident of codegen-unit layout: the same source
//! compiles to either a serial `csel` chain or a NEON loop that is 3.4x
//! faster, depending on inlining context. The specialized path pins a faster
//! shape down deterministically. It splits the work into two phases per
//! fixed-size chunk:
//!
//! * phase A produces elements and evaluates the key closure, exactly once
//!   per element and in iteration order, buffering the keys. The API contract
//!   of `max_by_key` constrains only this phase.
//! * phase B finds the chunk maximum — a pure max reduction with no index
//!   coupling, computed with SVE `smaxv` — and only when the chunk improves
//!   on the running best rescans it for the last equal key (`clastb` over an
//!   index vector). Nothing about how the maximum is located is observable.
//!
//! The winning *element* also has to be produced. Side-effect-free
//! random-access iterators (`TrustedRandomAccessNoCoerce`, e.g.
//! `Enumerate<slice::Iter>`) re-fetch it by index at the end; everything else
//! buffers the elements of the current chunk alongside the keys, which is
//! why the element type is restricted to `Copy` data.
//!
//! Ties follow the documented "last maximal element wins" rule: chunks merge
//! with `>=` (a later chunk beats an equal earlier one) and the rescan takes
//! the last equal lane within the chunk.

use crate::cmp::Ordering;

pub(super) trait SpecMaxByKey<B: Ord>: Iterator + Sized {
    fn spec_max_by_key<F: FnMut(&Self::Item) -> B>(self, f: F) -> Option<Self::Item>;
}

impl<I, B> SpecMaxByKey<B> for I
where
    I: Iterator,
    B: Ord,
{
    #[inline]
    default fn spec_max_by_key<F: FnMut(&I::Item) -> B>(self, f: F) -> Option<Self::Item> {
        max_by_key_fallback(self, f)
    }
}

/// The generic algorithm, also used by the specialized impl when the element
/// type is too large to buffer.
#[inline]
pub(super) fn max_by_key_fallback<I, B, F>(it: I, f: F) -> Option<I::Item>
where
    I: Iterator,
    B: Ord,
    F: FnMut(&I::Item) -> B,
{
    #[inline]
    fn key<T, B>(mut f: impl FnMut(&T) -> B) -> impl FnMut(T) -> (B, T) {
        move |x| (f(&x), x)
    }

    #[inline]
    fn compare<T, B: Ord>((x_p, _): &(B, T), (y_p, _): &(B, T)) -> Ordering {
        x_p.cmp(y_p)
    }

    let (_, x) = it.map(key(f)).max_by(compare)?;
    Some(x)
}

#[cfg(all(target_arch = "aarch64", target_feature = "sve"))]
mod chunked {
    use super::super::TrustedLen;
    use crate::cmp;
    use crate::iter::adapters::TrustedRandomAccessNoCoerce;
    use crate::mem::MaybeUninit;

    /// Number of elements whose keys are buffered before reducing.
    const CHUNK: usize = 64;
    /// Upper bound on the stack space spent on the element buffer; larger
    /// element types stay on the generic algorithm.
    const MAX_ITEM_BUF_BYTES: usize = 2048;

    impl<I, B> super::SpecMaxByKey<B> for I
    where
        I: Iterator + TrustedLen,
        I::Item: BufferableItem,
        B: ArgmaxKey,
    {
        #[inline]
        fn spec_max_by_key<F: FnMut(&I::Item) -> B>(self, f: F) -> Option<Self::Item> {
            if const { size_of::<I::Item>() * CHUNK > MAX_ITEM_BUF_BYTES } {
                super::max_by_key_fallback(self, f)
            } else {
                SpecChunked::spec_chunked(self, f)
            }
        }
    }

    /// Second dispatch level: iterators whose elements can be re-fetched by
    /// index skip the element buffer entirely.
    trait SpecChunked<B: ArgmaxKey>: Iterator + Sized {
        fn spec_chunked<F: FnMut(&Self::Item) -> B>(self, f: F) -> Option<Self::Item>;
    }

    impl<I, B> SpecChunked<B> for I
    where
        I: Iterator + TrustedLen,
        I::Item: BufferableItem,
        B: ArgmaxKey,
    {
        #[inline]
        default fn spec_chunked<F: FnMut(&I::Item) -> B>(self, f: F) -> Option<Self::Item> {
            chunked_max_by_key(self, f)
        }
    }

    impl<I, B> SpecChunked<B> for I
    where
        I: Iterator + TrustedLen + TrustedRandomAccessNoCoerce + CloneMarker,
        I::Item: BufferableItem,
        B: ArgmaxKey,
    {
        #[inline]
        fn spec_chunked<F: FnMut(&I::Item) -> B>(self, f: F) -> Option<Self::Item> {
            if I::MAY_HAVE_SIDE_EFFECT {
                // Producing an element runs user code (e.g. a `map` closure):
                // every index must be fetched exactly once, which the
                // buffering algorithm guarantees.
                chunked_max_by_key(self, f)
            } else {
                tra_max_by_key(self, f)
            }
        }
    }

    /// Restricts the element buffer to plain `Copy` data: buffered elements
    /// may be duplicated with a plain read and the non-maximal ones abandoned
    /// without running any drop glue, so buffering is unobservable.
    ///
    /// SAFETY (as a specialization marker): the only impl is the `T: Copy`
    /// blanket impl, and `Copy` implementations cannot be lifetime-dependent.
    #[rustc_unsafe_specialization_marker]
    trait BufferableItem {}

    impl<T: Copy> BufferableItem for T {}

    /// `TrustedRandomAccessNoCoerce` only permits fetching the same index
    /// twice when the iterator is `Clone` (its condition 2); this marker
    /// carries that knowledge through specialization.
    ///
    /// SAFETY (as a specialization marker): the only impl is the `T: Clone`
    /// blanket impl. Every `TrustedRandomAccessNoCoerce` implementor in the
    /// standard library implements `Clone` independently of lifetimes.
    #[rustc_unsafe_specialization_marker]
    trait CloneMarker {}

    impl<T: Clone> CloneMarker for T {}

    /// Key types with a vectorizable chunk-max kernel.
    ///
    /// # Safety
    ///
    /// `prim` must be an order-embedding into the kernel integer type:
    /// `a.cmp(&b)` must agree with the integer comparison of `a.prim()` and
    /// `b.prim()` performed by `prim_ge`, `chunk_max` and `chunk_last_eq`.
    #[rustc_specialization_trait]
    unsafe trait ArgmaxKey: Ord + Copy {
        type Prim: Copy;

        fn prim(self) -> Self::Prim;
        fn prim_ge(a: Self::Prim, b: Self::Prim) -> bool;

        /// Returns the maximum of `buf[..len]`.
        ///
        /// # Safety
        ///
        /// `buf[..len]` must be initialized and valid for reads, `len >= 1`.
        unsafe fn chunk_max(buf: *const Self::Prim, len: usize) -> Self::Prim;

        /// Returns the index of the last element of `buf[..len]` equal to
        /// `max`.
        ///
        /// # Safety
        ///
        /// Same as [`ArgmaxKey::chunk_max`], and `max` must occur in
        /// `buf[..len]`.
        unsafe fn chunk_last_eq(buf: *const Self::Prim, len: usize, max: Self::Prim) -> usize;
    }

    macro_rules! argmax_key_impls {
        ($($t:ty => $prim:ty, $chunk_max:ident, $chunk_last_eq:ident;)*) => ($(
            // SAFETY: the cast to the same-width kernel integer type is
            // lossless and order-preserving, and the kernels implement plain
            // integer max/equality, which agree with `Ord`.
            unsafe impl ArgmaxKey for $t {
                type Prim = $prim;

                #[inline]
                fn prim(self) -> $prim {
                    self as $prim
                }

                #[inline]
                fn prim_ge(a: $prim, b: $prim) -> bool {
                    a >= b
                }

                #[inline]
                unsafe fn chunk_max(buf: *const $prim, len: usize) -> $prim {
                    // SAFETY: forwarded from the caller.
                    unsafe { kernels::$chunk_max(buf, len) }
                }

                #[inline]
                unsafe fn chunk_last_eq(buf: *const $prim, len: usize, max: $prim) -> usize {
                    // SAFETY: forwarded from the caller.
                    unsafe { kernels::$chunk_last_eq(buf, len, max) }
                }
            }
        )*)
    }

    // SVE max reductions exist for all integer lanes, but only the 32/64-bit
    // kernels have been profiled; narrower keys stay on the generic
    // algorithm. `usize`/`isize` are 64-bit on aarch64.
    argmax_key_impls! {
        i32 => i32, chunk_max_s32, chunk_last_eq_s32;
        u32 => u32, chunk_max_u32, chunk_last_eq_u32;
        i64 => i64, chunk_max_s64, chunk_last_eq_s64;
        u64 => u64, chunk_max_u64, chunk_last_eq_u64;
        isize => i64, chunk_max_s64, chunk_last_eq_s64;
        usize => u64, chunk_max_u64, chunk_last_eq_u64;
    }

    // SAFETY: `Ord` for references delegates to the referent, so forwarding
    // `prim` through one dereference preserves the embedding.
    unsafe impl<'a, T: ArgmaxKey> ArgmaxKey for &'a T {
        type Prim = T::Prim;

        #[inline]
        fn prim(self) -> T::Prim {
            (*self).prim()
        }

        #[inline]
        fn prim_ge(a: T::Prim, b: T::Prim) -> bool {
            T::prim_ge(a, b)
        }

        #[inline]
        unsafe fn chunk_max(buf: *const T::Prim, len: usize) -> T::Prim {
            // SAFETY: forwarded from the caller.
            unsafe { T::chunk_max(buf, len) }
        }

        #[inline]
        unsafe fn chunk_last_eq(buf: *const T::Prim, len: usize, max: T::Prim) -> usize {
            // SAFETY: forwarded from the caller.
            unsafe { T::chunk_last_eq(buf, len, max) }
        }
    }

    /// Two-phase chunked argmax. `I: TrustedLen` makes phase A a counted
    /// loop; `I::Item: BufferableItem` guarantees the elements are `Copy`:
    /// buffered copies may be abandoned freely and the winner read out with
    /// `assume_init_read`.
    fn chunked_max_by_key<I, B, F>(mut it: I, mut f: F) -> Option<I::Item>
    where
        I: Iterator + TrustedLen,
        I::Item: BufferableItem,
        B: ArgmaxKey,
        F: FnMut(&I::Item) -> B,
    {
        let mut items = [const { MaybeUninit::<I::Item>::uninit() }; CHUNK];
        let mut keys = [const { MaybeUninit::<B::Prim>::uninit() }; CHUNK];
        let mut best: Option<(B::Prim, I::Item)> = None;

        let (_, upper) = it.size_hint();
        // `TrustedLen` iterators without an upper bound have more than
        // `usize::MAX` elements; consuming one is enough to restore an exact
        // bound and can never yield `None`.
        let mut remaining = match upper {
            Some(n) => n,
            // SAFETY: guaranteed by `TrustedLen`.
            None => {
                let x = unsafe { it.next().unwrap_unchecked() };
                let k = f(&x).prim();
                best = Some((k, x));
                it.size_hint().1.unwrap_or(usize::MAX)
            }
        };

        while remaining > 0 {
            let n = cmp::min(CHUNK, remaining);
            remaining -= n;

            // Phase A: evaluate the key closure exactly once per element, in
            // iteration order, buffering keys and elements. A counted loop
            // (valid per `TrustedLen`) keeps this a single tight loop that
            // slice-backed iterators compile to vectorizable code.
            let kbuf = keys.as_mut_ptr();
            let ibuf = items.as_mut_ptr();
            for i in 0..n {
                // SAFETY: `TrustedLen` guarantees at least `remaining + n`
                // more elements, and `i < n <= CHUNK` bounds the writes.
                unsafe {
                    let x = it.next().unwrap_unchecked();
                    (*kbuf.add(i)).write(f(&x).prim());
                    (*ibuf.add(i)).write(x);
                }
            }

            // Phase B: pure max over the buffered keys, then a last-equal
            // rescan only when the chunk improves on the running best.
            let kbuf = kbuf.cast::<B::Prim>();
            // SAFETY: `keys[..n]` was initialized by phase A and `n >= 1`.
            let cmax = unsafe { B::chunk_max(kbuf, n) };
            let improves = match &best {
                None => true,
                // `>=`: a later chunk wins ties.
                Some((bk, _)) => B::prim_ge(cmax, *bk),
            };
            if improves {
                // SAFETY: same buffer as above and `cmax` is its maximum.
                let last = unsafe { B::chunk_last_eq(kbuf, n, cmax) };
                // SAFETY: `last < n`, so the slot was initialized by phase A,
                // and the element type is `Copy` (via `BufferableItem`),
                // making a copy out of the buffer sound.
                best = Some((cmax, unsafe { items[last].assume_init_read() }));
            }
        }
        best.map(|(_, x)| x)
    }

    /// Buffer-free variant for random-access iterators without side effects:
    /// phase A only stores the keys, and the winning element is re-fetched by
    /// index at the end.
    ///
    /// Callers must have checked `I::MAY_HAVE_SIDE_EFFECT == false` (so
    /// re-producing an element is unobservable) and `I: Clone` via
    /// [`CloneMarker`] (so `TrustedRandomAccessNoCoerce` permits fetching the
    /// winning index a second time). `next()` is never called on `it`.
    fn tra_max_by_key<I, B, F>(mut it: I, mut f: F) -> Option<I::Item>
    where
        I: Iterator + TrustedRandomAccessNoCoerce,
        I::Item: BufferableItem,
        B: ArgmaxKey,
        F: FnMut(&I::Item) -> B,
    {
        let len = it.size();
        let mut keys = [const { MaybeUninit::<B::Prim>::uninit() }; CHUNK];
        let mut best: Option<(B::Prim, usize)> = None;

        let mut base = 0;
        while base < len {
            let n = cmp::min(CHUNK, len - base);

            // Phase A: evaluate the key closure exactly once per element, in
            // iteration order. Only the keys are buffered.
            let kbuf = keys.as_mut_ptr();
            for i in 0..n {
                // SAFETY: `base + i < len == it.size()`, elements have no
                // side effects and the iterator is never advanced; `i < CHUNK`
                // bounds the buffer write.
                unsafe {
                    let x = it.__iterator_get_unchecked(base + i);
                    (*kbuf.add(i)).write(f(&x).prim());
                }
            }

            // Phase B: pure max over the buffered keys, then a last-equal
            // rescan only when the chunk improves on the running best.
            let kbuf = kbuf.cast::<B::Prim>();
            // SAFETY: `keys[..n]` was initialized by phase A and `n >= 1`.
            let cmax = unsafe { B::chunk_max(kbuf, n) };
            let improves = match &best {
                None => true,
                // `>=`: a later chunk wins ties.
                Some((bk, _)) => B::prim_ge(cmax, *bk),
            };
            if improves {
                // SAFETY: same buffer as above and `cmax` is its maximum.
                let last = unsafe { B::chunk_last_eq(kbuf, n, cmax) };
                best = Some((cmax, base + last));
            }
            base += n;
        }

        let (_, idx) = best?;
        // SAFETY: `idx < len`; re-fetching an already-fetched index is
        // permitted because the iterator is `Clone` (via `CloneMarker`) and
        // unobservable because elements have no side effects.
        Some(unsafe { it.__iterator_get_unchecked(idx) })
    }

    mod kernels {
        use crate::arch::aarch64::*;

        macro_rules! sve_argmax_kernels {
            ($max:ident, $last:ident, $t:ty, $min:expr, $idx:ty,
             $cnt:ident, $whilelt:ident, $ptrue:ident, $ld1:ident, $dup:ident,
             $max_m:ident, $maxv:ident, $cmpeq:ident, $index:ident, $clastb:ident) => {
                /// Chunk max via SVE max reduction, one vector per iteration.
                ///
                /// # Safety
                ///
                /// `buf[..len]` must be initialized and valid for reads.
                #[target_feature(enable = "sve")]
                pub(super) unsafe fn $max(buf: *const $t, len: usize) -> $t {
                    let len = len as u64;
                    let vl = $cnt();
                    let mut acc = $dup($min);
                    let mut i = 0u64;
                    while i < len {
                        // SAFETY: the predicate keeps every access inside
                        // `..len`, which the caller guarantees is readable.
                        unsafe {
                            let pg = $whilelt(i, len);
                            let v = $ld1(pg, buf.add(i as usize));
                            acc = $max_m(pg, acc, v);
                        }
                        i += vl;
                    }
                    $maxv($ptrue(), acc)
                }

                /// Index of the last lane of `buf[..len]` equal to `max`,
                /// via `clastb` over an index vector.
                ///
                /// # Safety
                ///
                /// `buf[..len]` must be initialized and valid for reads.
                #[target_feature(enable = "sve")]
                pub(super) unsafe fn $last(buf: *const $t, len: usize, max: $t) -> usize {
                    let len = len as u64;
                    let vl = $cnt();
                    let mut last = 0usize;
                    let mut i = 0u64;
                    while i < len {
                        // SAFETY: as in the max kernel.
                        unsafe {
                            let pg = $whilelt(i, len);
                            let v = $ld1(pg, buf.add(i as usize));
                            let eq = $cmpeq(pg, v, max);
                            let idxv = $index(i as $idx, 1);
                            let l = $clastb(eq, -1, idxv);
                            if l >= 0 {
                                last = l as usize;
                            }
                        }
                        i += vl;
                    }
                    last
                }
            };
        }

        sve_argmax_kernels!(
            chunk_max_s32, chunk_last_eq_s32, i32, i32::MIN, i32, svcntw, svwhilelt_b32_u64,
            svptrue_b32, svld1_s32, svdup_n_s32, svmax_s32_m, svmaxv_s32, svcmpeq_n_s32,
            svindex_s32, svclastb_n_s32
        );
        sve_argmax_kernels!(
            chunk_max_u32, chunk_last_eq_u32, u32, 0, i32, svcntw, svwhilelt_b32_u64, svptrue_b32,
            svld1_u32, svdup_n_u32, svmax_u32_m, svmaxv_u32, svcmpeq_n_u32, svindex_s32,
            svclastb_n_s32
        );
        sve_argmax_kernels!(
            chunk_max_s64, chunk_last_eq_s64, i64, i64::MIN, i64, svcntd, svwhilelt_b64_u64,
            svptrue_b64, svld1_s64, svdup_n_s64, svmax_s64_m, svmaxv_s64, svcmpeq_n_s64,
            svindex_s64, svclastb_n_s64
        );
        sve_argmax_kernels!(
            chunk_max_u64, chunk_last_eq_u64, u64, 0, i64, svcntd, svwhilelt_b64_u64, svptrue_b64,
            svld1_u64, svdup_n_u64, svmax_u64_m, svmaxv_u64, svcmpeq_n_u64, svindex_s64,
            svclastb_n_s64
        );
    }
}
