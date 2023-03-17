//! This module defines types which are thread safe if cfg!(parallel_compiler) is true.
//!
//! `Lrc` is an alias of `Arc` if cfg!(parallel_compiler) is true, `Rc` otherwise.
//!
//! `Lock` is a mutex.
//! It internally uses `parking_lot::Mutex` if cfg!(parallel_compiler) is true,
//! `RefCell` otherwise.
//!
//! `RwLock` is a read-write lock.
//! It internally uses `parking_lot::RwLock` if cfg!(parallel_compiler) is true,
//! `RefCell` otherwise.
//!
//! `MTLock` is a mutex which disappears if cfg!(parallel_compiler) is false.
//!
//! `MTRef` is an immutable reference if cfg!(parallel_compiler), and a mutable reference otherwise.
//!
//! `rustc_erase_owner!` erases an OwningRef owner into Erased or Erased + Send + Sync
//! depending on the value of cfg!(parallel_compiler).

use crate::owning_ref::{Erased, OwningRef};
use std::cell::{Cell, UnsafeCell};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::hash::{BuildHasher, Hash};
use std::intrinsics::likely;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ops::{Deref, DerefMut};
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::ptr::NonNull;

pub use std::sync::atomic::Ordering;
pub use std::sync::atomic::Ordering::SeqCst;

pub use vec::AppendOnlyVec;

mod vec;
use parking_lot::lock_api::RawMutex as _;
use parking_lot::RawMutex;

mod mode {
    use super::Ordering;
    use std::sync::atomic::AtomicU8;

    const UNINITIALIZED: u8 = 0;
    const INACTIVE: u8 = 1;
    const ACTIVE: u8 = 2;

    static MODE: AtomicU8 = AtomicU8::new(UNINITIALIZED);

    #[inline]
    pub fn active() -> bool {
        match MODE.load(Ordering::Relaxed) {
            INACTIVE => false,
            ACTIVE => true,
            // Should panic here. Just for speed test.
            // _ => panic!("uninitialized parallel mode!"),
            _ => false,
        }
    }

    // Only set by the `-Z threads` compile option
    pub fn set(parallel: bool) {
        let set: u8 = if parallel { ACTIVE } else { INACTIVE };
        let previous =
            MODE.compare_exchange(UNINITIALIZED, set, Ordering::Relaxed, Ordering::Relaxed);

        // Check that the mode was either uninitialized or was already set to the requested mode.
        assert!(previous.is_ok() || previous == Err(set));
    }
}

pub use mode::{active, set};
cfg_if! {
    if #[cfg(not(parallel_compiler))] {
        pub auto trait Send {}
        pub auto trait Sync {}

        impl<T> Send for T {}
        impl<T> Sync for T {}

        #[macro_export]
        macro_rules! rustc_erase_owner {
            ($v:expr) => {
                $v.erase_owner()
            }
        }

        use std::ops::Add;

        /// This is a single threaded variant of `AtomicU64`, `AtomicUsize`, etc.
        /// It has explicit ordering arguments and is only intended for use with
        /// the native atomic types.
        /// You should use this type through the `AtomicU64`, `AtomicUsize`, etc, type aliases
        /// as it's not intended to be used separately.
        #[derive(Debug, Default)]
        pub struct Atomic<T: Copy>(Cell<T>);

        impl<T: Copy> Atomic<T> {
            #[inline]
            pub fn new(v: T) -> Self {
                Atomic(Cell::new(v))
            }

            #[inline]
            pub fn into_inner(self) -> T {
                self.0.into_inner()
            }

            #[inline]
            pub fn load(&self, _: Ordering) -> T {
                self.0.get()
            }

            #[inline]
            pub fn store(&self, val: T, _: Ordering) {
                self.0.set(val)
            }

            #[inline]
            pub fn swap(&self, val: T, _: Ordering) -> T {
                self.0.replace(val)
            }
        }

        impl<T: Copy + PartialEq> Atomic<T> {
            #[inline]
            pub fn compare_exchange(&self,
                                    current: T,
                                    new: T,
                                    _: Ordering,
                                    _: Ordering)
                                    -> Result<T, T> {
                let read = self.0.get();
                if read == current {
                    self.0.set(new);
                    Ok(read)
                } else {
                    Err(read)
                }
            }
        }

        impl<T: Add<Output=T> + Copy> Atomic<T> {
            #[inline]
            pub fn fetch_add(&self, val: T, _: Ordering) -> T {
                let old = self.0.get();
                self.0.set(old + val);
                old
            }
        }

        pub type AtomicUsize = Atomic<usize>;
        pub type AtomicBool = Atomic<bool>;
        pub type AtomicU32 = Atomic<u32>;
        pub type AtomicU64 = Atomic<u64>;

        pub fn join<A, B, RA, RB>(oper_a: A, oper_b: B) -> (RA, RB)
            where A: FnOnce() -> RA,
                  B: FnOnce() -> RB
        {
            (oper_a(), oper_b())
        }

        #[macro_export]
        macro_rules! parallel {
            ($($blocks:block),*) => {
                // We catch panics here ensuring that all the blocks execute.
                // This makes behavior consistent with the parallel compiler.
                let mut panic = None;
                $(
                    if let Err(p) = ::std::panic::catch_unwind(
                        ::std::panic::AssertUnwindSafe(|| $blocks)
                    ) {
                        if panic.is_none() {
                            panic = Some(p);
                        }
                    }
                )*
                if let Some(panic) = panic {
                    ::std::panic::resume_unwind(panic);
                }
            }
        }

        pub fn par_for_each_in<T: IntoIterator>(t: T, mut for_each: impl FnMut(T::Item) + Sync + Send) {
            // We catch panics here ensuring that all the loop iterations execute.
            // This makes behavior consistent with the parallel compiler.
            let mut panic = None;
            t.into_iter().for_each(|i| {
                if let Err(p) = catch_unwind(AssertUnwindSafe(|| for_each(i))) {
                    if panic.is_none() {
                        panic = Some(p);
                    }
                }
            });
            if let Some(panic) = panic {
                resume_unwind(panic);
            }
        }

        pub fn par_map<T: IntoIterator, R, C: FromIterator<R>>(
            t: T,
            mut map: impl FnMut(<<T as IntoIterator>::IntoIter as Iterator>::Item) -> R,
        ) -> C {
            // We catch panics here ensuring that all the loop iterations execute.
            let mut panic = None;
            let r = t.into_iter().filter_map(|i| {
                match catch_unwind(AssertUnwindSafe(|| map(i))) {
                    Ok(r) => Some(r),
                    Err(p) => {
                        if panic.is_none() {
                            panic = Some(p);
                        }
                        None
                    }
                }
            }).collect();
            if let Some(panic) = panic {
                resume_unwind(panic);
            }
            r
        }

        pub type MetadataRef = OwningRef<Box<dyn Erased>, [u8]>;

        pub use std::rc::Rc as Lrc;
        pub use std::rc::Weak as Weak;
        pub use std::cell::Ref as ReadGuard;
        pub use std::cell::Ref as MappedReadGuard;
        pub use std::cell::RefMut as WriteGuard;
        pub use std::cell::RefMut as MappedWriteGuard;
        pub use std::cell::RefMut as MappedLockGuard;

        pub use std::cell::OnceCell;

        use std::cell::RefCell as InnerRwLock;

        pub type MTRef<'a, T> = &'a mut T;

        #[derive(Debug, Default)]
        pub struct MTLock<T>(T);

        impl<T> MTLock<T> {
            #[inline(always)]
            pub fn new(inner: T) -> Self {
                MTLock(inner)
            }

            #[inline(always)]
            pub fn into_inner(self) -> T {
                self.0
            }

            #[inline(always)]
            pub fn get_mut(&mut self) -> &mut T {
                &mut self.0
            }

            #[inline(always)]
            pub fn lock(&self) -> &T {
                &self.0
            }

            #[inline(always)]
            pub fn lock_mut(&mut self) -> &mut T {
                &mut self.0
            }
        }

        // FIXME: Probably a bad idea (in the threaded case)
        impl<T: Clone> Clone for MTLock<T> {
            #[inline]
            fn clone(&self) -> Self {
                MTLock(self.0.clone())
            }
        }
    } else {
        pub use std::marker::Send as Send;
        pub use std::marker::Sync as Sync;

        pub use parking_lot::RwLockReadGuard as ReadGuard;
        pub use parking_lot::MappedRwLockReadGuard as MappedReadGuard;
        pub use parking_lot::RwLockWriteGuard as WriteGuard;
        pub use parking_lot::MappedRwLockWriteGuard as MappedWriteGuard;

        pub use parking_lot::MappedMutexGuard as MappedLockGuard;

        pub use std::sync::OnceLock as OnceCell;

        pub use std::sync::atomic::{AtomicBool, AtomicUsize, AtomicU32, AtomicU64};

        pub use std::sync::Arc as Lrc;
        pub use std::sync::Weak as Weak;

        pub type MTRef<'a, T> = &'a T;

        #[derive(Debug, Default)]
        pub struct MTLock<T>(Lock<T>);

        impl<T> MTLock<T> {
            #[inline(always)]
            pub fn new(inner: T) -> Self {
                MTLock(Lock::new(inner))
            }

            #[inline(always)]
            pub fn into_inner(self) -> T {
                self.0.into_inner()
            }

            #[inline(always)]
            pub fn get_mut(&mut self) -> &mut T {
                self.0.get_mut()
            }

            #[inline(always)]
            pub fn lock(&self) -> LockGuard<'_, T> {
                self.0.lock()
            }

            #[inline(always)]
            pub fn lock_mut(&self) -> LockGuard<'_, T> {
                self.lock()
            }
        }

        use parking_lot::RwLock as InnerRwLock;

        use std::thread;

        #[inline]
        pub fn join<A, B, RA: DynSend, RB: DynSend>(oper_a: A, oper_b: B) -> (RA, RB)
        where
            A: FnOnce() -> RA + DynSend,
            B: FnOnce() -> RB + DynSend,
        {
            if mode::active() {
                let oper_a = FromDyn::from(oper_a);
                let oper_b = FromDyn::from(oper_b);
                let (a, b) = rayon::join(move || FromDyn::from(oper_a.into_inner()()), move || FromDyn::from(oper_b.into_inner()()));
                (a.into_inner(), b.into_inner())
            } else {
                (oper_a(), oper_b())
            }
        }

        // This function only works when `mode::active()`.
        pub fn scope<'scope, OP, R>(op: OP) -> R
        where
            OP: FnOnce(&rayon::Scope<'scope>) -> R + DynSend,
            R: DynSend,
        {
            let op = FromDyn::from(op);
            rayon::scope(|s| FromDyn::from(op.into_inner()(s))).into_inner()
        }

        /// Runs a list of blocks in parallel. The first block is executed immediately on
        /// the current thread. Use that for the longest running block.
        #[macro_export]
        macro_rules! parallel {
            (impl $fblock:block [$($c:expr,)*] [$block:expr $(, $rest:expr)*]) => {
                parallel!(impl $fblock [$block, $($c,)*] [$($rest),*])
            };
            (impl $fblock:block [$($blocks:expr,)*] []) => {
                ::rustc_data_structures::sync::scope(|s| {
                    $(let block = rustc_data_structures::sync::FromDyn::from(|| $blocks);
                    s.spawn(move |_| block.into_inner()());)*
                    (|| $fblock)();
                });
            };
            ($fblock:block, $($blocks:block),*) => {
                if rustc_data_structures::sync::active() {
                    // Reverse the order of the later blocks since Rayon executes them in reverse order
                    // when using a single thread. This ensures the execution order matches that
                    // of a single threaded rustc
                    parallel!(impl $fblock [] [$($blocks),*]);
                } else {
                    // We catch panics here ensuring that all the blocks execute.
                    // This makes behavior consistent with the parallel compiler.
                    let mut panic = None;
                    if let Err(p) = ::std::panic::catch_unwind(
                        ::std::panic::AssertUnwindSafe(|| $fblock)
                    ) {
                        if panic.is_none() {
                            panic = Some(p);
                        }
                    }
                    $(
                        if let Err(p) = ::std::panic::catch_unwind(
                            ::std::panic::AssertUnwindSafe(|| $blocks)
                        ) {
                            if panic.is_none() {
                                panic = Some(p);
                            }
                        }
                    )*
                    if let Some(panic) = panic {
                        ::std::panic::resume_unwind(panic);
                    }
                }
            };
        }

        use rayon::iter::{FromParallelIterator, IntoParallelIterator, ParallelIterator};

        pub fn par_for_each_in<I, T: IntoIterator<Item = I> + IntoParallelIterator<Item = I>>(
            t: T,
            for_each: impl Fn(I) + DynSync + DynSend
        ) {
            if mode::active() {
                let for_each = FromDyn::from(for_each);
                let panic: Lock<Option<_>> = Lock::new(None);
                t.into_par_iter().for_each(|i| if let Err(p) = catch_unwind(AssertUnwindSafe(|| for_each(i))) {
                    let mut l = panic.lock();
                    if l.is_none() {
                        *l = Some(p)
                    }
                });

                if let Some(panic) = panic.into_inner() {
                    resume_unwind(panic);
                }
            } else {
                // We catch panics here ensuring that all the loop iterations execute.
                // This makes behavior consistent with the parallel compiler.
                let mut panic = None;
                t.into_iter().for_each(|i| {
                    if let Err(p) = catch_unwind(AssertUnwindSafe(|| for_each(i))) {
                        if panic.is_none() {
                            panic = Some(p);
                        }
                    }
                });
                if let Some(panic) = panic {
                    resume_unwind(panic);
                }
            }
        }

        pub fn par_map<
            I,
            T: IntoIterator<Item = I> + IntoParallelIterator<Item = I>,
            R: std::marker::Send,
            C: FromIterator<R> + FromParallelIterator<R>
        >(
            t: T,
            map: impl Fn(I) -> R + DynSync + DynSend
        ) -> C {
            if mode::active() {
                let panic: Lock<Option<_>> = Lock::new(None);
                let map = FromDyn::from(map);
                // We catch panics here ensuring that all the loop iterations execute.
                let r = t.into_par_iter().filter_map(|i| {
                    match catch_unwind(AssertUnwindSafe(|| map(i))) {
                        Ok(r) => Some(r),
                        Err(p) => {
                            let mut l = panic.lock();
                            if l.is_none() {
                                *l = Some(p);
                            }
                            None
                        },
                    }
                }).collect();

                if let Some(panic) = panic.into_inner() {
                    resume_unwind(panic);
                }
                r
            } else {
                // We catch panics here ensuring that all the loop iterations execute.
                let mut panic = None;
                let r = t.into_iter().filter_map(|i| {
                    match catch_unwind(AssertUnwindSafe(|| map(i))) {
                        Ok(r) => Some(r),
                        Err(p) => {
                            if panic.is_none() {
                                panic = Some(p);
                            }
                            None
                        }
                    }
                }).collect();
                if let Some(panic) = panic {
                    resume_unwind(panic);
                }
                r
            }
        }

        pub type MetadataRef = OwningRef<Box<dyn Erased + Send + Sync>, [u8]>;

        /// This makes locks panic if they are already held.
        /// It is only useful when you are running in a single thread
        const ERROR_CHECKING: bool = false;

        #[macro_export]
        macro_rules! rustc_erase_owner {
            ($v:expr) => {{
                let v = $v;
                ::rustc_data_structures::sync::assert_send_val(&v);
                v.erase_send_sync_owner()
            }}
        }
    }
}

pub unsafe trait DynSend {}
pub unsafe trait DynSync {}

unsafe impl<T> DynSend for T where T: Send {}
unsafe impl<T> DynSync for T where T: Sync {}

#[derive(Copy, Clone)]
pub struct FromDyn<T>(T);

impl<T> FromDyn<T> {
    #[inline(always)]
    pub fn from(val: T) -> Self {
        // Check that `sync::active()` is true on creation so we can
        // implement `Send` and `Sync` for this structure when `T`
        // implements `DynSend` and `DynSync` respectively.
        #[cfg(parallel_compiler)]
        assert!(mode::active());
        FromDyn(val)
    }

    #[inline(always)]
    pub fn into_inner(self) -> T {
        self.0
    }
}

// `FromDyn` is `Send` if `T` is `DynSend`, since it ensures that sync::active() is true.
#[cfg(parallel_compiler)]
unsafe impl<T: DynSend> Send for FromDyn<T> {}

// `FromDyn` is `Sync` if `T` is `DynSync`, since it ensures that sync::active() is true.
#[cfg(parallel_compiler)]
unsafe impl<T: DynSync> Sync for FromDyn<T> {}

impl<T> const std::ops::Deref for FromDyn<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub fn assert_sync<T: ?Sized + Sync>() {}
pub fn assert_send<T: ?Sized + Send>() {}
pub fn assert_send_val<T: ?Sized + Send>(_t: &T) {}
pub fn assert_send_sync_val<T: ?Sized + Sync + Send>(_t: &T) {}

pub trait HashMapExt<K, V> {
    /// Same as HashMap::insert, but it may panic if there's already an
    /// entry for `key` with a value not equal to `value`
    fn insert_same(&mut self, key: K, value: V);
}

impl<K: Eq + Hash, V: Eq, S: BuildHasher> HashMapExt<K, V> for HashMap<K, V, S> {
    fn insert_same(&mut self, key: K, value: V) {
        self.entry(key).and_modify(|old| assert!(*old == value)).or_insert(value);
    }
}

struct LockRaw {
    single_thread: bool,
    borrow: Cell<bool>,
    mutex: RawMutex,
}

pub struct Lock<T> {
    raw: LockRaw,
    data: UnsafeCell<T>,
}

impl<T: Debug> Debug for Lock<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.try_lock() {
            Some(guard) => f.debug_struct("Lock").field("data", &&*guard).finish(),
            None => {
                struct LockedPlaceholder;
                impl Debug for LockedPlaceholder {
                    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                        f.write_str("<locked>")
                    }
                }

                f.debug_struct("Lock").field("data", &LockedPlaceholder).finish()
            }
        }
    }
}

#[inline(never)]
fn try_lock_raw(raw: &LockRaw) -> bool {
    if likely(raw.single_thread) {
        if raw.borrow.get() {
            return false;
        } else {
            raw.borrow.set(true);
            true
        }
    } else {
        raw.mutex.try_lock()
    }
}

#[inline(never)]
fn lock_raw(raw: &LockRaw) {
    if likely(raw.single_thread) {
        assert!(!raw.borrow.get());
        raw.borrow.set(true);
    } else {
        raw.mutex.lock();
    }
}

impl<T> Lock<T> {
    #[inline]
    pub fn new(val: T) -> Self {
        Lock {
            raw: LockRaw {
                single_thread: !active(),
                borrow: Cell::new(false),
                mutex: RawMutex::INIT,
            },

            data: UnsafeCell::new(val),
        }
    }

    #[inline]
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }

    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        self.data.get_mut()
    }

    #[inline(always)]
    pub fn try_lock(&self) -> Option<LockGuard<'_, T>> {
        if try_lock_raw(&self.raw) {
            Some(LockGuard {
                value: unsafe { NonNull::new_unchecked(self.data.get()) },
                _raw: BorrowLockRaw { raw: &self.raw },
                marker: PhantomData,
            })
        } else {
            None
        }
    }

    #[inline(always)]
    #[track_caller]
    pub fn lock(&self) -> LockGuard<'_, T> {
        lock_raw(&self.raw);
        LockGuard {
            value: unsafe { NonNull::new_unchecked(self.data.get()) },
            _raw: BorrowLockRaw { raw: &self.raw },
            marker: PhantomData,
        }
    }

    #[inline(always)]
    #[track_caller]
    pub fn with_lock<F: FnOnce(&mut T) -> R, R>(&self, f: F) -> R {
        f(&mut *self.lock())
    }

    #[inline(always)]
    #[track_caller]
    pub fn borrow(&self) -> LockGuard<'_, T> {
        self.lock()
    }

    #[inline(always)]
    #[track_caller]
    pub fn borrow_mut(&self) -> LockGuard<'_, T> {
        self.lock()
    }
}

impl<T: Default> Default for Lock<T> {
    #[inline]
    fn default() -> Self {
        Lock::new(T::default())
    }
}

// FIXME: Probably a bad idea
impl<T: Clone> Clone for Lock<T> {
    #[inline]
    fn clone(&self) -> Self {
        Lock::new(self.borrow().clone())
    }
}

// Just for speed test
unsafe impl<T: Send> std::marker::Send for Lock<T> {}
unsafe impl<T: Send> std::marker::Sync for Lock<T> {}

struct BorrowLockRaw<'a> {
    raw: &'a LockRaw,
}

pub struct LockGuard<'a, T> {
    value: NonNull<T>,
    _raw: BorrowLockRaw<'a>,
    marker: PhantomData<&'a mut T>,
}

impl<T> const Deref for LockGuard<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        unsafe { self.value.as_ref() }
    }
}

impl<T> const DerefMut for LockGuard<'_, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.value.as_mut() }
    }
}

#[inline(never)]
unsafe fn unlock_mt(raw: &LockRaw) {
    raw.mutex.unlock()
}

impl<'a> Drop for BorrowLockRaw<'a> {
    #[inline]
    fn drop(&mut self) {
        if likely(self.raw.single_thread) {
            debug_assert!(self.raw.borrow.get());
            self.raw.borrow.set(false);
        } else {
            unsafe { unlock_mt(self.raw) }
        }
    }
}

#[derive(Debug, Default)]
pub struct RwLock<T>(InnerRwLock<T>);

impl<T> RwLock<T> {
    #[inline(always)]
    pub fn new(inner: T) -> Self {
        RwLock(InnerRwLock::new(inner))
    }

    #[inline(always)]
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }

    #[inline(always)]
    pub fn get_mut(&mut self) -> &mut T {
        self.0.get_mut()
    }

    #[cfg(not(parallel_compiler))]
    #[inline(always)]
    #[track_caller]
    pub fn read(&self) -> ReadGuard<'_, T> {
        self.0.borrow()
    }

    #[cfg(parallel_compiler)]
    #[inline(always)]
    pub fn read(&self) -> ReadGuard<'_, T> {
        if ERROR_CHECKING {
            self.0.try_read().expect("lock was already held")
        } else {
            self.0.read()
        }
    }

    #[inline(always)]
    #[track_caller]
    pub fn with_read_lock<F: FnOnce(&T) -> R, R>(&self, f: F) -> R {
        f(&*self.read())
    }

    #[cfg(not(parallel_compiler))]
    #[inline(always)]
    pub fn try_write(&self) -> Result<WriteGuard<'_, T>, ()> {
        self.0.try_borrow_mut().map_err(|_| ())
    }

    #[cfg(parallel_compiler)]
    #[inline(always)]
    pub fn try_write(&self) -> Result<WriteGuard<'_, T>, ()> {
        self.0.try_write().ok_or(())
    }

    #[cfg(not(parallel_compiler))]
    #[inline(always)]
    #[track_caller]
    pub fn write(&self) -> WriteGuard<'_, T> {
        self.0.borrow_mut()
    }

    #[cfg(parallel_compiler)]
    #[inline(always)]
    pub fn write(&self) -> WriteGuard<'_, T> {
        if ERROR_CHECKING {
            self.0.try_write().expect("lock was already held")
        } else {
            self.0.write()
        }
    }

    #[inline(always)]
    #[track_caller]
    pub fn with_write_lock<F: FnOnce(&mut T) -> R, R>(&self, f: F) -> R {
        f(&mut *self.write())
    }

    #[inline(always)]
    #[track_caller]
    pub fn borrow(&self) -> ReadGuard<'_, T> {
        self.read()
    }

    #[inline(always)]
    #[track_caller]
    pub fn borrow_mut(&self) -> WriteGuard<'_, T> {
        self.write()
    }

    #[cfg(not(parallel_compiler))]
    #[inline(always)]
    pub fn clone_guard<'a>(rg: &ReadGuard<'a, T>) -> ReadGuard<'a, T> {
        ReadGuard::clone(rg)
    }

    #[cfg(parallel_compiler)]
    #[inline(always)]
    pub fn clone_guard<'a>(rg: &ReadGuard<'a, T>) -> ReadGuard<'a, T> {
        ReadGuard::rwlock(&rg).read()
    }

    #[cfg(not(parallel_compiler))]
    #[inline(always)]
    pub fn leak(&self) -> &T {
        ReadGuard::leak(self.read())
    }

    #[cfg(parallel_compiler)]
    #[inline(always)]
    pub fn leak(&self) -> &T {
        let guard = self.read();
        let ret = unsafe { &*(&*guard as *const T) };
        std::mem::forget(guard);
        ret
    }
}

// FIXME: Probably a bad idea
impl<T: Clone> Clone for RwLock<T> {
    #[inline]
    fn clone(&self) -> Self {
        RwLock::new(self.borrow().clone())
    }
}

#[derive(Debug)]
pub struct WorkerLocal<T> {
    single_thread: bool,
    inner: T,
    mt_inner: Option<rayon_core::WorkerLocal<T>>,
}

impl<T> WorkerLocal<T> {
    /// Creates a new worker local where the `initial` closure computes the
    /// value this worker local should take for each thread in the thread pool.
    #[inline]
    pub fn new<F: FnMut(usize) -> T>(mut f: F) -> WorkerLocal<T> {
        if !active() {
            WorkerLocal { single_thread: true, inner: f(0), mt_inner: None }
        } else {
            WorkerLocal {
                single_thread: false,
                inner: unsafe { MaybeUninit::uninit().assume_init() },
                mt_inner: Some(rayon_core::WorkerLocal::new(f)),
            }
        }
    }

    /// Returns the worker-local value for each thread
    #[inline]
    pub fn into_inner(self) -> Vec<T> {
        if self.single_thread { vec![self.inner] } else { self.mt_inner.unwrap().into_inner() }
    }
}

impl<T> Deref for WorkerLocal<T> {
    type Target = T;

    #[inline(always)]
    fn deref(&self) -> &T {
        if self.single_thread { &self.inner } else { self.mt_inner.as_ref().unwrap().deref() }
    }
}

// Just for speed test
unsafe impl<T: Send> std::marker::Sync for WorkerLocal<T> {}

/// A type which only allows its inner value to be used in one thread.
/// It will panic if it is used on multiple threads.
#[derive(Debug)]
pub struct OneThread<T> {
    #[cfg(parallel_compiler)]
    thread: thread::ThreadId,
    inner: T,
}

#[cfg(parallel_compiler)]
unsafe impl<T> std::marker::Sync for OneThread<T> {}
#[cfg(parallel_compiler)]
unsafe impl<T> std::marker::Send for OneThread<T> {}

impl<T> OneThread<T> {
    #[inline(always)]
    fn check(&self) {
        #[cfg(parallel_compiler)]
        assert_eq!(thread::current().id(), self.thread);
    }

    #[inline(always)]
    pub fn new(inner: T) -> Self {
        OneThread {
            #[cfg(parallel_compiler)]
            thread: thread::current().id(),
            inner,
        }
    }

    #[inline(always)]
    pub fn into_inner(value: Self) -> T {
        value.check();
        value.inner
    }
}

impl<T> Deref for OneThread<T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.check();
        &self.inner
    }
}

impl<T> DerefMut for OneThread<T> {
    fn deref_mut(&mut self) -> &mut T {
        self.check();
        &mut self.inner
    }
}
