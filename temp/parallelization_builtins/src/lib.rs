#![feature(lang_items)]

extern crate rayon;

use rayon::prelude::*;

#[lang = "to_once_call_arg1"]
fn to_once_call_arg1<Arg1, T, F: FnOnce(Arg1) -> T>(f: F, arg: Arg1) -> impl FnOnce() -> T {
    let f = || f(arg);
    f
}

#[lang = "to_once_call_arg2"]
fn to_once_call_arg2<Arg1, Arg2, T, F: FnOnce(Arg1, Arg2) -> T>(
    f: F,
    arg1: Arg1,
    arg2: Arg2,
) -> impl FnOnce() -> T {
    let f = || f(arg1, arg2);
    f
}

#[lang = "rayon_join"]
fn rayon_join<T1: Send, T2: Send, F1: FnOnce() -> T1 + Send, F2: FnOnce() -> T2 + Send>(
    f1: F1,
    f2: F2,
) -> (T1, T2) {
    rayon::join(f1, f2)
}