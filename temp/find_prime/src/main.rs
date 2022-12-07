#![feature(parallelization)]

extern crate parallelization_builtins;

fn is_prime(n: i32) -> i32 {
    if n < 2 {
        return 0;
    }
    if n == 2 {
        return 1;
    }
    let up = (n as f64).sqrt().ceil() as i32;
    for i in 2..=up {
        if n % i == 0 {
            return 0;
        }
    }
    1
}

#[parallel_func]
fn find_prime(a: i32, b: i32) -> i32 {
    if b - a <= 10 {
        let mut ans = 0;
        for i in a..=b {
            ans += is_prime(i);
        }
        return ans;
    }
    let mid = (a + b) / 2;
    let mid_p1 = mid + 1;
    let lo = find_prime(a, mid);
    let hi = find_prime(mid_p1, b);
    return lo + hi;
}

fn find_prime2(a: i32, b: i32) -> i32 {
    if b - a <= 10 {
        let mut ans = 0;
        for i in a..=b {
            ans += is_prime(i);
        }
        return ans;
    }
    let mid = (a + b) / 2;
    let mid_p1 = mid + 1;
    let lo = std::thread::spawn(move || find_prime2(a, mid));
    let hi = find_prime2(mid_p1, b);
    return lo.join().unwrap() + hi;
}

fn find_prime3(a: i32, b: i32) -> i32 {
    if b - a <= 10 {
        let mut ans = 0;
        for i in a..=b {
            ans += is_prime(i);
        }
        return ans;
    }
    let mid = (a + b) / 2;
    let mid_p1 = mid + 1;
    let (lo, hi) = std::thread::scope(|s| {
        let lo = s.spawn(move || find_prime3(a, mid));
        let hi = find_prime3(mid_p1, b);
        (lo.join().unwrap(), hi)
    });
    return lo + hi;
}

use std::{io, thread};
use std::time;

fn main() {
    loop {
        let mut num = String::new();
        io::stdin().read_line(&mut num).expect("read fail");
        if let Ok(num) = num.trim().parse::<i32>() {
            let start = time::SystemTime::now();
            let ans = if num < 2 { 0 } else { find_prime(2, num) };
            let dur = time::SystemTime::now().duration_since(start).unwrap();
            println!("ans :{}, cost: {:?}", ans, dur);
        } else {
            break;
        }
    }
}
