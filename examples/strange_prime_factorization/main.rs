//! This directory contains an example with factorizing big numbers, using a naive (slow) algorithm.
//!
//! You can use this in one of two ways:
//!
//!   1. You can execute this example from the command line, to find "nice" prime factorizations of
//!      large numbers: start at a big number and it tries to find numbers below that that have
//!      nicer and nicer prime factorizations:
//!
//!          cargo run --release --example strange_prime_factorization -- -- 9007199254740991
//!
//!   2. You can execute benchmarks with `cargo +nightly bench --features bench,benchall --example strange_prime_factorization`.
//!      Rust nightly is needed for benchmarks.
//!
#![cfg_attr(feature = "bench", feature(test))]

mod using_bigint;
mod using_smallbigint;
mod using_u32;
#[cfg(feature = "bench")]
extern crate test;
#[cfg(feature = "bench")]
use test::Bencher;

use exitfailure::ExitFailure;
// use failure::ResultExt;
use lazy_static::lazy_static;
use smallbigint::Int;
use std::collections::BTreeSet;
use std::str::FromStr;
use structopt::StructOpt;

#[cfg(feature = "bench")]
const SMALL_PRIME_LIMIT: &str = ONE_MILLION;
#[cfg(feature = "bench")]
const ONE_MILLION: &str = "1000000";

lazy_static! {
    pub static ref DEFAULT_TARGET: Int = Int::from_str(&"9007199254740991").unwrap();
}

/// Find numbers with a nice prime factorization. Currently, a "nice" prime is one which has few
/// distinct prime factors. We start at a number, find its prime factors, then keep decrementing
/// forever and on the way we report any numbers that aren't worse than the last reported.
///
/// This implementation uses a very naive prime factorization algorithm, which only works when
/// all prime factors are reasonably small (under approximately one million).
#[derive(Debug, StructOpt)]
struct Cli {
    #[structopt(default_value = "1000000000000000")]
    start: String,
    #[structopt(default_value = "-1")]
    step: String,
    #[structopt(default_value = "1000000")]
    small_prime_limit: String,
}

/// Iterator for an exclusive numeric range specified by strings.
fn range(start: &str, stop: &str, step: &str) -> impl Iterator<Item = String> {
    num_iter::range_step_inclusive(
        Int::from_str(start).unwrap(),
        Int::from_str(stop).unwrap(),
        Int::from_str(step).unwrap(),
    )
    .map(|x| format!("{}", x))
}

fn main() -> Result<(), ExitFailure> {
    let args = Cli::from_args();

    let mut best_quality = 99999;
    for n in range(&args.start, "2", &args.step) {
        match using_smallbigint::find_small_prime_factorization_str(&n, &args.small_prime_limit)
            .unwrap()
        {
            None => println!("  Failed to compute factorization for {}", n),
            Some(factors) => {
                let quality = unique_elements(&factors);
                // Only report results that are at most 2 worse than the current best
                if quality <= best_quality + 2 {
                    best_quality = quality.min(best_quality);
                    println!(
                        "- {} has {} unique factors: [{}]",
                        n,
                        &quality,
                        factors.join(", ")
                    );
                }
            }
        }
    }
    Ok(())
}

fn unique_elements<T: Ord>(factors: impl AsRef<[T]>) -> usize {
    factors.as_ref().iter().collect::<BTreeSet<&T>>().len()
}

#[cfg(feature = "bench")]
#[bench]
fn strange_factor_100000000000000_bigint(bencher: &mut Bencher) {
    use using_bigint::find_small_prime_factorization_str;

    bencher.iter(|| {
        for v in range("100000000000000", "100000000000006", "1") {
            test::bench::black_box(find_small_prime_factorization_str(&v, SMALL_PRIME_LIMIT))
                .unwrap();
        }
    });
}

#[cfg(feature = "bench")]
#[bench]
fn strange_factor_100000000000000_smallbigint(bencher: &mut Bencher) {
    use using_smallbigint::find_small_prime_factorization_str;

    bencher.iter(|| {
        for v in range("100000000000000", "100000000000006", "1") {
            test::bench::black_box(find_small_prime_factorization_str(&v, SMALL_PRIME_LIMIT))
                .unwrap();
        }
    });
}

#[cfg(all(feature = "bench", feature = "benchall"))]
#[bench]
fn strange_factor_100000000000000_u32(bencher: &mut Bencher) {
    use using_u32::find_small_prime_factorization_str;

    bencher.iter(|| {
        for v in range("100000000000000", "100000000000006", "1") {
            test::bench::black_box(find_small_prime_factorization_str(&v, SMALL_PRIME_LIMIT))
                .unwrap();
        }
    });
}

#[cfg(feature = "bench")]
#[bench]
fn strange_factor_100000_bigint(bencher: &mut Bencher) {
    use using_bigint::find_small_prime_factorization_str;

    bencher.iter(|| {
        for v in range("100000", "100010", "1") {
            test::bench::black_box(find_small_prime_factorization_str(&v, SMALL_PRIME_LIMIT))
                .unwrap();
        }
    });
}

#[cfg(feature = "bench")]
#[bench]
fn strange_factor_100000_smallbigint(bencher: &mut Bencher) {
    use using_smallbigint::find_small_prime_factorization_str;

    bencher.iter(|| {
        for v in range("100000", "100010", "1") {
            test::bench::black_box(find_small_prime_factorization_str(&v, SMALL_PRIME_LIMIT))
                .unwrap();
        }
    });
}

#[cfg(feature = "bench")]
#[bench]
fn strange_factor_100000_u32(bencher: &mut Bencher) {
    use using_u32::find_small_prime_factorization_str;

    bencher.iter(|| {
        for v in range("100000", "100010", "1") {
            test::bench::black_box(find_small_prime_factorization_str(&v, SMALL_PRIME_LIMIT))
                .unwrap();
        }
    });
}

#[cfg(test)]
mod tests {
    use super::{using_bigint, using_smallbigint, using_u32};
    use std::collections::BTreeSet;
    #[test]
    fn btreeset_duplicates() {
        let mut bs = BTreeSet::<u8>::new();
        bs.insert(5);
        bs.insert(6);
        bs.insert(5);
        assert_eq!(bs.len(), 2); // not 3
    }

    #[test]
    fn works_using_u32() {
        assert_eq!(
            using_u32::find_small_prime_factorization_str("100000000", "1000000")
                .unwrap()
                .unwrap(),
            vec!["2", "2", "2", "2", "2", "2", "2", "2", "5", "5", "5", "5", "5", "5", "5", "5"]
        )
    }
    #[test]
    fn works_using_smallbigint() {
        assert_eq!(
            using_smallbigint::find_small_prime_factorization_str("100000000", "1000000")
                .unwrap()
                .unwrap(),
            vec!["2", "2", "2", "2", "2", "2", "2", "2", "5", "5", "5", "5", "5", "5", "5", "5"]
        )
    }
    #[test]
    fn works_using_bigint() {
        assert_eq!(
            using_bigint::find_small_prime_factorization_str("100000000", "1000000")
                .unwrap()
                .unwrap(),
            vec!["2", "2", "2", "2", "2", "2", "2", "2", "5", "5", "5", "5", "5", "5", "5", "5"]
        )
    }
}
