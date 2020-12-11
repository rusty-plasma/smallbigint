use anyhow::{ensure, Context, Error};
use num_bigint::BigUint;
use num_traits::identities::Zero;
use std::str::FromStr;
extern crate num_iter;

/// Given a uint (expressed as a string), try to find its prime factorization. The result is
/// expressed as a vector of its prime factors, in ascending order, e.g. ["2", "2", "3"] for
/// input "12". This function only finds the factorization if all prime factors are < the
/// second argument; if any prime factors are >= the second argument, we return None. The
/// second argument should be at least 20, to allow some optimizations.
#[allow(dead_code)]
pub fn find_small_prime_factorization_str(
    num: &str,
    small_prime_limit: &str,
) -> Result<Option<Vec<String>>, Error> {
    let n = BigUint::from_str(num)
        .context("when trying to parse first argument to find_small_prime_factorization_str")?;
    let spl = BigUint::from_str(small_prime_limit)
        .context("when trying to parse second argument to find_small_prime_factorization_str")?;
    ensure!(spl >= 20u8.into()); // enforce what's required by docstring

    if let Some(factors) = find_small_prime_factorization(&n, &spl) {
        let factors_str: Vec<String> = factors.into_iter().map(|x| format!("{}", x)).collect();
        Ok(Some(factors_str))
    } else {
        Ok(None)
    }
}

#[test]
fn find_small_prime_factorization_str_works() {
    assert_eq!(
        find_small_prime_factorization_str("12", "20")
            .unwrap()
            .unwrap(),
        ["2", "2", "3"]
    )
}

fn find_small_prime_factorization(
    v: &BigUint,
    small_prime_limit: &BigUint,
) -> Option<Vec<BigUint>> {
    assert!(v >= &1u8.into());
    let mut current = v.clone();
    let mut factors: Vec<BigUint> = Vec::new();
    while current != 1u8.into() {
        let (newfactor, new) = find_small_prime_factor(&current, small_prime_limit)?;
        factors.push(newfactor);
        current = new;
    }
    Some(factors)
}

/// Find one prime factor of the given number, together with what's left after
/// dividing by that number.
///
/// Only works for small prime factors; returns None when the biggest prime
/// factor is too big. Not optimized at all.
fn find_small_prime_factor(v: &BigUint, small_prime_limit: &BigUint) -> Option<(BigUint, BigUint)> {
    if (v % 2u8).is_zero() {
        return Some((2u8.into(), v / 2u8));
    }
    let mut cur_factor: BigUint = 3u8.into();
    while cur_factor < *small_prime_limit {
        if (v % &cur_factor).is_zero() {
            return Some((cur_factor.clone(), v / cur_factor));
        }
        cur_factor += 2u8;
    }
    None
}
