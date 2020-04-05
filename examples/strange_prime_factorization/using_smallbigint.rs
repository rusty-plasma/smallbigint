use failure::{ensure, Error, ResultExt};
use smallbigint::Uint;
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
    let n = Uint::from_str(num)
        .context("when trying to parse first argument to find_small_prime_factorization_str")?;
    let spl = Uint::from_str(small_prime_limit)
        .context("when trying to parse second argument to find_small_prime_factorization_str")?;
    ensure!(spl >= 20); // enforce what's required by docstring

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

fn find_small_prime_factorization(v: &Uint, small_prime_limit: &Uint) -> Option<Vec<Uint>> {
    assert!(v >= 1);
    let mut current = v.clone();
    let mut factors: Vec<Uint> = Vec::new();
    while current != 1 {
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
fn find_small_prime_factor(v: &Uint, small_prime_limit: &Uint) -> Option<(Uint, Uint)> {
    if v % 2u8 == 0 {
        return Some((Uint::small(2), v / 2u8));
    }
    let mut cur_factor = Uint::small(3);
    while cur_factor < small_prime_limit {
        if v % &cur_factor == 0 {
            return Some((cur_factor.clone(), v / cur_factor));
        }
        cur_factor += 2u8;
    }
    None
}
