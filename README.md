# Smallbigint

[![Docs.rs link](https://docs.rs/smallbigint/badge.svg)](https://docs.rs/smallbigint)
[![Commitizen friendly](https://img.shields.io/badge/commitizen-friendly-brightgreen.svg)](http://commitizen.github.io/cz-cli/)

A wrapper around `num_bigint::BigUint` and `num_bigint::BigInt` that
stays out of the heap for small values.

In the current implementation, we go to the heap for anything that
doesn't fit in 32 bits.

This crate already has a lot of relevant methods, but it is not really complete
yet. Patches are welcome!

## To do, and important:

- Implement `std::fmt::{Binary, LowerHex, Octal, UpperHex}` (easy?)
- Implement `num_bigint::{ToBigInt, ToBigUint}`
- Unit tests. Currently there are none, although the code is sufficiently simple
  that there is almost no place where bugs could hide.
- Make this compile against rust stable.

## Other traits and methods still to be implemented:

- Bit operations
- `num_traits::ops::checked` traits
- `num_traits::Num` (easy?)
- `num_traits::One` (easy?)
- `num_traits::Signed`
- `num_traits::Unsigned`
- `num_integer::Integer`
- `num_integer::Roots`
- `std::iter::Product`
- `std::iter::Sum`
- Other methods implemented directly on BigInt, BigUint

## Not done and seems hard:

- `num_traits::pow::Pow`

# License

This project is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or
   http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this project by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
