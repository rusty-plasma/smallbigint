# Smallbigint

A wrapper around `num_bigint::BigUint` and `num_bigint::BigInt` that
stays out of the heap for small values.

In the current implementation, we go to the heap for anything that
doesn't fit in 32 bits.

This crate is already has a lot of relevant methods, but it is not really complete
yet. Patches are welcome!

## To do, and important:

- Switch the "big integer" enum variant to a `Box`, as `BigInt` and
  `BigUint` are actually quite sizeable on the stack.
- Implement `std::fmt::{Binary, LowerHex, Octal, UpperHex}` (easy?)
- Implement `num_bigint::{ToBigInt, ToBigUint}`
- Unit tests. Currently there are none, although the code is sufficiently simple
  that there is almost no place where bugs could hide.
- Continuous integration.
- Make this compile against rust stable.

## Other traits and methods still to be implemented:

- Bit operations
- `num_traits::ops::checked` traits
- `num_integer::Integer`
- `num_traits::Num` (easy?)
- `num_traits::One` (easy?)
- `std::iter::Product`
- `num_integer::Roots`
- `num_traits::Signed`
- `std::iter::Sum`
- `num_traits::Unsigned`
- Other methods implemented directly on BigInt, BigUint

I probably also want conversions from/to 16-bit and 8-bit types.

## Not done and seems hard:

- `num_traits::pow::Pow`
