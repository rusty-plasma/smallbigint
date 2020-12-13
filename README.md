# Smallbigint

[![Docs.rs link](https://docs.rs/smallbigint/badge.svg)](https://docs.rs/smallbigint)
[![Commitizen friendly](https://img.shields.io/badge/commitizen-friendly-brightgreen.svg)](http://commitizen.github.io/cz-cli/)

Two types, `Uint` and `Int`, like `smallvec` for big integers. Anything that fits in 32 bits stays on the stack. Numbers that don't fit are stored in a `Box<num_bigint::BigUint>` / `Box<num_bigint::BigInt>`.

On 64-bit architectures, by default we use `unsafe` to compress the types to 8 bytes, exploiting pointer alignment. This behavior is triggered by the `unsafe-opt` feature, which is enabled by default.

## Implemented traits

Most important numeric traits have been implemented. Here are some that aren't yet; pull requests are welcome!

- Bit operations
- `num_traits::Num`, `num_traits::Signed`, `num_traits::Unsigned`, `num_integer::Integer`, `num_integer::Roots`, `std::iter::Product`, `std::iter::Sum`, `num_traits::pow::Pow`
- Other methods implemented directly on `BigInt`, `BigUint`
- Implement `num_bigint::{ToBigInt, ToBigUint}`

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
