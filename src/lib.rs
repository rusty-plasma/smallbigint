//! A wrapper around [`num_bigint::BigUint`] and [`num_bigint::BigInt`] that
//! stays out of the heap for small values.
//!
//! In the current implementation, we go to the heap for anything that
//! doesn't fit in 32 bits.
//!
//! This crate already has a lot of relevant methods, but it is not really complete
//! yet. Patches are welcome!
//!
//! Care has usually been taken to avoid allocation in the methods here, but not in
//! all cases.
//!
//! ## To do, and important:
//!
//! - Implement `std::fmt::{Binary, LowerHex, Octal, UpperHex}` (easy?)
//! - Implement `num_bigint::{ToBigInt, ToBigUint}`
//! - Unit tests. Currently there are none, although the code is sufficiently simple
//!   that there is almost no place where bugs could hide.
//! - Make this compile against rust stable.
//!
//! ## Other traits and methods still to be implemented:
//!
//! - Bit operations
//! - [`num_traits::ops::checked`] traits
//! - [`num_traits::Num`] (easy?)
//! - [`num_traits::One`] (easy?)
//! - [`num_traits::Signed`]
//! - [`num_traits::Unsigned`]
//! - [`num_integer::Integer`]
//! - [`num_integer::Roots`]
//! - [`std::iter::Product`]
//! - [`std::iter::Sum`]
//! - Other methods implemented directly on BigInt, BigUint
//!
//! ## Not done and seems hard:
//!
//! - [`num_traits::pow::Pow`]

use either::{Either, Left, Right};
use num_bigint::{BigInt, BigUint, ParseBigIntError, ToBigUint};
use num_traits::cast::{FromPrimitive, ToPrimitive};
use std::borrow::Borrow;
use std::borrow::Cow::{self, Borrowed, Owned};
use std::cmp::Ordering;
use std::convert::{From, Into, TryFrom, TryInto};
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};

use std::str::FromStr;

mod to_primitive_generic;
// Don't want to commit to exporting this yet
use to_primitive_generic::ToGeneric;

#[allow(non_camel_case_types)]
type uint = u32;
#[allow(non_camel_case_types)]
type int = i32;

#[derive(Clone, Debug)]
pub struct Uint(Either<uint, Box<BigUint>>);
#[derive(Clone, Debug)]
pub struct Int(Either<int, Box<BigInt>>);

impl Uint {
    pub const fn zero() -> Self {
        Self::small(0)
    }
    pub const fn small(x: uint) -> Self {
        Uint(Left(x))
    }
    pub fn big(v: BigUint) -> Self {
        Uint(Right(Box::new(v)))
    }
    /// A convenience function to get or convert to a [`BigUint`], without
    /// having to copy any heap-allocated data if we are already a `&BigUint`.
    ///
    /// Given a variable `x : &Uint`, the following pattern may be useful to get
    /// a `&BigUint` without unneeded allocation. If the [`Uint`] is small, then
    /// we create a new temporary [`BigUint`] from it and the Rust compiler can
    /// automatically figure out the lifetimes.
    ///
    /// ```rust
    /// # use smallbigint::Uint; use num_bigint::BigUint;
    /// # use std::borrow::Borrow;
    /// # let x = Uint::small(42);
    /// let x1 = x.cow_big();
    /// let x2 : &BigUint = x1.borrow();
    /// ```
    ///
    /// We have to
    ///
    /// - Put `x1` in a variable, so that the compiler can figure out the lifetimes
    /// - Put `x2` in a variable, otherwise the Rust compiler can't figure out its type.
    pub fn cow_big(&self) -> Cow<BigUint> {
        match self.0 {
            Left(x) => Owned(x.into()),
            Right(ref b) => Borrowed(b),
        }
    }
    /// If we're storing a [`BigUint`] but it would fit in a small uint instead, then
    /// convert, and discard the heap-allocated memory.
    pub fn normalize(self) -> Self {
        match self.0 {
            Left(x) => Self(Left(x)),
            Right(b) => {
                if let Some(x) = b.to_u32() {
                    Self(Left(x)) // drop the memory
                } else {
                    Self(Right(b))
                }
            }
        }
    }
}

impl Int {
    pub const fn zero() -> Self {
        Self::small(0)
    }
    pub const fn small(x: int) -> Self {
        Int(Left(x))
    }
    pub fn big(v: BigInt) -> Self {
        Int(Right(Box::new(v)))
    }
    /// A convenience function to get or convert to a [`BigInt`], without
    /// having to copy any heap-allocated data if we are already a `&BigInt`.
    ///
    /// Given a variable `x : &Int`, the following pattern may be useful to get
    /// a `&BigInt` without unneeded allocation. If the [`Int`] is small, then
    /// we create a new temporary [`BigInt`] from it and the Rust compiler can
    /// automatically figure out the lifetimes.
    ///
    /// ```rust
    /// # use smallbigint::Int; use num_bigint::BigInt;
    /// # use std::borrow::Borrow;
    /// # let x = Int::small(42);
    /// let x1 = x.cow_big();
    /// let x2 : &BigInt = x1.borrow();
    /// ```
    ///
    /// We have to
    ///
    /// - Put `x1` in a variable, so that the compiler can figure out the lifetimes
    /// - Put `x2` in a variable, otherwise the Rust compiler can't figure out its type.
    pub fn cow_big(&self) -> Cow<BigInt> {
        match self.0 {
            Left(x) => Owned(x.into()),
            Right(ref b) => Borrowed(b),
        }
    }
    /// If we're storing a [`BigInt`] but it would fit in a small int instead, then
    /// convert, and discard the heap-allocated memory.
    pub fn normalize(self) -> Self {
        match self.0 {
            Left(x) => Self(Left(x)),
            Right(b) => {
                if let Some(x) = b.to_i32() {
                    Self(Left(x)) // drop the memory
                } else {
                    Self(Right(b))
                }
            }
        }
    }
}

// -- Basic stuff between the same signedness --

impl Default for Uint {
    fn default() -> Self {
        Self::zero()
    }
}

impl Default for Int {
    fn default() -> Self {
        Self::zero()
    }
}

/// A utility extension function to make it easier to transform values in-place. Works
/// well automatically for types with a cheap [`Default`].
trait Transformable: Sized {
    fn transform(&mut self, f: impl FnOnce(Self) -> Self);
}

impl<T: Default> Transformable for T {
    fn transform(&mut self, f: impl FnOnce(Self) -> Self) {
        let mut tmp = Self::default();
        std::mem::swap(&mut tmp, self);
        *self = f(tmp)
    }
}

impl Display for Uint {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.0 {
            Left(x) => Display::fmt(x, f),
            Right(b) => Display::fmt(b, f),
        }
    }
}

impl Display for Int {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.0 {
            Left(x) => Display::fmt(x, f),
            Right(b) => Display::fmt(b, f),
        }
    }
}

impl From<BigUint> for Uint {
    fn from(v: BigUint) -> Self {
        Uint(Right(Box::new(v)))
    }
}
impl From<Uint> for BigUint {
    fn from(v: Uint) -> BigUint {
        match v.0 {
            Left(x) => x.into(),
            Right(b) => *b,
        }
    }
}

impl From<BigInt> for Int {
    fn from(v: BigInt) -> Self {
        Int(Right(Box::new(v)))
    }
}
impl From<Int> for BigInt {
    fn from(v: Int) -> BigInt {
        match v.0 {
            Left(x) => x.into(),
            Right(b) => *b,
        }
    }
}

impl FromStr for Uint {
    type Err = ParseBigIntError;
    fn from_str(s: &str) -> Result<Self, ParseBigIntError> {
        Ok(Uint::big(BigUint::from_str(s)?).normalize())
    }
}

impl FromStr for Int {
    type Err = ParseBigIntError;
    fn from_str(s: &str) -> Result<Self, ParseBigIntError> {
        Ok(Int::big(BigInt::from_str(s)?).normalize())
    }
}

impl Hash for Uint {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &self.0 {
            Left(x) => x.hash(state),
            Right(b) => b.hash(state),
        }
    }
}

impl Hash for Int {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &self.0 {
            Left(x) => x.hash(state),
            Right(b) => b.hash(state),
        }
    }
}

impl Neg for Int {
    type Output = Int;
    fn neg(self) -> Int {
        Int::big(BigInt::from(self).neg()).normalize()
    }
}

impl Neg for &Int {
    type Output = Int;
    fn neg(self) -> Int {
        let self1 = self.cow_big();
        let self2: &BigInt = self1.borrow();
        Int::big(self2.neg()).normalize()
    }
}

impl Ord for Uint {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if let (Left(x), Left(y)) = (&self.0, &other.0) {
            x.cmp(y)
        } else {
            let self1 = self.cow_big();
            let self2: &BigUint = self1.borrow();
            let other1 = other.cow_big();
            let other2: &BigUint = other1.borrow();
            self2.borrow().cmp(other2.borrow())
        }
    }
}

impl PartialOrd<Uint> for Uint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if let (Left(x), Left(y)) = (&self.0, &other.0) {
            x.partial_cmp(y)
        } else {
            let self1 = self.cow_big();
            let self2: &BigUint = self1.borrow();
            let other1 = other.cow_big();
            let other2: &BigUint = other1.borrow();
            self2.borrow().partial_cmp(other2.borrow())
        }
    }
}

impl Ord for Int {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if let (Left(x), Left(y)) = (&self.0, &other.0) {
            x.cmp(y)
        } else {
            let self1 = self.cow_big();
            let self2: &BigInt = self1.borrow();
            let other1 = other.cow_big();
            let other2: &BigInt = other1.borrow();
            self2.borrow().cmp(other2.borrow())
        }
    }
}

impl PartialOrd<Int> for Int {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if let (Left(x), Left(y)) = (&self.0, &other.0) {
            x.partial_cmp(y)
        } else {
            let self1 = self.cow_big();
            let self2: &BigInt = self1.borrow();
            let other1 = other.cow_big();
            let other2: &BigInt = other1.borrow();
            self2.borrow().partial_cmp(other2.borrow())
        }
    }
}

// -- Basic stuff between both same and different signedness --

impl PartialOrd<Uint> for Int {
    fn partial_cmp(&self, other: &Uint) -> Option<std::cmp::Ordering> {
        self.partial_cmp(&Int::from(other.clone()))
    }
}

impl PartialOrd<Int> for Uint {
    fn partial_cmp(&self, other: &Int) -> Option<std::cmp::Ordering> {
        Int::from(self.clone()).partial_cmp(other)
    }
}

impl PartialEq<Uint> for Uint {
    fn eq(&self, other: &Self) -> bool {
        if let (Left(x), Left(y)) = (&self.0, &other.0) {
            x == y
        } else {
            let self1 = self.cow_big();
            let self2: &BigUint = self1.borrow();
            let other1 = other.cow_big();
            let other2: &BigUint = other1.borrow();
            self2.borrow().eq(other2.borrow())
        }
    }
}
impl PartialEq<Int> for Uint {
    /// Cannot use the small-int optimization, and copies the [`Uint`] into a [`BigInt`].
    fn eq(&self, other: &Int) -> bool {
        let self_bigint = BigInt::from(BigUint::from(self.clone()));
        let other1 = other.cow_big();
        let other2: &BigInt = other1.borrow();
        self_bigint.eq(other2.borrow())
    }
}
impl Eq for Uint {}

impl PartialEq<Int> for Int {
    fn eq(&self, other: &Self) -> bool {
        if let (Left(x), Left(y)) = (&self.0, &other.0) {
            x == y
        } else {
            let self1 = self.cow_big();
            let self2: &BigInt = self1.borrow();
            let other1 = other.cow_big();
            let other2: &BigInt = other1.borrow();
            self2.borrow().eq(other2.borrow())
        }
    }
}
impl PartialEq<Uint> for Int {
    /// Cannot use the small-int optimization, and copies the [`Uint`] into a [`BigInt`].
    fn eq(&self, other: &Uint) -> bool {
        let other_bigint = BigInt::from(BigUint::from(other.clone()));
        let self1 = self.cow_big();
        let self2: &BigInt = self1.borrow();
        other_bigint.eq(self2.borrow())
    }
}
impl Eq for Int {}

// -- Basic stuff between different signedness --

impl From<Uint> for Int {
    fn from(v: Uint) -> Self {
        match v.0 {
            Left(x) => {
                if let Ok(x1) = x.try_into() {
                    Int(Left(x1))
                } else {
                    Int(Right(Box::new(x.into())))
                }
            }
            Right(b) => Int(Right(Box::new((*b).into()))),
        }
    }
}

#[non_exhaustive]
pub struct IntIsNegativeError();

impl TryFrom<Int> for Uint {
    type Error = IntIsNegativeError;
    /// Fails on negative numbers.
    fn try_from(v: Int) -> Result<Self, Self::Error> {
        match v.0 {
            Left(x) => {
                if let Ok(x1) = x.try_into() {
                    Ok(Uint(Left(x1)))
                } else {
                    Ok(Uint(Right(Box::new(
                        x.to_biguint().ok_or(IntIsNegativeError())?,
                    ))))
                }
            }
            Right(x) => Ok(Uint(Right(Box::new(
                x.to_biguint().ok_or(IntIsNegativeError())?,
            )))),
        }
    }
}

// -- Conversions from/to primitives --

impl From<u128> for Uint {
    fn from(x: u128) -> Self {
        if let Ok(x) = x.try_into() {
            Uint(Left(x))
        } else {
            Uint(Right(Box::new(x.into())))
        }
    }
}
impl TryFrom<i128> for Uint {
    type Error = IntIsNegativeError;
    fn try_from(x: i128) -> Result<Self, Self::Error> {
        if let Ok(x) = x.try_into() {
            Ok(Uint(Left(x)))
        } else {
            Ok(Uint(Right(Box::new(
                BigInt::from(x).to_biguint().ok_or(IntIsNegativeError())?,
            ))))
        }
    }
}
impl From<u64> for Uint {
    fn from(x: u64) -> Self {
        if let Ok(x) = x.try_into() {
            Uint(Left(x))
        } else {
            Uint(Right(Box::new(x.into())))
        }
    }
}
impl TryFrom<i64> for Uint {
    type Error = IntIsNegativeError;
    fn try_from(x: i64) -> Result<Self, Self::Error> {
        if let Ok(x) = x.try_into() {
            Ok(Uint(Left(x)))
        } else {
            Ok(Uint(Right(Box::new(
                BigInt::from(x).to_biguint().ok_or(IntIsNegativeError())?,
            ))))
        }
    }
}
impl From<u32> for Uint {
    fn from(x: u32) -> Self {
        if let Ok(x) = x.try_into() {
            Uint(Left(x))
        } else {
            Uint(Right(Box::new(x.into())))
        }
    }
}
impl TryFrom<i32> for Uint {
    type Error = IntIsNegativeError;
    fn try_from(x: i32) -> Result<Self, Self::Error> {
        if let Ok(x) = x.try_into() {
            Ok(Uint(Left(x)))
        } else {
            Ok(Uint(Right(Box::new(
                BigInt::from(x).to_biguint().ok_or(IntIsNegativeError())?,
            ))))
        }
    }
}

impl From<u16> for Uint {
    fn from(x: u16) -> Self {
        if let Ok(x) = x.try_into() {
            Uint(Left(x))
        } else {
            Uint(Right(Box::new(x.into())))
        }
    }
}
impl TryFrom<i16> for Uint {
    type Error = IntIsNegativeError;
    fn try_from(x: i16) -> Result<Self, Self::Error> {
        if let Ok(x) = x.try_into() {
            Ok(Uint(Left(x)))
        } else {
            Ok(Uint(Right(Box::new(
                BigInt::from(x).to_biguint().ok_or(IntIsNegativeError())?,
            ))))
        }
    }
}

impl From<u8> for Uint {
    fn from(x: u8) -> Self {
        if let Ok(x) = x.try_into() {
            Uint(Left(x))
        } else {
            Uint(Right(Box::new(x.into())))
        }
    }
}
impl TryFrom<i8> for Uint {
    type Error = IntIsNegativeError;
    fn try_from(x: i8) -> Result<Self, Self::Error> {
        if let Ok(x) = x.try_into() {
            Ok(Uint(Left(x)))
        } else {
            Ok(Uint(Right(Box::new(
                BigInt::from(x).to_biguint().ok_or(IntIsNegativeError())?,
            ))))
        }
    }
}

impl From<usize> for Uint {
    fn from(x: usize) -> Self {
        if let Ok(x) = x.try_into() {
            Uint(Left(x))
        } else {
            Uint(Right(Box::new(x.into())))
        }
    }
}
impl TryFrom<isize> for Uint {
    type Error = IntIsNegativeError;
    fn try_from(x: isize) -> Result<Self, Self::Error> {
        if let Ok(x) = x.try_into() {
            Ok(Uint(Left(x)))
        } else {
            Ok(Uint(Right(Box::new(
                BigInt::from(x).to_biguint().ok_or(IntIsNegativeError())?,
            ))))
        }
    }
}

impl FromPrimitive for Uint {
    fn from_u128(x: u128) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Uint(Left(x)))
        } else {
            Some(Uint(Right(Box::new(x.into()))))
        }
    }
    fn from_i128(x: i128) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Uint(Left(x)))
        } else {
            Some(Uint(Right(Box::new(BigInt::from(x).to_biguint()?))))
        }
    }
    fn from_u64(x: u64) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Uint(Left(x)))
        } else {
            Some(Uint(Right(Box::new(x.into()))))
        }
    }
    fn from_i64(x: i64) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Uint(Left(x)))
        } else {
            Some(Uint(Right(Box::new(BigInt::from(x).to_biguint()?))))
        }
    }
    fn from_u32(x: u32) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Uint(Left(x)))
        } else {
            Some(Uint(Right(Box::new(x.into()))))
        }
    }
    fn from_i32(x: i32) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Uint(Left(x)))
        } else {
            Some(Uint(Right(Box::new(BigInt::from(x).to_biguint()?))))
        }
    }
}

impl From<u128> for Int {
    fn from(x: u128) -> Self {
        if let Ok(x) = x.try_into() {
            Int(Left(x))
        } else {
            Int(Right(Box::new(x.into())))
        }
    }
}
impl From<i128> for Int {
    fn from(x: i128) -> Self {
        if let Ok(x) = x.try_into() {
            Int(Left(x))
        } else {
            Int(Right(Box::new(x.into())))
        }
    }
}
impl From<u64> for Int {
    fn from(x: u64) -> Self {
        if let Ok(x) = x.try_into() {
            Int(Left(x))
        } else {
            Int(Right(Box::new(x.into())))
        }
    }
}
impl From<i64> for Int {
    fn from(x: i64) -> Self {
        if let Ok(x) = x.try_into() {
            Int(Left(x))
        } else {
            Int(Right(Box::new(x.into())))
        }
    }
}
impl From<u32> for Int {
    fn from(x: u32) -> Self {
        if let Ok(x) = x.try_into() {
            Int(Left(x))
        } else {
            Int(Right(Box::new(x.into())))
        }
    }
}
impl From<i32> for Int {
    fn from(x: i32) -> Self {
        if let Ok(x) = x.try_into() {
            Int(Left(x))
        } else {
            Int(Right(Box::new(x.into())))
        }
    }
}

impl From<u16> for Int {
    fn from(x: u16) -> Self {
        if let Ok(x) = x.try_into() {
            Int(Left(x))
        } else {
            Int(Right(Box::new(x.into())))
        }
    }
}
impl From<i16> for Int {
    fn from(x: i16) -> Self {
        if let Ok(x) = x.try_into() {
            Int(Left(x))
        } else {
            Int(Right(Box::new(x.into())))
        }
    }
}

impl From<u8> for Int {
    fn from(x: u8) -> Self {
        if let Ok(x) = x.try_into() {
            Int(Left(x))
        } else {
            Int(Right(Box::new(x.into())))
        }
    }
}
impl From<i8> for Int {
    fn from(x: i8) -> Self {
        if let Ok(x) = x.try_into() {
            Int(Left(x))
        } else {
            Int(Right(Box::new(x.into())))
        }
    }
}

impl From<usize> for Int {
    fn from(x: usize) -> Self {
        if let Ok(x) = x.try_into() {
            Int(Left(x))
        } else {
            Int(Right(Box::new(x.into())))
        }
    }
}
impl From<isize> for Int {
    fn from(x: isize) -> Self {
        if let Ok(x) = x.try_into() {
            Int(Left(x))
        } else {
            Int(Right(Box::new(x.into())))
        }
    }
}

impl FromPrimitive for Int {
    fn from_u128(x: u128) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Int(Left(x)))
        } else {
            Some(Int(Right(Box::new(x.into()))))
        }
    }
    fn from_i128(x: i128) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Int(Left(x)))
        } else {
            Some(Int(Right(Box::new(x.into()))))
        }
    }
    fn from_u64(x: u64) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Int(Left(x)))
        } else {
            Some(Int(Right(Box::new(x.into()))))
        }
    }
    fn from_i64(x: i64) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Int(Left(x)))
        } else {
            Some(Int(Right(Box::new(x.into()))))
        }
    }
    fn from_u32(x: u32) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Int(Left(x)))
        } else {
            Some(Int(Right(Box::new(x.into()))))
        }
    }
    fn from_i32(x: i32) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Int(Left(x)))
        } else {
            Some(Int(Right(Box::new(x.into()))))
        }
    }
}

impl ToPrimitive for Int {
    fn to_u128(&self) -> Option<u128> {
        match &self.0 {
            Left(x) => (*x).try_into().ok(),
            Right(b) => b.to_u128(),
        }
    }
    fn to_i128(&self) -> Option<i128> {
        match &self.0 {
            Left(x) => (*x).try_into().ok(),
            Right(b) => b.to_i128(),
        }
    }
    fn to_u64(&self) -> Option<u64> {
        match &self.0 {
            Left(x) => (*x).try_into().ok(),
            Right(b) => b.to_u64(),
        }
    }
    fn to_i64(&self) -> Option<i64> {
        match &self.0 {
            Left(x) => (*x).try_into().ok(),
            Right(b) => b.to_i64(),
        }
    }
    fn to_u32(&self) -> Option<u32> {
        match &self.0 {
            Left(x) => (*x).try_into().ok(),
            Right(b) => b.to_u32(),
        }
    }
    fn to_i32(&self) -> Option<i32> {
        match &self.0 {
            Left(x) => (*x).try_into().ok(),
            Right(b) => b.to_i32(),
        }
    }
}

impl ToPrimitive for Uint {
    fn to_u128(&self) -> Option<u128> {
        match &self.0 {
            Left(x) => (*x).try_into().ok(),
            Right(b) => b.to_u128(),
        }
    }
    fn to_i128(&self) -> Option<i128> {
        match &self.0 {
            Left(x) => (*x).try_into().ok(),
            Right(b) => b.to_i128(),
        }
    }
    fn to_u64(&self) -> Option<u64> {
        match &self.0 {
            Left(x) => (*x).try_into().ok(),
            Right(b) => b.to_u64(),
        }
    }
    fn to_i64(&self) -> Option<i64> {
        match &self.0 {
            Left(x) => (*x).try_into().ok(),
            Right(b) => b.to_i64(),
        }
    }
    fn to_u32(&self) -> Option<u32> {
        match &self.0 {
            Left(x) => (*x).try_into().ok(),
            Right(b) => b.to_u32(),
        }
    }
    fn to_i32(&self) -> Option<i32> {
        match &self.0 {
            Left(x) => (*x).try_into().ok(),
            Right(b) => b.to_i32(),
        }
    }
}

macro_rules! call_with_all_signed_base_types {
    ($macroname:ident, $($token:tt)*) => {
        $macroname!{$($token)* i8}
        $macroname!{$($token)* i16}
        $macroname!{$($token)* i32}
        $macroname!{$($token)* i64}
        $macroname!{$($token)* i128}
        $macroname!{$($token)* isize}
    };
}

macro_rules! call_with_all_unsigned_base_types {
    ($macroname:ident, $($token:tt)*) => {
        $macroname!{$($token)* u8}
        $macroname!{$($token)* u16}
        $macroname!{$($token)* u32}
        $macroname!{$($token)* u64}
        $macroname!{$($token)* u128}
        $macroname!{$($token)* usize}
    };
}

macro_rules! call_with_ref_permutations {
    ($macroname_value:ident, $macroname_mut:ident, $type:tt, $basetype:tt, $bigtype:tt, signed) => {
        call_with_ref_permutations!{$macroname_value, $macroname_mut, $type, $basetype, $bigtype, self case}
        call_with_all_signed_base_types!{
            call_with_ref_permutations,
            $macroname_value, $macroname_mut, $type, $basetype, $bigtype, base type
        }
        call_with_all_unsigned_base_types!{
            call_with_ref_permutations,
            $macroname_value, $macroname_mut, $type, $basetype, $bigtype, base type
        }
    };
    ($macroname_value:ident, $macroname_mut:ident, $type:tt, $basetype:tt, $bigtype:tt, unsigned) => {
        call_with_ref_permutations!{$macroname_value, $macroname_mut, $type, $basetype, $bigtype, self case}
        call_with_all_unsigned_base_types!{
            call_with_ref_permutations,
            $macroname_value, $macroname_mut, $type, $basetype, $bigtype, base type
        }
    };
    ($macroname_value:ident, $macroname_mut:ident, $type:tt, $basetype:tt, $bigtype:tt) => {
        call_with_ref_permutations!{$macroname_value, $macroname_mut, $type, $basetype, $bigtype, self case}
    };
    ($macroname_value:ident, $macroname_mut:ident, $type:tt, $basetype:tt, $bigtype:tt, self case) => {
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, $type, $type, &v.0, {},
            $bigtype::from(self), $bigtype::from(v)
        }
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, $type, &$type, &v.0, {
                let v1 = v.cow_big()
                let v2: &$bigtype = v1.borrow()
            }, $bigtype::from(self), v2
        }
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, &$type, $type, &v.0, {
                let self1 = self.cow_big()
                let self2: &$bigtype = self1.borrow()
            }, self2, $bigtype::from(v)
        }
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, &$type, &$type, &v.0, {
                let self1 = self.cow_big()
                let self2: &$bigtype = self1.borrow()
                let v1 = v.cow_big()
                let v2: &$bigtype = v1.borrow()
            }, self2, v2
        }
        $macroname_mut!{$type, $type}
        $macroname_mut!{$type, &$type}
    };
    ($macroname_value:ident, $macroname_mut:ident, $type:tt, $basetype:ty, $bigtype:tt, base type $baseothertype:ty) => {
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, $type, $baseothertype, Either::<&$baseothertype, $type>::Left(&v), {},
            $bigtype::from(self), v
        }
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, $type, &$baseothertype, Either::<&$baseothertype, $type>::Left(v), {},
            $bigtype::from(self), *v
        }
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, &$type, $baseothertype, Either::<&$baseothertype, $type>::Left(&v), {
                let self1 = self.cow_big()
                let self2: &$bigtype = self1.borrow()
            }, self2, v
        }
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, &$type, &$baseothertype, Either::<&$baseothertype, $type>::Left(v), {
                let self1 = self.cow_big()
                let self2: &$bigtype = self1.borrow()
            }, self2, *v
        }
        $macroname_mut!{$type, $baseothertype}
        $macroname_mut!{$type, &$baseothertype}
    };
}

macro_rules! trait_add_value {
    ($type:tt, $basetype:ty, $bigtype:ty, $selfvar:tt, $othvar:ident,
        $selftype:ty, $othtype:ty, $otheitherref:expr,
        {$($makecows:stmt)*}, $bigexpr1:expr, $bigexpr2:expr) => {
            impl Add<$othtype> for $selftype {
                type Output = $type;
                fn add($selfvar, $othvar: $othtype) -> $type {
                    if let (Left(x), Left(y)) = (&$selfvar.0, $otheitherref) {
                        if let Ok(y_base) = <$basetype>::try_from(*y) {
                            if let Some(z) = x.checked_add(y_base) {
                                return $type::small(z);
                            }
                        }
                    }
                    $($makecows)*
                    $type::big($bigexpr1.add($bigexpr2))
                }
            }
    };
}

macro_rules! trait_add_mut {
    ($type:tt, $othtype:ty) => {
        impl AddAssign<$othtype> for $type {
            fn add_assign(&mut self, other: $othtype) {
                self.transform(|sf| sf.add(other));
            }
        }
    };
}

call_with_ref_permutations! {trait_add_value, trait_add_mut, Int, int, BigInt, signed}
call_with_ref_permutations! {trait_add_value, trait_add_mut, Uint, uint, BigUint, unsigned}

macro_rules! trait_div_value {
    ($type:tt, $basetype:ty, $bigtype:ty, $selfvar:tt, $othvar:ident,
        $selftype:ty, $othtype:ty, $otheitherref:expr,
        {$($makecows:stmt)*}, $bigexpr1:expr, $bigexpr2:expr) => {
        impl Div<$othtype> for $selftype {
            type Output = $type;
            fn div($selfvar, $othvar: $othtype) -> $type {
                if let (Left(x), Left(y)) = (&$selfvar.0, $otheitherref) {
                    if let Ok(y_base) = <$basetype>::try_from(*y) {
                        if let Some(z) = x.checked_div(y_base) {
                            return $type::small(z);
                        }
                    }
                }
                $($makecows)*
                $type::big($bigexpr1.div($bigexpr2))
            }
        }
    };
}

macro_rules! trait_div_mut {
    ($type:tt, $othtype:ty) => {
        impl DivAssign<$othtype> for $type {
            fn div_assign(&mut self, other: $othtype) {
                self.transform(|sf| sf.div(other));
            }
        }
    };
}

call_with_ref_permutations! {trait_div_value, trait_div_mut, Int, int, BigInt, signed}
call_with_ref_permutations! {trait_div_value, trait_div_mut, Uint, uint, BigUint, unsigned}

macro_rules! trait_mul_value {
    ($type:tt, $basetype:ty, $bigtype:ty, $selfvar:tt, $othvar:ident,
        $selftype:ty, $othtype:ty, $otheitherref:expr,
        {$($makecows:stmt)*}, $bigexpr1:expr, $bigexpr2:expr) => {
        impl Mul<$othtype> for $selftype {
            type Output = $type;
            fn mul($selfvar, $othvar: $othtype) -> $type {
                if let (Left(x), Left(y)) = (&$selfvar.0, $otheitherref) {
                    if let Ok(y_base) = <$basetype>::try_from(*y) {
                        if let Some(z) = x.checked_mul(y_base) {
                            return $type::small(z);
                        }
                    }
                }
                $($makecows)*
                $type::big($bigexpr1.mul($bigexpr2))
            }
        }
    };
}

macro_rules! trait_mul_mut {
    ($type:tt, $othtype:ty) => {
        impl MulAssign<$othtype> for $type {
            fn mul_assign(&mut self, other: $othtype) {
                self.transform(|sf| sf.mul(other));
            }
        }
    };
}

call_with_ref_permutations! {trait_mul_value, trait_mul_mut, Int, int, BigInt, signed}
call_with_ref_permutations! {trait_mul_value, trait_mul_mut, Uint, uint, BigUint, unsigned}

macro_rules! trait_rem_value {
    ($type:tt, $basetype:ty, $bigtype:ty, $selfvar:tt, $othvar:ident,
        $selftype:ty, $othtype:ty, $otheitherref:expr,
        {$($makecows:stmt)*}, $bigexpr1:expr, $bigexpr2:expr) => {
        impl Rem<$othtype> for $selftype {
            type Output = $type;
            fn rem($selfvar, $othvar: $othtype) -> $type {
                if let (Left(x), Left(y)) = (&$selfvar.0, $otheitherref) {
                    if let Ok(y_base) = <$basetype>::try_from(*y) {
                        if let Some(z) = x.checked_rem(y_base) {
                            return $type::small(z);
                        }
                    }
                }
                $($makecows)*
                $type::big($bigexpr1.rem($bigexpr2))
            }
        }
    };
}

macro_rules! trait_rem_mut {
    ($type:tt, $othtype:ty) => {
        impl RemAssign<$othtype> for $type {
            fn rem_assign(&mut self, other: $othtype) {
                self.transform(|sf| sf.rem(other));
            }
        }
    };
}

call_with_ref_permutations! {trait_rem_value, trait_rem_mut, Int, int, BigInt, signed}
call_with_ref_permutations! {trait_rem_value, trait_rem_mut, Uint, uint, BigUint, unsigned}

macro_rules! trait_sub_value {
    ($type:tt, $basetype:ty, $bigtype:ty, $selfvar:tt, $othvar:ident,
        $selftype:ty, $othtype:ty, $otheitherref:expr,
        {$($makecows:stmt)*}, $bigexpr1:expr, $bigexpr2:expr) => {
        impl Sub<$othtype> for $selftype {
            type Output = $type;
            fn sub($selfvar, $othvar: $othtype) -> $type {
                if let (Left(x), Left(y)) = (&$selfvar.0, $otheitherref) {
                    if let Ok(y_base) = <$basetype>::try_from(*y) {
                        if let Some(z) = x.checked_sub(y_base) {
                            return $type::small(z);
                        }
                    }
                }
                $($makecows)*
                $type::big($bigexpr1.sub($bigexpr2))
            }
        }
    };
}

macro_rules! trait_sub_mut {
    ($type:tt, $othtype:ty) => {
        impl SubAssign<$othtype> for $type {
            fn sub_assign(&mut self, other: $othtype) {
                self.transform(|sf| sf.sub(other));
            }
        }
    };
}

call_with_ref_permutations! {trait_sub_value, trait_sub_mut, Int, int, BigInt, signed}
call_with_ref_permutations! {trait_sub_value, trait_sub_mut, Uint, uint, BigUint, unsigned}

macro_rules! trait_partialeq {
    ($type:tt $basetype:ty) => {
        // One way
        impl PartialEq<$basetype> for $type {
            fn eq(&self, other: &$basetype) -> bool {
                ToGeneric::<$basetype>::to_generic(self).map_or(false, |x| x.eq(other))
            }
        }

        // The other way
        impl PartialEq<$type> for $basetype {
            fn eq(&self, other: &$type) -> bool {
                ToGeneric::<$basetype>::to_generic(other).map_or(false, |x| x.eq(self))
            }
        }
    };
}

call_with_all_unsigned_base_types!(trait_partialeq, Uint);
call_with_all_unsigned_base_types!(trait_partialeq, Int);
call_with_all_signed_base_types!(trait_partialeq, Uint);
call_with_all_signed_base_types!(trait_partialeq, Int);

macro_rules! trait_partialord_straight {
    ($type:tt $basetype:tt) => {
        // One way
        impl PartialOrd<$basetype> for $type {
            fn partial_cmp(&self, other: &$basetype) -> Option<Ordering> {
                // First, try to do it on the base type
                match ToGeneric::<$basetype>::to_generic(self) {
                    Some(x) => x.partial_cmp(other),
                    None => {
                        // If that fails, then do it on our type.
                        match $type::try_from(other.clone()) {
                            Ok(other2) => self.partial_cmp(&other2),
                            Err(_) => {
                                // Size is never an issue for TryFrom. This can only
                                // happen because we're trying to convert a negative
                                // number to unsigned.
                                Some(Ordering::Greater)
                            }
                        }
                    }
                }
            }
        }

        // The other way
        impl PartialOrd<$type> for $basetype {
            fn partial_cmp(&self, other: &$type) -> Option<Ordering> {
                other.partial_cmp(self).map(|ord| ord.reverse())
            }
        }
    };
}

call_with_all_unsigned_base_types!(trait_partialord_straight, Uint);
call_with_all_unsigned_base_types!(trait_partialord_straight, Int);
call_with_all_signed_base_types!(trait_partialord_straight, Uint);
call_with_all_signed_base_types!(trait_partialord_straight, Int);

#[cfg(test)]
mod test {
    #![allow(clippy::redundant_clone)]
    use super::*;
    #[test]
    fn test_unsigned() {
        let eleven = Uint::small(11);
        assert_eq!(eleven, 11u8);
        assert_ne!(eleven, 10u8);
        assert_eq!(11u8, eleven);
        assert_ne!(10u8, eleven);
        assert_eq!(eleven, 11i8);
        assert_ne!(eleven, 10i8);
        assert_eq!(11i8, eleven);
        assert_ne!(10i8, eleven);
        assert!(eleven.0.is_left());
        assert!(eleven.clone().0.is_left());
        assert!(eleven.clone().normalize().0.is_left());

        let eleven_to_the_eleven = &eleven
            * &eleven
            * &eleven
            * &eleven
            * &eleven
            * &eleven
            * &eleven
            * &eleven
            * &eleven
            * &eleven
            * &eleven;
        assert!(eleven_to_the_eleven.0.is_right());
        assert!(eleven_to_the_eleven.clone().0.is_right());
        assert!(eleven_to_the_eleven.clone().normalize().0.is_right());
        assert!(eleven < eleven_to_the_eleven);
        assert!(11u8 < eleven_to_the_eleven);
        assert!(11i8 < eleven_to_the_eleven);
    }
    #[test]
    fn test_signed() {
        let eleven = Int::small(11);
        assert_eq!(eleven, 11u8);
        assert_ne!(eleven, 10u8);
        assert_eq!(11u8, eleven);
        assert_ne!(10u8, eleven);
        assert_eq!(eleven, 11i8);
        assert_ne!(eleven, 10i8);
        assert_eq!(11i8, eleven);
        assert_ne!(10i8, eleven);
        assert!(eleven.0.is_left());
        assert!(eleven.clone().0.is_left());
        assert!(eleven.clone().normalize().0.is_left());

        let eleven_to_the_eleven = &eleven
            * &eleven
            * &eleven
            * &eleven
            * &eleven
            * &eleven
            * &eleven
            * &eleven
            * &eleven
            * &eleven
            * &eleven;
        assert!(eleven_to_the_eleven.0.is_right());
        assert!(eleven_to_the_eleven.clone().0.is_right());
        assert!(eleven_to_the_eleven.clone().normalize().0.is_right());
        assert!(eleven < eleven_to_the_eleven);
        assert!(-eleven.clone() < eleven_to_the_eleven);
        assert!(-eleven_to_the_eleven.clone() < eleven);
        assert!(-eleven_to_the_eleven.clone() < -eleven.clone());
        assert!(11u8 < eleven_to_the_eleven);
        assert!(11i8 < eleven_to_the_eleven);
        assert!(-11i8 < eleven_to_the_eleven);
        assert!(-eleven_to_the_eleven.clone() < 11i8);
        assert!(-eleven_to_the_eleven.clone() < -11i8);
    }
}
