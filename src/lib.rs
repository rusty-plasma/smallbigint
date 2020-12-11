//! Two types, [`Uint`] and [`Int`], like `smallvec` for big integers.
//! Anything that fits in 32 bits stays on the stack. Numbers that
//! don't fit are stored in a `Box<num_bigint::BigUint>` / `Box<num_bigint::BigInt>`.
//!
//! On 64-bit architectures, by default we use `unsafe` to compress
//! the types to 8 bytes, exploiting pointer alignment. This behavior
//! is triggered by the `unsafe-opt` feature, which is enabled by default.
//!
//! ## Implemented traits
//!
//! Most important numeric traits have been implemented. Here are some that aren't yet;
//! pull requests are welcome!
//!
//! - [`std::fmt::{Binary, LowerHex, Octal, UpperHex}`]
//! - Bit operations
//! - [`num_traits::Num`], [`num_traits::Signed`], [`num_traits::Unsigned`],
//!   [`num_integer::Integer`], [`num_integer::Roots`], [`std::iter::Product`],
//!   [`std::iter::Sum`], [`num_traits::pow::Pow`]
//! - Other methods implemented directly on [`BigInt`], [`BigUint`]
//! - Implement `num_bigint::{ToBigInt, ToBigUint}`
//!
//!
//! There aren't super many unit tests currently, but the code is sufficiently
//! simple that there is not much space where bugs could hide.

// Some useless conversions make the code look more uniform.
#![allow(clippy::useless_conversion)]

use cfg_if::cfg_if;
use either::{Either, Left, Right};
use num_bigint::{BigInt, BigUint, ParseBigIntError, ToBigInt, ToBigUint};
use num_traits::cast::{FromPrimitive, ToPrimitive};
use num_traits::identities::{One, Zero};
#[allow(unused_imports)]
use num_traits::{
    CheckedAdd, CheckedDiv, CheckedMul, CheckedNeg, CheckedRem, CheckedShl, CheckedShr, CheckedSub,
};
use std::borrow::Cow::{self, Borrowed, Owned};
use std::cmp::Ordering;
use std::convert::{From, Into, TryFrom, TryInto};
use std::fmt::{Debug, Display};
use std::hash::{Hash, Hasher};
use std::ops::{
    Add, AddAssign, Deref, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};

use std::str::FromStr;

mod to_primitive_generic;
// Don't want to commit to exporting this yet
use to_primitive_generic::ToGeneric;

#[allow(non_camel_case_types)]
type uint = u32;
#[allow(non_camel_case_types)]
type int = i32;

cfg_if! {
    if #[cfg(any(not(feature = "unsafe-opt"), not(target_pointer_width = "64")))] {
        // The real contents of the Uint and Int types. If we are using the
        // unsafe optimization, then we use a different type that's equivalent
        // to these Eithers.

        #[derive(Clone)]
        pub struct UintInner(Either<uint, Box<BigUint>>);
        #[derive(Clone)]
        pub struct IntInner(Either<int, Box<BigInt>>);

        impl UintInner {
            const fn make_left(i: u32) -> Self {
                UintInner(Left(i))
            }
            fn make(v: Either<u32, Box<BigUint>>) -> Self {
                UintInner(v)
            }
            fn get(self) -> Either<u32, Box<BigUint>> {
                self.0
            }
            fn get_ref(&self) -> Either<u32, &BigUint> {
                match self.0 {
                    Left(v) => Left(v),
                    Right(ref b) => Right(&*b),
                }
            }
        }

        impl IntInner {
            const fn make_left(i: i32) -> Self {
                IntInner(Left(i))
            }
            fn make(v: Either<i32, Box<BigInt>>) -> Self {
                IntInner(v)
            }
            fn get(self) -> Either<i32, Box<BigInt>> {
                self.0
            }
            fn get_ref(&self) -> Either<i32, &BigInt> {
                match self.0 {
                    Left(v) => Left(v),
                    Right(ref b) => Right(&*b),
                }
            }
        }
    } else {
        mod unsafeu32orbox;

        type UintInner = unsafeu32orbox::UnsafeU32OrBox<BigUint>;
        type IntInner = unsafeu32orbox::UnsafeI32OrBox<BigInt>;
    }
}

#[derive(Clone)]
pub struct Uint(UintInner);
#[derive(Clone)]
pub struct Int(IntInner);

impl Uint {
    const fn make_left(i: u32) -> Self {
        Uint(UintInner::make_left(i))
    }
    fn mk(v: Either<u32, Box<BigUint>>) -> Self {
        Uint(UintInner::make(v))
    }
    fn get(self) -> Either<u32, Box<BigUint>> {
        self.0.get()
    }
    fn get_ref(&self) -> Either<u32, &BigUint> {
        self.0.get_ref()
    }

    pub const fn zero() -> Self {
        Self::small(0)
    }
    pub const fn small(x: uint) -> Self {
        Uint::make_left(x)
    }
    pub fn big(v: BigUint) -> Self {
        Uint::mk(Right(Box::new(v)))
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
    /// # use std::ops::Deref;
    /// # let x = Uint::small(42);
    /// let x1 = x.cow_big();
    /// let x2 : &BigUint = x1.deref();
    /// ```
    ///
    /// We have to
    ///
    /// - Put `x1` in a variable, so that the compiler can figure out the lifetimes
    /// - Put `x2` in a variable, otherwise the Rust compiler can't figure out its type.
    pub fn cow_big(&self) -> Cow<BigUint> {
        match self.get_ref() {
            Left(x) => Owned(x.into()),
            Right(ref b) => Borrowed(b),
        }
    }
    /// If we're storing a [`BigUint`] but it would fit in a small uint instead, then
    /// convert, and discard the heap-allocated memory.
    pub fn normalize(self) -> Self {
        match self.get() {
            Left(x) => Self::mk(Left(x)),
            Right(b) => {
                if let Some(x) = b.to_u32() {
                    Self::mk(Left(x)) // drop the memory
                } else {
                    Self::mk(Right(b))
                }
            }
        }
    }
    /// Like `normalize`, but borrows instead.
    #[allow(clippy::needless_return)]
    pub fn normalize_ref(&self) -> Cow<Self> {
        if let Right(ref b) = self.0.get_ref() {
            if let Some(x) = b.to_u32() {
                return Owned(Self::mk(Left(x)));
            }
        }
        return Borrowed(self);
    }
    #[allow(dead_code)]
    fn is_stored_as_big(&self) -> bool {
        matches!(self.0.get_ref(), Right(_))
    }
}

impl Int {
    const fn make_left(i: i32) -> Self {
        Int(IntInner::make_left(i))
    }
    fn mk(v: Either<i32, Box<BigInt>>) -> Self {
        Int(IntInner::make(v))
    }
    fn get(self) -> Either<i32, Box<BigInt>> {
        self.0.get()
    }
    fn get_ref(&self) -> Either<i32, &BigInt> {
        self.0.get_ref()
    }

    pub const fn zero() -> Self {
        Self::small(0)
    }
    pub const fn small(x: int) -> Self {
        Int::make_left(x)
    }
    pub fn big(v: BigInt) -> Self {
        Int::mk(Right(Box::new(v)))
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
    /// # use std::ops::Deref;
    /// # let x = Int::small(42);
    /// let x1 = x.cow_big();
    /// let x2 : &BigInt = x1.deref();
    /// ```
    ///
    /// We have to
    ///
    /// - Put `x1` in a variable, so that the compiler can figure out the lifetimes
    /// - Put `x2` in a variable, otherwise the Rust compiler can't figure out its type.
    pub fn cow_big(&self) -> Cow<BigInt> {
        match self.get_ref() {
            Left(x) => Owned(x.into()),
            Right(ref b) => Borrowed(b),
        }
    }
    /// If we're storing a [`BigInt`] but it would fit in a small int instead, then
    /// convert, and discard the heap-allocated memory.
    pub fn normalize(self) -> Self {
        match self.get() {
            Left(x) => Self::mk(Left(x)),
            Right(b) => {
                if let Some(x) = b.to_i32() {
                    Self::mk(Left(x)) // drop the memory
                } else {
                    Self::mk(Right(b))
                }
            }
        }
    }
    /// Like `normalize`, but borrows instead.
    #[allow(clippy::needless_return)]
    pub fn normalize_ref(&self) -> Cow<Self> {
        if let Right(ref b) = self.0.get_ref() {
            if let Some(x) = b.to_i32() {
                return Owned(Self::mk(Left(x)));
            }
        }
        return Borrowed(self);
    }
    #[allow(dead_code)]
    fn is_stored_as_big(&self) -> bool {
        matches!(self.0.get_ref(), Right(_))
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

impl Zero for Uint {
    fn zero() -> Self {
        Self::small(0)
    }
    fn is_zero(&self) -> bool {
        *self == Self::zero()
    }
}
impl Zero for Int {
    fn zero() -> Self {
        Self::small(0)
    }
    fn is_zero(&self) -> bool {
        *self == Self::zero()
    }
}

impl One for Uint {
    fn one() -> Self {
        Self::small(1)
    }
    fn is_one(&self) -> bool {
        *self == Self::one()
    }
}
impl One for Int {
    fn one() -> Self {
        Self::small(1)
    }
    fn is_one(&self) -> bool {
        *self == Self::one()
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
        match self.0.get_ref() {
            Left(x) => Display::fmt(&x, f),
            Right(b) => Display::fmt(b, f),
        }
    }
}

impl Display for Int {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.0.get_ref() {
            Left(x) => Display::fmt(&x, f),
            Right(b) => Display::fmt(b, f),
        }
    }
}

impl Debug for Uint {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

impl Debug for Int {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

impl From<BigUint> for Uint {
    fn from(v: BigUint) -> Self {
        Uint::mk(Right(Box::new(v)))
    }
}
impl From<Uint> for BigUint {
    fn from(v: Uint) -> BigUint {
        match v.0.get() {
            Left(x) => x.into(),
            Right(b) => *b,
        }
    }
}

impl From<BigInt> for Int {
    fn from(v: BigInt) -> Self {
        Int::mk(Right(Box::new(v)))
    }
}
impl From<Int> for BigInt {
    fn from(v: Int) -> BigInt {
        match v.0.get() {
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
        match self.normalize_ref().get_ref() {
            Left(x) => x.hash(state),
            Right(b) => b.hash(state),
        }
    }
}

impl Hash for Int {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self.normalize_ref().get_ref() {
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
        let self2: &BigInt = self1.deref();
        Int::big(self2.neg()).normalize()
    }
}

// -- Basic stuff between both same and different signedness --

impl Ord for Uint {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if let (Left(x), Left(y)) = (self.get_ref(), other.get_ref()) {
            x.cmp(&y)
        } else {
            let self1 = self.cow_big();
            let self2: &BigUint = self1.deref();
            let other1 = other.cow_big();
            let other2: &BigUint = other1.deref();
            self2.cmp(other2.deref())
        }
    }
}

impl PartialOrd<Uint> for Uint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if let (Left(x), Left(y)) = (self.get_ref(), other.get_ref()) {
            x.partial_cmp(&y)
        } else {
            let self1 = self.cow_big();
            let self2: &BigUint = self1.deref();
            let other1 = other.cow_big();
            let other2: &BigUint = other1.deref();
            self2.partial_cmp(other2.deref())
        }
    }
}

impl Ord for Int {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if let (Left(x), Left(y)) = (self.get_ref(), other.get_ref()) {
            x.cmp(&y)
        } else {
            let self1 = self.cow_big();
            let self2: &BigInt = self1.deref();
            let other1 = other.cow_big();
            let other2: &BigInt = other1.deref();
            self2.cmp(other2.deref())
        }
    }
}

impl PartialOrd<Int> for Int {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if let (Left(x), Left(y)) = (self.get_ref(), other.get_ref()) {
            x.partial_cmp(&y)
        } else {
            let self1 = self.cow_big();
            let self2: &BigInt = self1.deref();
            let other1 = other.cow_big();
            let other2: &BigInt = other1.deref();
            self2.partial_cmp(other2.deref())
        }
    }
}

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
        if let (Left(x), Left(y)) = (self.get_ref(), other.get_ref()) {
            x == y
        } else {
            let self1 = self.cow_big();
            let self2: &BigUint = self1.deref();
            let other1 = other.cow_big();
            let other2: &BigUint = other1.deref();
            self2.eq(other2.deref())
        }
    }
}
impl PartialEq<Int> for Uint {
    /// Cannot use the small-int optimization, and copies the [`Uint`] into a [`BigInt`].
    fn eq(&self, other: &Int) -> bool {
        let self_bigint = BigInt::from(BigUint::from(self.clone()));
        let other1 = other.cow_big();
        let other2: &BigInt = other1.deref();
        self_bigint.eq(other2.deref())
    }
}
impl Eq for Uint {}

impl PartialEq<Int> for Int {
    fn eq(&self, other: &Self) -> bool {
        if let (Left(x), Left(y)) = (self.get_ref(), other.get_ref()) {
            x == y
        } else {
            let self1 = self.cow_big();
            let self2: &BigInt = self1.deref();
            let other1 = other.cow_big();
            let other2: &BigInt = other1.deref();
            self2.eq(other2.deref())
        }
    }
}
impl PartialEq<Uint> for Int {
    /// Cannot use the small-int optimization, and copies the [`Uint`] into a [`BigInt`].
    fn eq(&self, other: &Uint) -> bool {
        let other_bigint = BigInt::from(BigUint::from(other.clone()));
        let self1 = self.cow_big();
        let self2: &BigInt = self1.deref();
        other_bigint.eq(self2.deref())
    }
}
impl Eq for Int {}

macro_rules! impl_ref_variants {
    // Here we implement stuff like
    //
    //   - PartialEq<&i16> for Int
    //   - PartialEq<i16> for &Int
    //
    // so that you don't have to call the * operator yourself as much. But we
    // don't implement PartialEq<&i16> for &Int because the generic implementation
    // already takes care of that.
    //
    // These functions are very simple (a dereference and a function call), so it
    // seems reasonable to suggest that they should be inlined.
    ($trait:tt, $method:tt, $selftype:ty, $othtype:ty, $resulttype:ty) => {
        impl $trait<&$othtype> for $selftype {
            #[inline]
            fn $method(&self, other: &&$othtype) -> $resulttype {
                self.$method(*other)
            }
        }
        impl $trait<$othtype> for &$selftype {
            #[inline]
            fn $method(&self, other: &$othtype) -> $resulttype {
                (*self).$method(other)
            }
        }
    };
}

impl_ref_variants! { PartialEq, eq, Uint, Uint, bool }
impl_ref_variants! { PartialEq, eq, Int, Uint, bool }
impl_ref_variants! { PartialEq, eq, Uint, Int, bool }
impl_ref_variants! { PartialEq, eq, Int, Int, bool }
impl_ref_variants! { PartialOrd, partial_cmp, Uint, Uint, Option<Ordering> }
impl_ref_variants! { PartialOrd, partial_cmp, Int, Uint, Option<Ordering> }
impl_ref_variants! { PartialOrd, partial_cmp, Uint, Int, Option<Ordering> }
impl_ref_variants! { PartialOrd, partial_cmp, Int, Int, Option<Ordering> }

// -- Basic stuff between different signedness --

impl Uint {
    /// Convert owned to [`Int`].
    pub fn into_int(self) -> Int {
        match self.get() {
            Left(x) => {
                if let Ok(x1) = x.try_into() {
                    Int::mk(Left(x1))
                } else {
                    Int::mk(Right(Box::new(x.into())))
                }
            }
            Right(b) => Int::mk(Right(Box::new((*b).into()))),
        }
    }
    /// Convert reference to [`Int`].
    pub fn to_int(&self) -> Int {
        match self.0.get_ref() {
            Left(x) => {
                if let Ok(x1) = x.try_into() {
                    Int::mk(Left(x1))
                } else {
                    Int::mk(Right(Box::new(x.into())))
                }
            }
            Right(b) => Int::mk(Right(Box::new(
                b.to_bigint()
                    .expect("ToBigInt on BigUint should always succeed"),
            ))),
        }
    }
}
/// An alias for `.into_uint()`.
impl From<Uint> for Int {
    fn from(v: Uint) -> Self {
        v.into_int()
    }
}

impl Int {
    /// Convert owned to [`Uint`] if nonnegative, otherwise None.
    ///
    /// As there is not yet such a method on [`BigUint`], for now this clones
    /// the underlying storage.
    /// <https://github.com/rust-num/num-bigint/issues/120>
    pub fn into_uint(self) -> Option<Uint> {
        match self.get() {
            Left(x) => {
                if let Ok(x1) = x.try_into() {
                    Some(Uint::mk(Left(x1)))
                } else {
                    Some(Uint::mk(Right(Box::new(x.to_biguint()?))))
                }
            }
            Right(x) => Some(Uint::mk(Right(Box::new(x.to_biguint()?)))),
        }
    }
    /// Convert reference to [`Uint`] if nonnegative, otherwise None.
    pub fn to_uint(&self) -> Option<Uint> {
        match self.0.get_ref() {
            Left(x) => {
                if let Ok(x1) = x.try_into() {
                    Some(Uint::mk(Left(x1)))
                } else {
                    Some(Uint::mk(Right(Box::new(x.to_biguint()?))))
                }
            }
            Right(x) => Some(Uint::mk(Right(Box::new(x.to_biguint()?)))),
        }
    }
}
#[non_exhaustive]
#[derive(Debug)]
pub struct IntIsNegativeError();

/// An alias for `.into_int()`.
impl TryFrom<Int> for Uint {
    type Error = IntIsNegativeError;
    /// Fails on negative numbers.
    fn try_from(v: Int) -> Result<Self, Self::Error> {
        v.into_uint().ok_or(IntIsNegativeError())
    }
}

// -- Conversions from/to primitives --

impl From<u128> for Uint {
    fn from(x: u128) -> Self {
        if let Ok(x) = x.try_into() {
            Uint::mk(Left(x))
        } else {
            Uint::mk(Right(Box::new(x.into())))
        }
    }
}
impl TryFrom<i128> for Uint {
    type Error = IntIsNegativeError;
    fn try_from(x: i128) -> Result<Self, Self::Error> {
        if let Ok(x) = x.try_into() {
            Ok(Uint::mk(Left(x)))
        } else {
            Ok(Uint::mk(Right(Box::new(
                BigInt::from(x).to_biguint().ok_or(IntIsNegativeError())?,
            ))))
        }
    }
}
impl From<u64> for Uint {
    fn from(x: u64) -> Self {
        if let Ok(x) = x.try_into() {
            Uint::mk(Left(x))
        } else {
            Uint::mk(Right(Box::new(x.into())))
        }
    }
}
impl TryFrom<i64> for Uint {
    type Error = IntIsNegativeError;
    fn try_from(x: i64) -> Result<Self, Self::Error> {
        if let Ok(x) = x.try_into() {
            Ok(Uint::mk(Left(x)))
        } else {
            Ok(Uint::mk(Right(Box::new(
                BigInt::from(x).to_biguint().ok_or(IntIsNegativeError())?,
            ))))
        }
    }
}
impl From<u32> for Uint {
    fn from(x: u32) -> Self {
        if let Ok(x) = x.try_into() {
            Uint::mk(Left(x))
        } else {
            Uint::mk(Right(Box::new(x.into())))
        }
    }
}
impl TryFrom<i32> for Uint {
    type Error = IntIsNegativeError;
    fn try_from(x: i32) -> Result<Self, Self::Error> {
        if let Ok(x) = x.try_into() {
            Ok(Uint::mk(Left(x)))
        } else {
            Ok(Uint::mk(Right(Box::new(
                BigInt::from(x).to_biguint().ok_or(IntIsNegativeError())?,
            ))))
        }
    }
}

impl From<u16> for Uint {
    fn from(x: u16) -> Self {
        if let Ok(x) = x.try_into() {
            Uint::mk(Left(x))
        } else {
            Uint::mk(Right(Box::new(x.into())))
        }
    }
}
impl TryFrom<i16> for Uint {
    type Error = IntIsNegativeError;
    fn try_from(x: i16) -> Result<Self, Self::Error> {
        if let Ok(x) = x.try_into() {
            Ok(Uint::mk(Left(x)))
        } else {
            Ok(Uint::mk(Right(Box::new(
                BigInt::from(x).to_biguint().ok_or(IntIsNegativeError())?,
            ))))
        }
    }
}

impl From<u8> for Uint {
    fn from(x: u8) -> Self {
        if let Ok(x) = x.try_into() {
            Uint::mk(Left(x))
        } else {
            Uint::mk(Right(Box::new(x.into())))
        }
    }
}
impl TryFrom<i8> for Uint {
    type Error = IntIsNegativeError;
    fn try_from(x: i8) -> Result<Self, Self::Error> {
        if let Ok(x) = x.try_into() {
            Ok(Uint::mk(Left(x)))
        } else {
            Ok(Uint::mk(Right(Box::new(
                BigInt::from(x).to_biguint().ok_or(IntIsNegativeError())?,
            ))))
        }
    }
}

impl From<usize> for Uint {
    fn from(x: usize) -> Self {
        if let Ok(x) = x.try_into() {
            Uint::mk(Left(x))
        } else {
            Uint::mk(Right(Box::new(x.into())))
        }
    }
}
impl TryFrom<isize> for Uint {
    type Error = IntIsNegativeError;
    fn try_from(x: isize) -> Result<Self, Self::Error> {
        if let Ok(x) = x.try_into() {
            Ok(Uint::mk(Left(x)))
        } else {
            Ok(Uint::mk(Right(Box::new(
                BigInt::from(x).to_biguint().ok_or(IntIsNegativeError())?,
            ))))
        }
    }
}

impl FromPrimitive for Uint {
    fn from_u128(x: u128) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Uint::mk(Left(x)))
        } else {
            Some(Uint::mk(Right(Box::new(x.into()))))
        }
    }
    fn from_i128(x: i128) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Uint::mk(Left(x)))
        } else {
            Some(Uint::mk(Right(Box::new(BigInt::from(x).to_biguint()?))))
        }
    }
    fn from_u64(x: u64) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Uint::mk(Left(x)))
        } else {
            Some(Uint::mk(Right(Box::new(x.into()))))
        }
    }
    fn from_i64(x: i64) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Uint::mk(Left(x)))
        } else {
            Some(Uint::mk(Right(Box::new(BigInt::from(x).to_biguint()?))))
        }
    }
    fn from_u32(x: u32) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Uint::mk(Left(x)))
        } else {
            Some(Uint::mk(Right(Box::new(x.into()))))
        }
    }
    fn from_i32(x: i32) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Uint::mk(Left(x)))
        } else {
            Some(Uint::mk(Right(Box::new(BigInt::from(x).to_biguint()?))))
        }
    }
}

impl From<u128> for Int {
    fn from(x: u128) -> Self {
        if let Ok(x) = x.try_into() {
            Int::mk(Left(x))
        } else {
            Int::mk(Right(Box::new(x.into())))
        }
    }
}
impl From<i128> for Int {
    fn from(x: i128) -> Self {
        if let Ok(x) = x.try_into() {
            Int::mk(Left(x))
        } else {
            Int::mk(Right(Box::new(x.into())))
        }
    }
}
impl From<u64> for Int {
    fn from(x: u64) -> Self {
        if let Ok(x) = x.try_into() {
            Int::mk(Left(x))
        } else {
            Int::mk(Right(Box::new(x.into())))
        }
    }
}
impl From<i64> for Int {
    fn from(x: i64) -> Self {
        if let Ok(x) = x.try_into() {
            Int::mk(Left(x))
        } else {
            Int::mk(Right(Box::new(x.into())))
        }
    }
}
impl From<u32> for Int {
    fn from(x: u32) -> Self {
        if let Ok(x) = x.try_into() {
            Int::mk(Left(x))
        } else {
            Int::mk(Right(Box::new(x.into())))
        }
    }
}
impl From<i32> for Int {
    fn from(x: i32) -> Self {
        if let Ok(x) = x.try_into() {
            Int::mk(Left(x))
        } else {
            Int::mk(Right(Box::new(x.into())))
        }
    }
}

impl From<u16> for Int {
    fn from(x: u16) -> Self {
        if let Ok(x) = x.try_into() {
            Int::mk(Left(x))
        } else {
            Int::mk(Right(Box::new(x.into())))
        }
    }
}
impl From<i16> for Int {
    fn from(x: i16) -> Self {
        if let Ok(x) = x.try_into() {
            Int::mk(Left(x))
        } else {
            Int::mk(Right(Box::new(x.into())))
        }
    }
}

impl From<u8> for Int {
    fn from(x: u8) -> Self {
        if let Ok(x) = x.try_into() {
            Int::mk(Left(x))
        } else {
            Int::mk(Right(Box::new(x.into())))
        }
    }
}
impl From<i8> for Int {
    fn from(x: i8) -> Self {
        if let Ok(x) = x.try_into() {
            Int::mk(Left(x))
        } else {
            Int::mk(Right(Box::new(x.into())))
        }
    }
}

impl From<usize> for Int {
    fn from(x: usize) -> Self {
        if let Ok(x) = x.try_into() {
            Int::mk(Left(x))
        } else {
            Int::mk(Right(Box::new(x.into())))
        }
    }
}
impl From<isize> for Int {
    fn from(x: isize) -> Self {
        if let Ok(x) = x.try_into() {
            Int::mk(Left(x))
        } else {
            Int::mk(Right(Box::new(x.into())))
        }
    }
}

impl FromPrimitive for Int {
    fn from_u128(x: u128) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Int::mk(Left(x)))
        } else {
            Some(Int::mk(Right(Box::new(x.into()))))
        }
    }
    fn from_i128(x: i128) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Int::mk(Left(x)))
        } else {
            Some(Int::mk(Right(Box::new(x.into()))))
        }
    }
    fn from_u64(x: u64) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Int::mk(Left(x)))
        } else {
            Some(Int::mk(Right(Box::new(x.into()))))
        }
    }
    fn from_i64(x: i64) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Int::mk(Left(x)))
        } else {
            Some(Int::mk(Right(Box::new(x.into()))))
        }
    }
    fn from_u32(x: u32) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Int::mk(Left(x)))
        } else {
            Some(Int::mk(Right(Box::new(x.into()))))
        }
    }
    fn from_i32(x: i32) -> Option<Self> {
        if let Ok(x) = x.try_into() {
            Some(Int::mk(Left(x)))
        } else {
            Some(Int::mk(Right(Box::new(x.into()))))
        }
    }
}

impl ToPrimitive for Int {
    fn to_u128(&self) -> Option<u128> {
        match self.0.get_ref() {
            Left(x) => x.try_into().ok(),
            Right(b) => b.to_u128(),
        }
    }
    fn to_i128(&self) -> Option<i128> {
        match self.0.get_ref() {
            Left(x) => x.try_into().ok(),
            Right(b) => b.to_i128(),
        }
    }
    fn to_u64(&self) -> Option<u64> {
        match self.0.get_ref() {
            Left(x) => x.try_into().ok(),
            Right(b) => b.to_u64(),
        }
    }
    fn to_i64(&self) -> Option<i64> {
        match self.0.get_ref() {
            Left(x) => x.try_into().ok(),
            Right(b) => b.to_i64(),
        }
    }
    fn to_u32(&self) -> Option<u32> {
        match self.0.get_ref() {
            Left(x) => x.try_into().ok(),
            Right(b) => b.to_u32(),
        }
    }
    fn to_i32(&self) -> Option<i32> {
        match self.0.get_ref() {
            Left(x) => x.try_into().ok(),
            Right(b) => b.to_i32(),
        }
    }
}

impl ToPrimitive for Uint {
    fn to_u128(&self) -> Option<u128> {
        match self.0.get_ref() {
            Left(x) => x.try_into().ok(),
            Right(b) => b.to_u128(),
        }
    }
    fn to_i128(&self) -> Option<i128> {
        match self.0.get_ref() {
            Left(x) => x.try_into().ok(),
            Right(b) => b.to_i128(),
        }
    }
    fn to_u64(&self) -> Option<u64> {
        match self.0.get_ref() {
            Left(x) => x.try_into().ok(),
            Right(b) => b.to_u64(),
        }
    }
    fn to_i64(&self) -> Option<i64> {
        match self.0.get_ref() {
            Left(x) => x.try_into().ok(),
            Right(b) => b.to_i64(),
        }
    }
    fn to_u32(&self) -> Option<u32> {
        match self.0.get_ref() {
            Left(x) => x.try_into().ok(),
            Right(b) => b.to_u32(),
        }
    }
    fn to_i32(&self) -> Option<i32> {
        match self.0.get_ref() {
            Left(x) => x.try_into().ok(),
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

// The first macro name represents a macro to define e.g. Add; the second represents
// a macro to define e.g. AddAssign.
//
// There are a number of ways to use this macro; the mode is indicated by the last argument,
// which is merely a textual mode indicator. This macro can help with implementing four kinds
// of things:
//
// (1a) impl Add<Int> for Int (and various &-combinations)
// (1b) impl AddAssign<Int> for Int (and AddAssign<&Int>)
// (1a) impl Add<i16> for Int (and various &-combinations, and other base types)
// (1b) impl AddAssign<i16> for Int (and AddAssign<&i16>, and other base types)
//
// I advise you to look at the invocations of this macro, and perhaps also at the macroexpansions.
//
// Example parameter values:
//
//   macroname_value = trait_add_value
//   macroname_mut   = trait_add_mut
//   type     = Int
//   basetype = int (type alias for i32)
//   bigtype  = BigInt
macro_rules! call_with_cow_permutations {
    ($macroname_value:ident, $macroname_mut:ident, $type:tt, $basetype:tt, $bigtype:tt, both signed and unsigned) => {
        call_with_cow_permutations!{$macroname_value, $macroname_mut, $type, $basetype, $bigtype, self case}
        call_with_all_signed_base_types!{
            call_with_cow_permutations,
            $macroname_value, $macroname_mut, $type, $basetype, $bigtype, base type
        }
        call_with_all_unsigned_base_types!{
            call_with_cow_permutations,
            $macroname_value, $macroname_mut, $type, $basetype, $bigtype, base type
        }
    };
    ($macroname_value:ident, $macroname_mut:ident, $type:tt, $basetype:tt, $bigtype:tt, only unsigned) => {
        call_with_cow_permutations!{$macroname_value, $macroname_mut, $type, $basetype, $bigtype, self case}
        call_with_all_unsigned_base_types!{
            call_with_cow_permutations,
            $macroname_value, $macroname_mut, $type, $basetype, $bigtype, base type
        }
    };
    ($macroname_value:ident, $macroname_mut:ident, $type:tt, $basetype:tt, $bigtype:tt) => {
        call_with_cow_permutations!{$macroname_value, $macroname_mut, $type, $basetype, $bigtype, self case}
    };

    // Calls the implementing macros for a number of cases. For example for Add/AddAssign, this would
    // call macros to implement, in order:
    //
    // - Add<Int> for Int
    // - Add<&Int> for Int
    // - Add<Int> for &Int
    // - Add<&Int> for &Int
    //
    // In all cases, the implementing macro would have two cases, one for when self and other are
    // small, one for when one of them is big. The latter case takes a &BigInt, which is provided
    // using .cow_big(). The code fragment argument is inserted to make an expression for &BigInt
    // possible.
    //
    // Also, calls macros to implement AddAssign<Int> and AddAssign<&Int>.
    ($macroname_value:ident, $macroname_mut:ident, $type:tt, $basetype:tt, $bigtype:tt, self case) => {
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, $type, $type, v.get_ref(), {},
            $bigtype::from(self), $bigtype::from(v)
        }
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, $type, &$type, v.get_ref(), {
                let v1 = v.cow_big()
                let v2: &$bigtype = v1.deref()
            }, $bigtype::from(self), v2
        }
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, &$type, $type, v.get_ref(), {
                let self1 = self.cow_big()
                let self2: &$bigtype = self1.deref()
            }, self2, $bigtype::from(v)
        }
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, &$type, &$type, v.get_ref(), {
                let self1 = self.cow_big()
                let self2: &$bigtype = self1.deref()
                let v1 = v.cow_big()
                let v2: &$bigtype = v1.deref()
            }, self2, v2
        }
        $macroname_mut!{$type, $type}
        $macroname_mut!{$type, &$type}
    };

    // Calls the implementing macros for the base types (e.g. Add<i128> for Int), with expressions
    // that first call $bigtype::from(..) on the i128 to convert to &Int.
    ($macroname_value:ident, $macroname_mut:ident, $type:tt, $basetype:ty, $bigtype:tt, base type $baseothertype:ty) => {
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, $type, $baseothertype, Either::<$baseothertype, $type>::Left(v), {},
            $bigtype::from(self), v
        }
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, $type, &$baseothertype, Either::<$baseothertype, $type>::Left(*v), {},
            $bigtype::from(self), *v
        }
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, &$type, $baseothertype, Either::<$baseothertype, $type>::Left(v), {
                let self1 = self.cow_big()
                let self2: &$bigtype = self1.deref()
            }, self2, v
        }
        $macroname_value!{
            $type, $basetype, $bigtype, self, v, &$type, &$baseothertype, Either::<$baseothertype, $type>::Left(*v), {
                let self1 = self.cow_big()
                let self2: &$bigtype = self1.deref()
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
                    if let (Left(x), Left(y)) = ($selfvar.get_ref(), $otheitherref) {
                        if let Ok(y_base) = <$basetype>::try_from(y) {
                            if let Some(z) = <$basetype>::checked_add(x, y_base) {
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

call_with_cow_permutations! {trait_add_value, trait_add_mut, Int, int, BigInt, both signed and unsigned}
call_with_cow_permutations! {trait_add_value, trait_add_mut, Uint, uint, BigUint, only unsigned}

macro_rules! trait_div_value {
    ($type:tt, $basetype:ty, $bigtype:ty, $selfvar:tt, $othvar:ident,
        $selftype:ty, $othtype:ty, $otheitherref:expr,
        {$($makecows:stmt)*}, $bigexpr1:expr, $bigexpr2:expr) => {
        impl Div<$othtype> for $selftype {
            type Output = $type;
            fn div($selfvar, $othvar: $othtype) -> $type {
                if let (Left(x), Left(y)) = ($selfvar.get_ref(), $otheitherref) {
                    if let Ok(y_base) = <$basetype>::try_from(y) {
                        if let Some(z) = <$basetype>::checked_div(x, y_base) {
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

call_with_cow_permutations! {trait_div_value, trait_div_mut, Int, int, BigInt, both signed and unsigned}
call_with_cow_permutations! {trait_div_value, trait_div_mut, Uint, uint, BigUint, only unsigned}

macro_rules! trait_mul_value {
    ($type:tt, $basetype:ty, $bigtype:ty, $selfvar:tt, $othvar:ident,
        $selftype:ty, $othtype:ty, $otheitherref:expr,
        {$($makecows:stmt)*}, $bigexpr1:expr, $bigexpr2:expr) => {
        impl Mul<$othtype> for $selftype {
            type Output = $type;
            fn mul($selfvar, $othvar: $othtype) -> $type {
                if let (Left(x), Left(y)) = ($selfvar.get_ref(), $otheitherref) {
                    if let Ok(y_base) = <$basetype>::try_from(y) {
                        if let Some(z) = <$basetype>::checked_mul(x, y_base) {
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

call_with_cow_permutations! {trait_mul_value, trait_mul_mut, Int, int, BigInt, both signed and unsigned}
call_with_cow_permutations! {trait_mul_value, trait_mul_mut, Uint, uint, BigUint, only unsigned}

macro_rules! trait_rem_value {
    ($type:tt, $basetype:ty, $bigtype:ty, $selfvar:tt, $othvar:ident,
        $selftype:ty, $othtype:ty, $otheitherref:expr,
        {$($makecows:stmt)*}, $bigexpr1:expr, $bigexpr2:expr) => {
        impl Rem<$othtype> for $selftype {
            type Output = $type;
            fn rem($selfvar, $othvar: $othtype) -> $type {
                if let (Left(x), Left(y)) = ($selfvar.get_ref(), $otheitherref) {
                    if let Ok(y_base) = <$basetype>::try_from(y) {
                        if let Some(z) = <$basetype>::checked_rem(x, y_base) {
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

call_with_cow_permutations! {trait_rem_value, trait_rem_mut, Int, int, BigInt, both signed and unsigned}
call_with_cow_permutations! {trait_rem_value, trait_rem_mut, Uint, uint, BigUint, only unsigned}

macro_rules! trait_sub_value {
    ($type:tt, $basetype:ty, $bigtype:ty, $selfvar:tt, $othvar:ident,
        $selftype:ty, $othtype:ty, $otheitherref:expr,
        {$($makecows:stmt)*}, $bigexpr1:expr, $bigexpr2:expr) => {
        impl Sub<$othtype> for $selftype {
            type Output = $type;
            fn sub($selfvar, $othvar: $othtype) -> $type {
                if let (Left(x), Left(y)) = ($selfvar.get_ref(), $otheitherref) {
                    if let Ok(y_base) = <$basetype>::try_from(y) {
                        if let Some(z) = <$basetype>::checked_sub(x, y_base) {
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

call_with_cow_permutations! {trait_sub_value, trait_sub_mut, Int, int, BigInt, both signed and unsigned}
call_with_cow_permutations! {trait_sub_value, trait_sub_mut, Uint, uint, BigUint, only unsigned}

// The checked traits are always a function from (&Self, &Self) to Option<Self>.
// We implement them by first trying them on the base type; if that works, falling
// back to the big type. This could be improved: for certain traits we could give
// an optimized implementation.

macro_rules! checked_trait {
    ($trait:tt, $method:tt, $type:tt) => {
        impl $trait for $type {
            fn $method(&self, other: &Self) -> Option<Self> {
                // Try to do it on the base type.
                if let (Left(x), Left(y)) = (self.get_ref(), other.get_ref()) {
                    if let Some(res) = x.$method(y) {
                        return Some($type::small(res));
                    }
                }
                // If it fails, try again on the big type, otherwise really fail.
                let x_big = self.cow_big();
                let y_big = other.cow_big();
                if let Some(z_big) = x_big.$method(y_big.deref()) {
                    return Some($type::big(z_big));
                } else {
                    return None;
                }
            }
        }
    };
}

macro_rules! call_with_args {
    ($macroname:tt, $baseargs:tt, [$($nextarg:tt),*]) => {
        $(append_macro_call!{$macroname, $baseargs, $nextarg})*
    };
}

macro_rules! append_macro_call {
    ($macroname:tt, ($($baseargs:tt)*), $nextarg:tt) => {
        $macroname!($($baseargs)* $nextarg)
    };
    ($macroname:tt, [$($baseargs:tt)*], $nextarg:tt) => {
        $macroname![$($baseargs)* $nextarg]
    };
    ($macroname:tt, {$($baseargs:tt)*}, $nextarg:tt) => {
        $macroname!{$($baseargs)* $nextarg}
    };
}

call_with_args! {checked_trait, {CheckedAdd, checked_add, }, [Uint, Int]}
call_with_args! {checked_trait, {CheckedDiv, checked_div, }, [Uint, Int]}
call_with_args! {checked_trait, {CheckedMul, checked_mul, }, [Uint, Int]}
// These don't yet exist for num_bigint.
//   call_with_args! {checked_trait, {CheckedNeg, checked_neg, }, [Uint, Int]}
//   call_with_args! {checked_trait, {CheckedRem, checked_rem, }, [Uint, Int]}
//   call_with_args! {checked_trait, {CheckedShl, checked_shl, }, [Uint, Int]}
//   call_with_args! {checked_trait, {CheckedShr, checked_shr, }, [Uint, Int]}
call_with_args! {checked_trait, {CheckedSub, checked_sub, }, [Uint, Int]}

macro_rules! trait_partialeq {
    (base, $type:tt, $basetype:ty) => {
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

        // These are just lazy variants so you don't have to do * yourself when
        // one is a reference and one isn't.
        impl_ref_variants! {PartialEq, eq, $type, $basetype, bool}
        impl_ref_variants! {PartialEq, eq, $basetype, $type, bool}
    };
}

call_with_all_unsigned_base_types!(trait_partialeq, base, Uint,);
call_with_all_unsigned_base_types!(trait_partialeq, base, Int,);
call_with_all_signed_base_types!(trait_partialeq, base, Uint,);
call_with_all_signed_base_types!(trait_partialeq, base, Int,);

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

        impl_ref_variants! {PartialOrd, partial_cmp, $type, $basetype, Option<Ordering>}
        impl_ref_variants! {PartialOrd, partial_cmp, $basetype, $type, Option<Ordering>}
    };
}

call_with_all_unsigned_base_types!(trait_partialord_straight, Uint);
call_with_all_unsigned_base_types!(trait_partialord_straight, Int);
call_with_all_signed_base_types!(trait_partialord_straight, Uint);
call_with_all_signed_base_types!(trait_partialord_straight, Int);

#[cfg(test)]
mod test {
    #![allow(clippy::redundant_clone, clippy::cognitive_complexity, clippy::op_ref)]
    use super::*;
    #[test]
    fn test_unsigned() {
        println!("Size of Uint: {}", std::mem::size_of::<Uint>());

        let eleven = Uint::small(11);
        assert_eq!(eleven, 11u8);
        assert_eq!(&eleven, 11u8);
        assert_eq!(eleven, &11u8);
        assert_ne!(eleven, 10u8);
        assert_eq!(11u8, eleven);
        assert_ne!(10u8, eleven);
        assert_eq!(eleven, 11i8);
        assert_ne!(eleven, 10i8);
        assert_eq!(11i8, eleven);
        assert_ne!(10i8, eleven);
        assert!(eleven.get_ref().is_left());
        assert!(eleven.clone().get_ref().is_left());
        assert!(eleven.clone().normalize().get_ref().is_left());

        let eleven_pow11 = &eleven
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
        assert!(eleven_pow11.get_ref().is_right());
        assert!(eleven_pow11.clone().get_ref().is_right());
        assert!(eleven_pow11.clone().normalize().get_ref().is_right());
        assert!(eleven < eleven_pow11);
        assert!(&eleven < eleven_pow11);
        assert!(eleven < &eleven_pow11);
        assert!(11u8 < eleven_pow11);
        assert!(11i8 < eleven_pow11);
        let eleven_big = Uint::big(BigUint::from(11u8));
        let eleven_big_norm = eleven_big.clone().normalize();
        let eleven_big_norm_ref = eleven_big.normalize_ref();
        assert_eq!(eleven, eleven_big);
        assert_eq!(&eleven, eleven_big);
        assert_eq!(eleven, &eleven_big);
        assert_eq!(eleven, eleven_big_norm);
        assert_eq!(eleven, *eleven_big_norm_ref);
        assert_eq!(eleven_big.is_stored_as_big(), true);
        assert_eq!(eleven_big_norm.is_stored_as_big(), false);
        assert_eq!(eleven_big_norm_ref.is_stored_as_big(), false);
        let eleven_pow11_norm = eleven_pow11.clone().normalize();
        let eleven_pow11_norm_ref = eleven_pow11.normalize_ref();
        assert_eq!(eleven_pow11, eleven_pow11_norm);
        assert_eq!(eleven_pow11, *eleven_pow11_norm_ref);
        assert_eq!(
            &eleven_pow11 + &eleven_pow11,
            eleven_pow11.checked_add(&eleven_pow11).unwrap()
        );
    }
    #[test]
    fn test_signed() {
        println!("Size of Int: {}", std::mem::size_of::<Int>());

        let eleven = Int::small(11);
        assert_eq!(eleven, 11u8);
        assert_eq!(&eleven, 11u8);
        assert_eq!(eleven, &11u8);
        assert_ne!(eleven, 10u8);
        assert_eq!(11u8, eleven);
        assert_ne!(10u8, eleven);
        assert_eq!(eleven, 11i8);
        assert_ne!(eleven, 10i8);
        assert_eq!(11i8, eleven);
        assert_ne!(10i8, eleven);
        assert!(eleven.get_ref().is_left());
        assert!(eleven.clone().get_ref().is_left());
        assert!(eleven.clone().normalize().get_ref().is_left());

        let eleven_pow11 = &eleven
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
        assert!(eleven_pow11.get_ref().is_right());
        assert!(eleven_pow11.clone().get_ref().is_right());
        assert!(eleven_pow11.clone().normalize().get_ref().is_right());
        assert!(eleven < eleven_pow11);
        assert!(&eleven < eleven_pow11);
        assert!(eleven < &eleven_pow11);
        assert!(-eleven.clone() < eleven_pow11);
        assert!(-eleven_pow11.clone() < eleven);
        assert!(-eleven_pow11.clone() < -eleven.clone());
        assert!(11u8 < eleven_pow11);
        assert!(11i8 < eleven_pow11);
        assert!(-11i8 < eleven_pow11);
        assert!(-eleven_pow11.clone() < 11i8);
        assert!(-eleven_pow11.clone() < -11i8);
        let eleven_big = Int::big(BigInt::from(11i8));
        let eleven_big_norm = eleven_big.clone().normalize();
        let eleven_big_norm_ref = eleven_big.normalize_ref();
        assert_eq!(eleven, eleven_big);
        assert_eq!(&eleven, eleven_big);
        assert_eq!(eleven, &eleven_big);
        assert_eq!(eleven, eleven_big_norm);
        assert_eq!(eleven, *eleven_big_norm_ref);
        assert_eq!(eleven_big.is_stored_as_big(), true);
        assert_eq!(eleven_big_norm.is_stored_as_big(), false);
        assert_eq!(eleven_big_norm_ref.is_stored_as_big(), false);
        let eleven_pow11_norm = eleven_pow11.clone().normalize();
        let eleven_pow11_norm_ref = eleven_pow11.normalize_ref();
        assert_eq!(eleven_pow11, eleven_pow11_norm);
        assert_eq!(eleven_pow11, *eleven_pow11_norm_ref);
        assert_eq!(
            &eleven_pow11 + &eleven_pow11,
            eleven_pow11.checked_add(&eleven_pow11).unwrap()
        );
    }
}
