use num_traits::cast::ToPrimitive;

/// An alias for a part of ToPrimitive, in a way that the type system can handle in an
/// easier way.
pub trait ToGeneric<Res> {
    fn to_generic(&self) -> Option<Res>;
}
impl<T: ToPrimitive> ToGeneric<u8> for T {
    fn to_generic(&self) -> Option<u8> {
        self.to_u8()
    }
}
impl<T: ToPrimitive> ToGeneric<u16> for T {
    fn to_generic(&self) -> Option<u16> {
        self.to_u16()
    }
}
impl<T: ToPrimitive> ToGeneric<u32> for T {
    fn to_generic(&self) -> Option<u32> {
        self.to_u32()
    }
}
impl<T: ToPrimitive> ToGeneric<u64> for T {
    fn to_generic(&self) -> Option<u64> {
        self.to_u64()
    }
}
impl<T: ToPrimitive> ToGeneric<u128> for T {
    fn to_generic(&self) -> Option<u128> {
        self.to_u128()
    }
}
impl<T: ToPrimitive> ToGeneric<usize> for T {
    fn to_generic(&self) -> Option<usize> {
        self.to_usize()
    }
}
impl<T: ToPrimitive> ToGeneric<i8> for T {
    fn to_generic(&self) -> Option<i8> {
        self.to_i8()
    }
}
impl<T: ToPrimitive> ToGeneric<i16> for T {
    fn to_generic(&self) -> Option<i16> {
        self.to_i16()
    }
}
impl<T: ToPrimitive> ToGeneric<i32> for T {
    fn to_generic(&self) -> Option<i32> {
        self.to_i32()
    }
}
impl<T: ToPrimitive> ToGeneric<i64> for T {
    fn to_generic(&self) -> Option<i64> {
        self.to_i64()
    }
}
impl<T: ToPrimitive> ToGeneric<i128> for T {
    fn to_generic(&self) -> Option<i128> {
        self.to_i128()
    }
}
impl<T: ToPrimitive> ToGeneric<isize> for T {
    fn to_generic(&self) -> Option<isize> {
        self.to_isize()
    }
}
