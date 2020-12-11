use either::{Either, Left, Right};
use std::marker::PhantomData;

// This stuff only works on 64-bit architectures. Fail early, if we're not on 64-bit.
#[cfg(not(target_pointer_width = "64"))]
fn ThisModuleOnlyWorksOn64BitArchitectures() -> ! {}

/// The least significant bit of the u64 is 0 for a u32 (which is shifted up by
/// 32 bits) and it is 1 for a pointer.
pub(crate) struct UnsafeU32OrBox<T> {
    inner: u64,
    phantom: PhantomData<T>,
}

const fn mk_raw<T>(v: u64) -> UnsafeU32OrBox<T> {
    UnsafeU32OrBox {
        inner: v,
        phantom: PhantomData,
    }
}

const fn pack_left(i: u32) -> u64 {
    (i as u64) << 32
}

fn pack<T>(v: Either<u32, Box<T>>) -> u64 {
    match v {
        Left(i) => pack_left(i),
        Right(b) => {
            let ptr: *mut T = Box::into_raw(b);
            let ptr_num = ptr as u64;
            // Pointers must be 2-aligned for this to work. This check will
            // hopefully be compiled away to nothing.
            assert!(ptr_num & 1 == 0);
            ptr_num + 1
        }
    }
}

fn unpack<T>(inner: u64) -> Either<u32, *mut T> {
    if inner & 1 == 0 {
        Left((inner >> 32) as u32)
    } else {
        Right((inner & !(1 as u64)) as *mut T)
    }
}

impl<T> UnsafeU32OrBox<T> {
    pub const fn make_left(i: u32) -> Self {
        mk_raw(pack_left(i))
    }

    pub fn make(v: Either<u32, Box<T>>) -> Self {
        mk_raw(pack(v))
    }

    fn take(&mut self) -> Either<u32, Box<T>> {
        let inner = std::mem::replace(&mut self.inner, 0u64); // 0 is safe
        unpack::<T>(inner).map_right(|ptr| unsafe { Box::from_raw(ptr) })
    }

    pub fn get_ref(&self) -> Either<u32, &T> {
        unpack::<T>(self.inner).map_right(|ptr| Box::leak(unsafe { Box::from_raw(ptr) }) as &T)
    }

    pub fn get(mut self) -> Either<u32, Box<T>> {
        self.take()
    }
}

impl<T> Drop for UnsafeU32OrBox<T> {
    fn drop(&mut self) {
        self.take();
    }
}

impl<T: Clone> Clone for UnsafeU32OrBox<T> {
    fn clone(&self) -> Self {
        UnsafeU32OrBox::make(self.get_ref().map_right(|b| Box::new(b.clone())))
    }
}

// Same as UnsafeU32OrBox but reinterprets the u32 to i32 and vice versa.
#[derive(Clone)]
pub(crate) struct UnsafeI32OrBox<T>(UnsafeU32OrBox<T>);

impl<T> UnsafeI32OrBox<T> {
    pub const fn make_left(i: i32) -> Self {
        UnsafeI32OrBox(UnsafeU32OrBox::make_left(i as u32))
    }
    pub fn make(v: Either<i32, Box<T>>) -> Self {
        match v {
            Left(i) => UnsafeI32OrBox(UnsafeU32OrBox::make(Left(i as u32))),
            Right(b) => UnsafeI32OrBox(UnsafeU32OrBox::make(Right(b))),
        }
    }

    pub fn get(self) -> Either<i32, Box<T>> {
        match self.0.get() {
            Left(i) => Left(i as i32),
            Right(b) => Right(b),
        }
    }

    pub fn get_ref(&self) -> Either<i32, &T> {
        match self.0.get_ref() {
            Left(i) => Left(i as i32),
            Right(br) => Right(br),
        }
    }
}
