//! traits for generic casting of primitive types

pub(crate) trait CastFrom<T> {
  fn cast_from(x: T) -> Self;
}

impl<T> CastFrom<T> for T {
  #[inline(always)]
  fn cast_from(x: T) -> Self {
    x
  }
}

pub(crate) trait CastInto<T> {
  fn cast_into(x: Self) -> T;
}

impl<T, U: CastFrom<T>> CastInto<U> for T {
  #[inline(always)]
  fn cast_into(x: Self) -> U {
    U::cast_from(x)
  }
}

pub(crate) trait Cast: Sized {
  #[inline(always)]
  fn cast<T>(self) -> T where Self: CastInto<T> {
    Self::cast_into(self)
  }
}

macro_rules! cast_from_into_impls {
  ($($src:ty => $($dst:ty)*;)*) => {
    $(
      impl Cast for $src {
      }
    $(
      impl CastFrom<$src> for $dst {
          #[inline(always)]
          fn cast_from(x: $src) -> $dst {
            x as $dst
          }
      }
    )*
    )*
  };
}

cast_from_into_impls! {
  u8 => usize;
  u16 => usize;
  u32 => usize;
  u64 => usize;
  usize => u8 u16 u32 u64;
}

pub(crate) trait CastSigned {
  type Output;

  fn cast_signed(self) -> Self::Output;
}

pub(crate) trait CastUnsigned {
  type Output;

  fn cast_unsigned(self) -> Self::Output;
}

macro_rules! cast_signed_unsigned_impls {
  ($($sint:ty, $uint:ty;)*) => {
    $(
      impl CastSigned for $uint {
        type Output = $sint;

        #[inline(always)]
        fn cast_signed(self) -> Self::Output {
          self as $sint
        }
      }

      impl CastUnsigned for $sint {
        type Output = $uint;

        #[inline(always)]
        fn cast_unsigned(self) -> Self::Output {
          self as $uint
        }
      }
    )*
  };
}

cast_signed_unsigned_impls! {
  i8, u8;
  i16, u16;
  i32, u32;
  i64, u64;
}
