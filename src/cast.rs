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

macro_rules! cast_impls {
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

cast_impls! {
  i8 => u8;
  i32 => u32;
  i64 => u64;
  u8 => i8 usize;
  u32 => i32 usize;
  u64 => i64 usize;
  usize => u8 u32 u64;
}
