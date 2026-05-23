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

macro_rules! impl_cast_from {
  ($src:ty, $dst:ty) => {
    impl CastFrom<$src> for $dst {
      #[inline(always)]
      fn cast_from(x: $src) -> $dst {
        x as $dst
      }
    }
  }
}

impl Cast for i32 { }
impl Cast for i64 { }
impl Cast for u32 { }
impl Cast for u64 { }
impl Cast for usize { }

impl_cast_from!(i32, u32);
impl_cast_from!(i64, u64);
impl_cast_from!(u32, i32);
impl_cast_from!(u32, usize);
impl_cast_from!(u64, i64);
impl_cast_from!(u64, usize);
impl_cast_from!(usize, u32);
impl_cast_from!(usize, u64);
