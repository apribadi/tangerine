use casting::CastInto;
use casting::CastFrom;

pub(crate) unsafe trait Word
  : Copy
  + Ord
  + CastInto<usize>
  + CastFrom<usize>
  + CastInto<Self::Signed>
  + CastFrom<Self::Signed>
  + core::ops::BitOr<Self, Output = Self>
  + core::ops::Not<Output = Self>
  + core::ops::Shr<usize, Output = Self>
{
  type Signed
    : Copy
    + core::ops::Shr<usize, Output = Self::Signed>;

  const BITS: usize;

  const MAX: Self;

  #[inline(always)]
  fn asr(x: Self, n: usize) -> Self {
    let x: Self::Signed = x.cast_into();
    let x = x >> n;
    let x: Self = x.cast_into();
    x
  }
}

unsafe impl Word for u32 {
  type Signed = i32;

  const BITS: usize = 32;

  const MAX: Self = u32::MAX;
}

unsafe impl Word for u64 {
  type Signed = i64;

  const BITS: usize = 64;

  const MAX: Self = u64::MAX;
}
