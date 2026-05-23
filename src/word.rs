use crate::cast::Cast;
use crate::cast::CastInto;
use crate::cast::CastFrom;

pub(crate) unsafe trait Word
  : Copy
  + Ord
  + Cast
  + CastFrom<Self::Signed>
  + CastFrom<usize>
  + CastInto<Self::Signed>
  + CastInto<usize>
  + core::ops::BitOr<Self, Output = Self>
  + core::ops::Not<Output = Self>
  + core::ops::Shr<usize, Output = Self>
{
  type Signed
    : Copy
    + Cast
    + core::ops::Shr<usize, Output = Self::Signed>;

  const BITS: usize;

  const MAX: Self;

  #[inline(always)]
  fn asr(x: Self, n: usize) -> Self {
    (x.cast::<Self::Signed>() >> n).cast()
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
