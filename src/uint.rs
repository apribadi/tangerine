use crate::cast::Cast;
use crate::cast::CastInto;
use crate::cast::CastFrom;

pub(crate) unsafe trait UInt
  : Copy
  + Ord
  + Cast
  + CastFrom<Self::SInt>
  + CastFrom<usize>
  + CastInto<Self::SInt>
  + CastInto<usize>
  + core::ops::BitOr<Self, Output = Self>
  + core::ops::Not<Output = Self>
  + core::ops::Shr<usize, Output = Self>
{
  type SInt
    : Copy
    + Cast
    + core::ops::Shr<usize, Output = Self::SInt>;

  const BITS: usize;

  const MAX: Self;

  #[inline(always)]
  fn asr(x: Self, n: usize) -> Self {
    (x.cast::<Self::SInt>() >> n).cast()
  }
}

unsafe impl UInt for u32 {
  type SInt = i32;

  const BITS: usize = 32;

  const MAX: Self = u32::MAX;
}

unsafe impl UInt for u64 {
  type SInt = i64;

  const BITS: usize = 64;

  const MAX: Self = u64::MAX;
}
