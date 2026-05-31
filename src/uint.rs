use crate::cast::Cast;
use crate::cast::CastFrom;
use crate::cast::CastInto;
use crate::cast::CastSigned;
use crate::cast::CastUnsigned;

pub(crate) unsafe trait UInt
  : Copy
  + Ord
  + Cast
  + CastFrom<usize>
  + CastInto<usize>
  + CastSigned<Output: CastUnsigned<Output = Self> + core::ops::Shr<usize, Output = <Self as CastSigned>::Output>>
  + core::ops::BitOr<Self, Output = Self>
  + core::ops::Not<Output = Self>
  + core::ops::Shr<usize, Output = Self>
{
  const BITS: usize = 8 * size_of::<Self>();

  const MAX: Self;

  #[inline(always)]
  fn asr(x: Self, n: usize) -> Self {
    (x.cast_signed() >> n).cast_unsigned()
  }
}

unsafe impl UInt for u8 {
  const MAX: Self = u8::MAX;
}

unsafe impl UInt for u16 {
  const MAX: Self = u16::MAX;
}

unsafe impl UInt for u32 {
  const MAX: Self = u32::MAX;
}

unsafe impl UInt for u64 {
  const MAX: Self = u64::MAX;
}
