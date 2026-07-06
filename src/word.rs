// an agglomeration of things we need for each word size that we support

use crate::cast::Cast;
use crate::cast::CastFrom;
use crate::cast::CastInto;
use crate::cast::CastSigned;
use crate::cast::CastUnsigned;
use crate::hash::Hash;

pub(crate) trait Word
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
  type Hash: Hash<Self>;

  const BITS: u32 = (8 * size_of::<Self>()) as u32;

  const MAX: Self;
}

impl Word for u8 {
  type Hash = crate::hash::backend::HashB;

  const MAX: Self = u8::MAX;
}

impl Word for u16 {
  type Hash = crate::hash::backend::HashH;

  const MAX: Self = u16::MAX;
}

impl Word for u32 {
  type Hash = crate::hash::backend::HashW;

  const MAX: Self = u32::MAX;
}

impl Word for u64 {
  type Hash = crate::hash::backend::HashD;

  const MAX: Self = u64::MAX;
}
