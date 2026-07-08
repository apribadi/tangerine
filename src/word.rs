// an agglomeration of things we need for each word size that we support

use crate::hash::Hash;

pub(crate) trait Word: Copy + Ord {
  type Hash: Hash<Self>;

  const BITS: usize;

  const MAX: Self;

  const MSB: Self;

  fn capacity(_: usize) -> usize;

  fn slot(_: Self, _: usize) -> usize;
}

macro_rules! impl_word_for {
  ($($word:ty => $hash:ty;)*) => {
    $(
    impl Word for $word {
      type Hash = $hash;

      const BITS: usize = <$word>::BITS as usize;

      const MAX: Self = <$word>::MAX;

      const MSB: Self = 1 << Self::BITS - 1;

      #[inline(always)]
      fn capacity(shift: usize) -> usize {
        if const { size_of::<Self>() < size_of::<usize>() } {
          let n = ((Self::MSB as usize) >> shift) as Self;
          let n = n | (n.cast_signed() >> Self::BITS - 1).cast_unsigned();
          n as usize
        } else {
          (Self::MSB >> shift) as usize
        }
      }

      #[inline(always)]
      fn slot(hash: Self, shift: usize) -> usize {
        if const { size_of::<Self>() < size_of::<usize>() } {
          (hash as usize) >> shift
        } else {
          (hash >> shift) as usize
        }
      }
    }
    )*
  };
}

impl_word_for! {
  u8 => crate::hash::backend::HashB;
  u16 => crate::hash::backend::HashH;
  u32 => crate::hash::backend::HashW;
  u64 => crate::hash::backend::HashD;
}
