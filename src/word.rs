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

      const BITS: usize = 8 * size_of::<Self>();

      const MAX: Self = ! 0;

      const MSB: Self = ! (! 0 >> 1);

      // NOTE: A "full size" table configuration has `shift == 0`. It requires zero
      // overflow space, as the last slot would be occupied by `MAX`. The capacity
      // can be `2 ** BITS - 1`
      //
      // It is only possible to allocate a table this large when the key size is
      // strictly less than the pointer size.

      // NOTE: For `capacity` and `slot`, it can improve code generation to operate on
      // `usize`s when possible.

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
