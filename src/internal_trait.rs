use core::num::NonZeroU32;
use core::num::NonZeroU64;
use rand_core::Rng;
use crate::key::IntoKey;

pub(crate) unsafe trait Key: Sized {
  type Word: Hash + Word;

  const BITS: usize = Self::Word::BITS;

  const MAX: Self::Word = Self::Word::MAX;

  fn into_word(_: Self) -> Self::Word;

  unsafe fn from_word(_: Self::Word) -> Self;
}

unsafe impl Key for NonZeroU32 {
  type Word = u32;

  #[inline(always)]
  fn into_word(x: Self) -> Self::Word {
    x.get()
  }

  #[inline(always)]
  unsafe fn from_word(x: Self::Word) -> Self {
    unsafe { Self::new_unchecked(x) }
  }
}

unsafe impl Key for NonZeroU64 {
  type Word = u64;

  #[inline(always)]
  fn into_word(x: Self) -> Self::Word {
    x.get()
  }

  #[inline(always)]
  unsafe fn from_word(x: Self::Word) -> Self {
    unsafe { Self::new_unchecked(x) }
  }
}

unsafe impl<K: Key, T: IntoKey<Key = K>> Key for T {
  type Word = K::Word;

  #[inline(always)]
  fn into_word(x: Self) -> Self::Word {
    K::into_word(T::inject(x))
  }

  #[inline(always)]
  unsafe fn from_word(x: Self::Word) -> Self {
    unsafe { T::project(K::from_word(x)) }
  }
}

pub(crate) unsafe trait Word:
  Copy
  + Ord
  + Into<u64>
  + core::ops::Add<Self, Output = Self>
  + core::ops::BitOr<Self, Output = Self>
  + core::ops::Not<Output = Self>
  + core::ops::Shr<usize, Output = Self>
  + int_cast::IntCast
  + int_cast::BoundedCastFromInt<u64>
  + int_cast::BoundedCastFromInt<Self::UInt>
{
  type UInt:
    Copy
    + core::ops::Shr<usize, Output = Self::UInt>
    + Into<u64>
    + int_cast::IntCast
    + int_cast::CastFromInt<Self>;


  const BITS: usize;

  const MAX: Self;

  fn asr(_: Self, _: usize) -> Self;
}

unsafe impl Word for u32 {
  type UInt = u64;

  const BITS: usize = Self::BITS as usize;

  const MAX: Self = Self::MAX;

  #[inline(always)]
  fn asr(x: Self, s: usize) -> Self {
    (x as i32 >> s) as u32
  }
}

unsafe impl Word for u64 {
  type UInt = u64;

  const BITS: usize = Self::BITS as usize;

  const MAX: Self = Self::MAX;

  #[inline(always)]
  fn asr(x: Self, s: usize) -> Self {
    (x as i64 >> s) as u64
  }
}

pub(crate) unsafe trait Hash {
  type Seed0: Copy;

  type Seed1: Copy;

  fn seed_nondet() -> (Self::Seed0, Self::Seed1);

  fn seed(_: &mut impl Rng) -> (Self::Seed0, Self::Seed1);

  fn hash(_: Self, _: Self::Seed0) -> Self;

  fn invert_hash(_: Self, _: Self::Seed1) -> Self;
}
