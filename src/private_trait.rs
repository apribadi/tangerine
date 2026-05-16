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

  #[inline(always)]
  fn hash(x: Self, m: <Self::Word as Hash>::Seed0) -> Self::Word {
    Self::Word::hash(Self::into_word(x), m)
  }

  #[inline(always)]
  unsafe fn invert_hash(x: Self::Word, m: <Self::Word as Hash>::Seed1) -> Self {
    unsafe { Self::from_word(Self::Word::invert_hash(x, m)) }
  }
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

unsafe impl<T: IntoKey> Key for T {
  type Word = <T::Key as Key>::Word;

  #[inline(always)]
  fn into_word(x: Self) -> Self::Word {
    <T::Key as Key>::into_word(T::inject(x))
  }

  #[inline(always)]
  unsafe fn from_word(x: Self::Word) -> Self {
    unsafe { T::project(<T::Key as Key>::from_word(x)) }
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
{
  const BITS: usize;

  const MAX: Self;

  fn asr(_: Self, _: usize) -> Self;

  fn from_u64(_: u64) -> Self;
}

unsafe impl Word for u32 {
  const BITS: usize = 32;

  const MAX: Self = u32::MAX;

  #[inline(always)]
  fn asr(x: Self, s: usize) -> Self {
    ((x as i32) >> s) as u32
  }

  #[inline(always)]
  fn from_u64(x: u64) -> Self {
    x as Self
  }
}

unsafe impl Word for u64 {
  const BITS: usize = 64;

  const MAX: Self = u64::MAX;

  #[inline(always)]
  fn asr(x: Self, s: usize) -> Self {
    ((x as i64) >> s) as u64
  }

  #[inline(always)]
  fn from_u64(x: u64) -> Self {
    x
  }
}

pub(crate) unsafe trait Hash {
  type Seed: Copy;

  type Seed0: Copy;

  type Seed1: Copy;

  fn seed0(_: Self::Seed) -> Self::Seed0;

  fn seed1(_: Self::Seed) -> Self::Seed1;

  fn seed_nondet() -> Self::Seed;

  fn seed(_: &mut impl Rng) -> Self::Seed;

  fn hash(_: Self, _: Self::Seed0) -> Self;

  fn invert_hash(_: Self, _: Self::Seed1) -> Self;
}
