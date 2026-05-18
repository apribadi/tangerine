use core::num::NonZeroU32;
use core::num::NonZeroU64;
use rand_core::Rng;
use crate::key::IntoKey;

pub(crate) unsafe trait Key: Sized {
  type Word: Hash + Word;

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

pub(crate) unsafe trait Hash {
  type Seed0: Copy;

  type Seed1: Copy;

  fn seed_nondet() -> (Self::Seed0, Self::Seed1);

  fn seed(_: &mut impl Rng) -> (Self::Seed0, Self::Seed1);

  fn hash(_: Self, _: Self::Seed0) -> Self;

  fn invert_hash(_: Self, _: Self::Seed1) -> Self;
}

pub(crate) unsafe trait Word: Copy + Ord {
  const BITS: usize;

  const MAX: Self;

  fn capacity(_: usize) -> usize;

  fn slot(_: Self, _: usize) -> usize;
}

unsafe impl Word for u32 {
  const BITS: usize = 32;

  const MAX: Self = u32::MAX;

  #[inline(always)]
  fn capacity(s: usize) -> usize {
    const { assert!(usize::BITS >= 32) };
    let n = 0x8000_0000_usize >> s;
    let n = n as u32;
    let n = n | (((n as i32) >> 31) as u32);
    n as usize
  }

  #[inline(always)]
  fn slot(h: Self, s: usize) -> usize {
    const { assert!(usize::BITS >= 32) };
    (h as usize) >> s
  }
}

unsafe impl Word for u64 {
  const BITS: usize = 64;

  const MAX: Self = u64::MAX;

  #[inline(always)]
  fn capacity(s: usize) -> usize {
    let n = 0x8000_0000_0000_0000_u64 >> s;
    let n = n | (((n as i64) >> 63) as u64);
    n as usize
  }

  #[inline(always)]
  fn slot(h: Self, s: usize) -> usize {
    (h >> s) as usize
  }
}
