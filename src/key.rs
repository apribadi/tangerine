//! This module provides traits for hashable keys representable as [`NonZeroU32`]
//! or [`NonZeroU64`].

use core::num::NonZeroU32;
use core::num::NonZeroU64;

use crate::word::Word;
use crate::hash::Hash;

/// A sealed trait for hashable keys representable as [`NonZeroU32`] or
/// [`NonZeroU64`]. The only way to implement this trait for additional types is
/// to implement the [`IntoKey`] trait.
///
/// Types that implement this trait will usually be `Copy`, though that is not
/// strictly required.
#[allow(private_bounds)]
pub trait Key: private::Key {
}

impl Key for NonZeroU32 {
}

impl Key for NonZeroU64 {
}

impl<T: IntoKey> Key for T {
}

/// A trait for representing keys as [`NonZeroU32`] or [`NonZeroU64`].
///
/// For logical correctness, the key ought to be in some sense "the same" after
/// a round trip.
///
/// # Safety
///
/// It must be sound to `project` the result of any `inject`, possibly multiple
/// times, e.g.
///
/// ```text
/// let y = T::inject(x);
/// let ... = unsafe { T::project(y) };
/// let ... = unsafe { T::project(y) };
/// ```
pub unsafe trait IntoKey {
  #![allow(missing_docs)]

  type Key: Key;

  fn inject(_: Self) -> Self::Key;

  unsafe fn project(_: Self::Key) -> Self;
}

unsafe impl private::Key for NonZeroU32 {
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

unsafe impl private::Key for NonZeroU64 {
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

unsafe impl<T: IntoKey> private::Key for T {
  type Word = <T::Key as private::Key>::Word;

  #[inline(always)]
  fn into_word(x: Self) -> Self::Word {
    <T::Key as private::Key>::into_word(T::inject(x))
  }

  #[inline(always)]
  unsafe fn from_word(x: Self::Word) -> Self {
    unsafe { T::project(<T::Key as private::Key>::from_word(x)) }
  }
}

pub(crate) mod private {
  use super::Hash;
  use super::Word;

  pub(crate) unsafe trait Key: Sized {
    type Word: Hash + Word;

    const BITS: usize = Self::Word::BITS;

    const ZERO: Self::Word = Self::Word::ZERO;

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
}
