//! This module provides traits for hashable keys representable as [`NonZeroU32`]
//! or [`NonZeroU64`].

use core::num::NonZeroU32;
use core::num::NonZeroU64;

/// A sealed trait for hashable keys representable as [`NonZeroU32`] or
/// [`NonZeroU64`]. The only way to implement this trait for additional types is
/// to implement the [`IntoKey`] trait.
///
/// Types that implement this trait will usually be `Copy`, though that is not
/// strictly required.
#[allow(private_bounds)]
pub trait Key: internal::Key {
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

pub(crate) mod internal {
  use core::num::NonZeroU32;
  use core::num::NonZeroU64;
  use super::IntoKey;
  use crate::hash::Hash;
  use crate::word::Word;

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
}
