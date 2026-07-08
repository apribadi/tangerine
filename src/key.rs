//! This module provides traits for hashable keys representable as non-zero
//! integers.

use core::num::NonZeroI16;
use core::num::NonZeroI32;
use core::num::NonZeroI64;
use core::num::NonZeroI8;
use core::num::NonZeroIsize;
use core::num::NonZeroU16;
use core::num::NonZeroU32;
use core::num::NonZeroU64;
use core::num::NonZeroU8;
use core::num::NonZeroUsize;

/// A sealed trait for hashable keys representable as non-zero integers. The
/// only way to implement this trait for additional types is to implement the
/// [`IntoKey`] trait.
///
/// Types that implement this trait will usually be `Copy`, though that is not
/// strictly required.
#[allow(private_bounds)]
pub trait Key: private::Key {
}

/// A trait for representing keys as non-zero integers.
///
/// For logical correctness, the key ought to be in some sense "the same" after
/// a round trip.
///
/// # Safety
///
/// It must be sound apply `from_key` to the result of `into_key`, possibly
/// multiple times, e.g.
///
/// ```text
/// let a = T::into_key(x);
/// let b = unsafe { T::from_key(a) };
/// let c = unsafe { T::from_key(a) };
/// ```
pub unsafe trait IntoKey {
  /// Target key type.
  type Key: Key;

  /// An injective transformation.
  fn into_key(_: Self) -> Self::Key;

  /// The inverse of `into_key`.
  unsafe fn from_key(_: Self::Key) -> Self;
}

impl<T: IntoKey> Key for T {
}

unsafe impl<T: IntoKey> private::Key for T {
  type Hash = <T::Key as private::Key>::Hash;

  type Word = <T::Key as private::Key>::Word;

  #[inline(always)]
  fn into_word(x: Self) -> Self::Word {
    <T::Key as private::Key>::into_word(T::into_key(x))
  }

  #[inline(always)]
  unsafe fn from_word(x: Self::Word) -> Self {
    unsafe { T::from_key(<T::Key as private::Key>::from_word(x)) }
  }
}

macro_rules! impl_key_for {
  ($($nzint:ty => $word:ty;)*) => {
    $(
    impl Key for $nzint {
    }

    unsafe impl private::Key for $nzint {
      type Hash = <$word as crate::word::Word>::Hash;

      type Word = $word;

      #[inline(always)]
      fn into_word(x: Self) -> Self::Word {
        #[allow(trivial_numeric_casts)]
        return x.get() as _
      }

      #[inline(always)]
      unsafe fn from_word(x: Self::Word) -> Self {
        #[allow(trivial_numeric_casts)]
        return unsafe { Self::new_unchecked(x as _) }
      }
    }
    )*
  };
}

impl_key_for! {
  NonZeroI8 => u8;
  NonZeroI16 => u16;
  NonZeroI32 => u32;
  NonZeroI64 => u64;
  NonZeroU8 => u8;
  NonZeroU16 => u16;
  NonZeroU32 => u32;
  NonZeroU64 => u64;
}

cfg_select! {
  target_pointer_width = "16" => {
    impl_key_for! {
      NonZeroIsize => u16;
      NonZeroUsize => u16;
    }
  }
  target_pointer_width = "32" => {
    impl_key_for! {
      NonZeroIsize => u32;
      NonZeroUsize => u32;
    }
  }
  target_pointer_width = "64" => {
    impl_key_for! {
      NonZeroIsize => u64;
      NonZeroUsize => u64;
    }
  }
  _ => {
  }
}

pub(crate) mod private {
  pub(crate) unsafe trait Key: Sized {
    type Hash: crate::hash::Hash<Self::Word>;

    type Word: crate::word::Word;

    fn into_word(_: Self) -> Self::Word;

    unsafe fn from_word(_: Self::Word) -> Self;
  }
}
