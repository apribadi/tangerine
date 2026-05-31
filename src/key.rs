//! This module provides traits for hashable keys representable as non-zero
//! integers.

use core::num::NonZeroI8;
use core::num::NonZeroI16;
use core::num::NonZeroI32;
use core::num::NonZeroI64;
use core::num::NonZeroIsize;
use core::num::NonZeroU8;
use core::num::NonZeroU16;
use core::num::NonZeroU32;
use core::num::NonZeroU64;
use core::num::NonZeroUsize;
use crate::hash::backend::HashU8;
use crate::hash::backend::HashU16;
use crate::hash::backend::HashU32;
use crate::hash::backend::HashU64;

/// A sealed trait for hashable keys representable as non-zero integers. The
/// only way to implement this trait for additional types is to implement the
/// [`IntoKey`] trait.
///
/// Types that implement this trait will usually be `Copy`, though that is not
/// strictly required.
#[allow(private_bounds)]
pub trait Key: private::Key {
}

impl<T: IntoKey> Key for T {
}

macro_rules! key_impls {
  ($($nzint:ty => $uint:ty, $hash:ty;)*) => {
    $(
      impl Key for $nzint {
      }

      unsafe impl private::Key for $nzint {
        #![allow(trivial_numeric_casts)]

        type UInt = $uint;

        type Hash = $hash;

        #[inline(always)]
        fn into_uint(x: Self) -> Self::UInt {
          x.get() as _
        }

        #[inline(always)]
        unsafe fn from_uint(x: Self::UInt) -> Self {
          unsafe { Self::new_unchecked(x as _) }
        }
      }
    )*
  };
}

key_impls! {
  NonZeroI8 => u8, HashU8;
  NonZeroI16 => u16, HashU16;
  NonZeroI32 => u32, HashU32;
  NonZeroI64 => u64, HashU64;
  NonZeroU8 => u8, HashU8;
  NonZeroU16 => u16, HashU16;
  NonZeroU32 => u32, HashU32;
  NonZeroU64 => u64, HashU64;
}

cfg_select! {
  target_pointer_width = "32" => {
    key_impls! {
      NonZeroIsize => u32, HashU32;
      NonZeroUsize => u32, HashU32;
    }
  }
  target_pointer_width = "64" => {
    key_impls! {
      NonZeroIsize => u64, HashU64;
      NonZeroUsize => u64, HashU64;
    }
  }
  _ => {
  }
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
  /// A codomain key type.
  type Key: Key;

  /// An injective transformation.
  fn into_key(_: Self) -> Self::Key;

  /// The inverse of `into_key`.
  unsafe fn from_key(_: Self::Key) -> Self;
}

unsafe impl<T: IntoKey> private::Key for T {
  type UInt = <T::Key as private::Key>::UInt;

  type Hash = <T::Key as private::Key>::Hash;

  #[inline(always)]
  fn into_uint(x: Self) -> Self::UInt {
    <T::Key as private::Key>::into_uint(T::into_key(x))
  }

  #[inline(always)]
  unsafe fn from_uint(x: Self::UInt) -> Self {
    unsafe { T::from_key(<T::Key as private::Key>::from_uint(x)) }
  }
}

pub(crate) mod private {
  use crate::uint::UInt;
  use crate::hash::Hash;

  pub(crate) unsafe trait Key: Sized {
    type UInt: UInt;

    type Hash: Hash<Self::UInt>;

    fn into_uint(_: Self) -> Self::UInt;

    unsafe fn from_uint(_: Self::UInt) -> Self;
  }
}
