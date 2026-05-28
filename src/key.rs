//! This module provides traits for hashable keys representable as non-zero
//! integers.

use core::num::NonZeroU8;
use core::num::NonZeroU32;
use core::num::NonZeroU64;
use crate::hash::backend::HashU8;
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

impl Key for NonZeroU8 {
}

impl Key for NonZeroU32 {
}

impl Key for NonZeroU64 {
}

impl<T: IntoKey> Key for T {
}

/// A trait for representing keys as non-zero integers.
///
/// For logical correctness, the key ought to be in some sense "the same" after
/// a round trip.
///
/// # Safety
///
/// It must be sound to `retract` the result of any `inject`, possibly multiple
/// times, e.g.
///
/// ```text
/// let y = T::inject(x);
/// let ... = unsafe { T::retract(y) };
/// let ... = unsafe { T::retract(y) };
/// ```
pub unsafe trait IntoKey {
  /// A codomain key type.
  type Key: Key;

  /// An injective transformation.
  fn inject(_: Self) -> Self::Key;

  /// The inverse of `inject`.
  unsafe fn retract(_: Self::Key) -> Self;
}

unsafe impl<K: private::Key, T: IntoKey<Key = K>> private::Key for T {
  type UInt = K::UInt;

  type Hash = K::Hash;

  #[inline(always)]
  fn into_uint(x: Self) -> Self::UInt {
    K::into_uint(T::inject(x))
  }

  #[inline(always)]
  unsafe fn from_uint(x: Self::UInt) -> Self {
    unsafe { T::retract(K::from_uint(x)) }
  }
}

macro_rules! key_impls {
  ($($nzuint:ty => $uint:ty, $hash:ty;)*) => {
    $(
      unsafe impl private::Key for $nzuint {
        type UInt = $uint;

        type Hash = $hash;

        #[inline(always)]
        fn into_uint(x: Self) -> Self::UInt {
          x.get()
        }

        #[inline(always)]
        unsafe fn from_uint(x: Self::UInt) -> Self {
          unsafe { Self::new_unchecked(x) }
        }
      }
    )*
  };
}

key_impls! {
  NonZeroU8 => u8, HashU8;
  NonZeroU32 => u32, HashU32;
  NonZeroU64 => u64, HashU64;
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
