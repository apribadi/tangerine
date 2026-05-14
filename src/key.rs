//! This module provides traits for hashable keys representable as [`NonZeroU32`]
//! or [`NonZeroU64`].

use core::cfg_select;
use core::num::NonZeroU32;
use core::num::NonZeroU64;
use rand_core::Rng;

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

#[allow(dead_code)]
#[inline(always)]
fn invert_u32(a: u32) -> u32 {
  // https://jeffhurchalla.com/2022/04/25/a-faster-multiplicative-inverse-mod-a-power-of-2/
  let x = a.wrapping_mul(3) ^ 2;
  let y = 1u32.wrapping_sub(a.wrapping_mul(x));
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  x
}

#[allow(dead_code)]
#[inline(always)]
fn invert_u64(a: u64) -> u64 {
  // https://arxiv.org/abs/2204.04342
  let x = a.wrapping_mul(3) ^ 2;
  let y = 1u64.wrapping_sub(a.wrapping_mul(x));
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  x
}

cfg_select! {
  all(target_arch = "aarch64", target_feature = "crc") => {
    #[inline(always)]
    fn crc32cw(a: u32, x: u32) -> u32 {
      unsafe { core::arch::aarch64::__crc32cw(a, x) }
    }

    #[inline(always)]
    fn crc32cd(a: u32, x: u64) -> u32 {
      unsafe { core::arch::aarch64::__crc32cd(a, x) }
    }

    #[inline(always)]
    fn vmull_p64(x: u64, y: u64) -> u128 {
      // NOTE: not supported by Miri
      unsafe { core::arch::aarch64::vmull_p64(x, y) }
    }

    unsafe impl private::Hash for u32 {
      type Seed = (u32, u32);

      type Seed0 = u32;

      type Seed1 = u32;

      #[inline(always)]
      fn seed0(m: Self::Seed) -> Self::Seed0 {
        m.0
      }

      #[inline(always)]
      fn seed1(m: Self::Seed) -> Self::Seed1 {
        m.1
      }

      #[inline(always)]
      fn seed_nondet() -> Self::Seed {
        let a = 1 | dandelion::thread_local::u32();
        let b = invert_u32(a);
        (a, b)
      }

      #[inline(always)]
      fn seed(g: &mut impl Rng) -> Self::Seed {
        let a = 1 | g.next_u32();
        let b = invert_u32(a);
        (a, b)
      }

      #[inline(always)]
      fn hash(x: Self, m: Self::Seed0) -> Self {
        crc32cw(0, x).wrapping_mul(m)
      }

      #[inline(always)]
      fn invert_hash(x: Self, m: Self::Seed1) -> Self {
        crc32cd(0, vmull_p64(x.wrapping_mul(m) as u64, 0xc915_ea3b) as u64)
      }
    }
  }
  _ => {
    unsafe impl private::Hash for u32 {
      type Seed = ((u32, u32), (u32, u32));

      type Seed0 = (u32, u32);

      type Seed1 = (u32, u32);

      #[inline(always)]
      fn seed0(m: Self::Seed) -> Self::Seed0 {
        m.0
      }

      #[inline(always)]
      fn seed1(m: Self::Seed) -> Self::Seed1 {
        m.1
      }

      #[inline(always)]
      fn seed_nondet() -> Self::Seed {
        let n = dandelion::thread_local::u64();
        let a = 1 | (n as u32);
        let b = 1 | (n >> 32) as u32;
        let x = invert_u32(a.wrapping_mul(b));
        let c = x.wrapping_mul(a);
        let d = x.wrapping_mul(b);
        ((a, b), (c, d))
      }

      #[inline(always)]
      fn seed(g: &mut impl Rng) -> Self::Seed {
        let n = g.next_u64();
        let a = 1 | (n as u32);
        let b = 1 | (n >> 32) as u32;
        let x = invert_u32(a.wrapping_mul(b));
        let c = x.wrapping_mul(a);
        let d = x.wrapping_mul(b);
        ((a, b), (c, d))
      }

      #[inline(always)]
      fn hash(x: Self, m: Self::Seed0) -> Self {
        let a = m.0;
        let b = m.1;
        let x = x.wrapping_mul(a);
        let x = x.swap_bytes();
        let x = x.wrapping_mul(b);
        x
      }

      #[inline(always)]
      fn invert_hash(x: Self, m: Self::Seed1) -> Self {
        let a = m.0;
        let b = m.1;
        let x = x.wrapping_mul(a);
        let x = x.swap_bytes();
        let x = x.wrapping_mul(b);
        x
      }
    }
  }
}

unsafe impl private::Hash for u64 {
  type Seed = ((u64, u64), (u64, u64));

  type Seed0 = (u64, u64);

  type Seed1 = (u64, u64);

  #[inline(always)]
  fn seed0(m: Self::Seed) -> Self::Seed0 {
    m.0
  }

  #[inline(always)]
  fn seed1(m: Self::Seed) -> Self::Seed1 {
    m.1
  }

  #[inline(always)]
  fn seed_nondet() -> Self::Seed {
    let n = dandelion::thread_local::u128();
    let a = 1 | (n as u64);
    let b = 1 | (n >> 64) as u64;
    let x = invert_u64(a.wrapping_mul(b));
    let c = x.wrapping_mul(a);
    let d = x.wrapping_mul(b);
    ((a, b), (c, d))
  }

  #[inline(always)]
  fn seed(g: &mut impl Rng) -> Self::Seed {
    let a = 1 | g.next_u64();
    let b = 1 | g.next_u64();
    let x = invert_u64(a.wrapping_mul(b));
    let c = x.wrapping_mul(a);
    let d = x.wrapping_mul(b);
    ((a, b), (c, d))
  }

  #[inline(always)]
  fn hash(x: Self, m: Self::Seed0) -> Self {
    let a = m.0;
    let b = m.1;
    let x = x.wrapping_mul(a);
    let x = x.swap_bytes();
    let x = x.wrapping_mul(b);
    x
  }

  #[inline(always)]
  fn invert_hash(x: Self, m: Self::Seed1) -> Self {
    let a = m.0;
    let b = m.1;
    let x = x.wrapping_mul(a);
    let x = x.swap_bytes();
    let x = x.wrapping_mul(b);
    x
  }
}

unsafe impl private::Word for u32 {
  const BITS: usize = 32;

  const ZERO: Self = 0;

  #[inline(always)]
  fn asr(x: Self, s: usize) -> Self {
    ((x as i32) >> s) as u32
  }

  #[inline(always)]
  fn into_usize(self) -> usize {
    self as usize
  }
}

unsafe impl private::Word for u64 {
  const BITS: usize = 64;

  const ZERO: Self = 0;

  #[inline(always)]
  fn asr(x: Self, s: usize) -> Self {
    ((x as i64) >> s) as u64
  }

  #[inline(always)]
  fn into_usize(self) -> usize {
    self as usize
  }
}

pub(crate) mod private {
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

  pub(crate) unsafe trait Hash {
    type Seed: Copy;

    type Seed0: Copy;

    type Seed1: Copy;

    fn seed0(_: Self::Seed) -> Self::Seed0;

    fn seed1(_: Self::Seed) -> Self::Seed1;

    fn seed_nondet() -> Self::Seed;

    fn seed(_: &mut impl rand_core::Rng) -> Self::Seed;

    fn hash(_: Self, _: Self::Seed0) -> Self;

    fn invert_hash(_: Self, _: Self::Seed1) -> Self;
  }

  pub(crate) unsafe trait Word:
    Copy
    + Ord
    + core::ops::Add<Self, Output = Self>
    + core::ops::BitOr<Self, Output = Self>
    + core::ops::Not<Output = Self>
    + core::ops::Shr<usize, Output = Self>
  {
    const BITS: usize;

    const ZERO: Self;

    fn asr(_: Self, _: usize) -> Self;

    fn into_usize(self) -> usize;
  }
}

pub mod internal {
  //! Unstable API exposing implementation details for benchmarks and tests.

  #![allow(missing_docs)]

  use super::Rng;
  use super::private::Hash;

  #[derive(Clone, Copy)]
  pub struct Seed32(<u32 as Hash>::Seed0);

  pub fn seed32(g: &mut impl Rng) -> Seed32 {
    Seed32(<u32 as Hash>::seed0(<u32 as Hash>::seed(g)))
  }

  pub fn hash32(x: u32, m: Seed32) -> u32 {
    <u32 as Hash>::hash(x, m.0)
  }
}
