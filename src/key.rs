//! This module provides traits for hashable keys representable as [`NonZeroU32`]
//! or [`NonZeroU64`].

use core::num::NonZeroU32;
use core::num::NonZeroU64;
use rand_core::RngCore;

/// A sealed trait for hashable keys representable as [`NonZeroU32`] or
/// [`NonZeroU64`]. The only way to implement this trait for additional types is
/// to implement the [`IntoKey`] trait.
#[allow(private_bounds)]
pub trait Key: private::Key {
}

impl Key for NonZeroU32 {
}

impl Key for NonZeroU64 {
}

impl<T: IntoKey + Copy + Ord> Key for T {
}

/// A trait for representing keys as [`NonZeroU32`] or [`NonZeroU64`].
///
/// For logical correctness, the key ought to be in some sense "the same" after
/// a round trip.
///
/// # Safety
///
/// It must be safe to `project` the result of any `inject`, possibly
/// multiple times, e.g.
///
/// ```text
/// let y = inject(x);
/// let _ = unsafe { project(y) };
/// let _ = unsafe { project(y) };
/// ```
pub unsafe trait IntoKey {
  #![allow(missing_docs)]

  type Key: Key;

  fn inject(_: Self) -> Self::Key;

  unsafe fn project(_: Self::Key) -> Self;
}

static EMPTY_TABLE_U32: [u32; 3] = [0u32; 3];

static EMPTY_TABLE_U64: [u64; 3] = [0u64; 3];

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

  #[inline(always)]
  fn seed_nondet() -> (Self::Word, Self::Word) {
    let n = dandelion::thread_local::u64();
    let a = n as u32;
    let b = (n >> 32) as u32;
    (a | 1, b | 1)
  }

  #[inline(always)]
  fn seed(g: &mut impl RngCore) -> (Self::Word, Self::Word) {
    let n = g.next_u64();
    let a = n as u32;
    let b = (n >> 32) as u32;
    (a | 1, b | 1)
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

  #[inline(always)]
  fn seed_nondet() -> (Self::Word, Self::Word) {
    let n = dandelion::thread_local::u128();
    let a = n as u64;
    let b = (n >> 64) as u64;
    (a | 1, b | 1)
  }

  #[inline(always)]
  fn seed(g: &mut impl RngCore) -> (Self::Word, Self::Word) {
    let a = g.next_u64();
    let b = g.next_u64();
    (a | 1, b | 1)
  }
}

unsafe impl<T: IntoKey + Copy + Ord> private::Key for T {
  type Word = <T::Key as private::Key>::Word;

  #[inline(always)]
  fn into_word(x: Self) -> Self::Word {
    <T::Key as private::Key>::into_word(T::inject(x))
  }

  #[inline(always)]
  unsafe fn from_word(x: Self::Word) -> Self {
    unsafe { T::project(<T::Key as private::Key>::from_word(x)) }
  }

  #[inline(always)]
  fn seed_nondet() -> (Self::Word, Self::Word) {
    <T::Key as private::Key>::seed_nondet()
  }

  #[inline(always)]
  fn seed(g: &mut impl RngCore) -> (Self::Word, Self::Word) {
    <T::Key as private::Key>::seed(g)
  }
}

impl private::Word for u32 {
  const BITS: usize = 32;

  const ZERO: Self = 0;

  const ONE: Self = 1;

  const EMPTY_TABLE: *const Self = &raw const EMPTY_TABLE_U32 as *const Self;

  #[inline(always)]
  fn into_usize(self) -> usize {
    self as usize
  }

  #[inline(always)]
  fn asr(x: Self, s: usize) -> Self {
    ((x as i32) >> s) as u32
  }

  #[inline(always)]
  fn swap_bytes(self) -> Self {
    self.swap_bytes()
  }

  #[inline(always)]
  fn wrapping_mul(self, y: Self) -> Self {
    self.wrapping_mul(y)
  }

  #[inline(always)]
  fn invert(a: u32) -> u32 {
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
}

impl private::Word for u64 {
  const BITS: usize = 64;

  const ZERO: Self = 0;

  const ONE: Self = 1;

  const EMPTY_TABLE: *const Self = &raw const EMPTY_TABLE_U64 as *const Self;

  #[inline(always)]
  fn into_usize(self) -> usize {
    self as usize
  }

  #[inline(always)]
  fn asr(x: Self, s: usize) -> Self {
    ((x as i64) >> s) as u64
  }

  #[inline(always)]
  fn swap_bytes(self) -> Self {
    self.swap_bytes()
  }

  #[inline(always)]
  fn wrapping_mul(self, y: Self) -> Self {
    self.wrapping_mul(y)
  }

  #[inline(always)]
  fn invert(a: u64) -> u64 {
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
}

pub(crate) mod private {
  pub(crate) unsafe trait Key: Copy + Ord {
    type Word: Word;

    const BITS: usize = Self::Word::BITS;

    const ZERO: Self::Word = Self::Word::ZERO;

    const EMPTY_TABLE: *const Self::Word = Self::Word::EMPTY_TABLE;

    fn into_word(_: Self) -> Self::Word;

    unsafe fn from_word(_: Self::Word) -> Self;

    fn seed_nondet() -> (Self::Word, Self::Word);

    fn seed(_: &mut impl rand_core::RngCore) -> (Self::Word, Self::Word);
  }

  pub(crate) trait Word:
    Copy
    + Ord
    + core::ops::Add<Self, Output = Self>
    + core::ops::BitOr<Self, Output = Self>
    + core::ops::Not<Output = Self>
    + core::ops::Shr<usize, Output = Self>
  {
    const BITS: usize;

    const ZERO: Self;

    const ONE: Self;

    const EMPTY_TABLE: *const Self;

    fn into_usize(self) -> usize;

    fn swap_bytes(self) -> Self;

    fn wrapping_mul(self, _: Self) -> Self;

    fn asr(_: Self, _: usize) -> Self;

    fn invert(_: Self) -> Self;
  }
}
