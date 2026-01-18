//! This module provides traits for hashable keys representable as `NonZeroU32`
//! or `NonZeroU64`.

use core::num::NonZeroU32;
use core::num::NonZeroU64;
use rand_core::RngCore;

/// A sealed trait for hashable keys representable as `NonZeroU32` or
/// `NonZeroU64`.

#[allow(private_bounds)]
pub trait Key: private::Key {
}

impl Key for NonZeroU32 {
}

impl Key for NonZeroU64 {
}

impl<T: IntoKey> Key for T {
}

/// A trait for representing keys as `NonZeroU32` or `NonZeroU64`.
///
/// For logical correctness, the key ought to be in some sense "the same" after
/// a round trip.
///
/// SAFETY: It must be safe to do `project(inject(_))`.

pub unsafe trait IntoKey: Copy + Ord {
  #![allow(missing_docs)]

  type Key: Key;

  fn inject(_: Self) -> Self::Key;

  unsafe fn project(_: Self::Key) -> Self;
}

#[inline(always)]
fn umulh(x: u64, y: u64) -> u64 {
  return ((x as u128 * y as u128) >> 64) as u64;
}

#[inline(always)]
fn invert32(a: u32) -> u32 {
  // https://jeffhurchalla.com/2022/04/25/a-faster-multiplicative-inverse-mod-a-power-of-2/

  let x = a.wrapping_mul(3) ^ 2;
  let y = 1u32.wrapping_sub(a.wrapping_mul(x));
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  return x;
}

#[inline(always)]
fn invert64(a: u64) -> u64 {
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
  return x;
}

unsafe impl private::Key for NonZeroU32 {
  type Seed = (u32, u32);

  type Hash = u32;

  const ZERO: Self::Hash = 0;

  #[inline(always)]
  fn seed_nondet() -> Self::Seed {
    let n = dandelion::thread_local::u64();
    let a = n as u32;
    let b = (n >> 32) as u32;
    return (a | 1, b | 1);
  }

  #[inline(always)]
  fn seed(g: &mut impl RngCore) -> Self::Seed {
    let n = g.next_u64();
    let a = n as u32;
    let b = (n >> 32) as u32;
    return (a | 1, b | 1);
  }

  #[inline(always)]
  fn invert_seed(m: Self::Seed) -> Self::Seed {
    let a = m.0;
    let b = m.1;
    let c = invert32(a.wrapping_mul(b));
    return (c.wrapping_mul(a), c.wrapping_mul(b));
  }

  #[inline(always)]
  fn hash(k: Self, (a, b): Self::Seed) -> Self::Hash {
    let h = k.get();
    let h = h.wrapping_mul(a);
    let h = h.swap_bytes();
    let h = h.wrapping_mul(b);
    return h;
  }

  #[inline(always)]
  unsafe fn invert_hash(h: Self::Hash, (a, b): Self::Seed) -> Self {
    let h = h.wrapping_mul(a);
    let h = h.swap_bytes();
    let h = h.wrapping_mul(b);
    return unsafe { NonZeroU32::new_unchecked(h) };
  }

  #[inline(always)]
  fn slot(h: Self::Hash, w: usize) -> usize {
    // NB: We will run out of memory before `w as u64` truncates on a
    // hypothetical 128-bit machine.
    return umulh((h as u64) << 32, w as u64) as usize;
  }
}

unsafe impl private::Key for NonZeroU64 {
  type Seed = (u64, u64);

  type Hash = u64;

  const ZERO: Self::Hash = 0;

  #[inline(always)]
  fn seed_nondet() -> Self::Seed {
    let n = dandelion::thread_local::u128();
    let a = n as u64;
    let b = (n >> 64) as u64;
    return (a | 1, b | 1);
  }

  #[inline(always)]
  fn seed(g: &mut impl RngCore) -> Self::Seed {
    let a = g.next_u64();
    let b = g.next_u64();
    return (a | 1, b | 1);
  }

  #[inline(always)]
  fn invert_seed(m: Self::Seed) -> Self::Seed {
    let a = m.0;
    let b = m.1;
    let c = invert64(a.wrapping_mul(b));
    return (c.wrapping_mul(a), c.wrapping_mul(b));
  }

  #[inline(always)]
  fn hash(k: Self, (a, b): Self::Seed) -> Self::Hash {
    let h = k.get();
    let h = h.wrapping_mul(a);
    let h = h.swap_bytes();
    let h = h.wrapping_mul(b);
    return h;
  }

  #[inline(always)]
  unsafe fn invert_hash(h: Self::Hash, (a, b): Self::Seed) -> Self {
    let h = h.wrapping_mul(a);
    let h = h.swap_bytes();
    let h = h.wrapping_mul(b);
    return unsafe { NonZeroU64::new_unchecked(h) };
  }

  #[inline(always)]
  fn slot(h: Self::Hash, w: usize) -> usize {
    // NB: We will run out of memory before `w as u64` truncates on a
    // hypothetical 128-bit machine.
    return umulh(h, w as u64) as usize;
  }
}

unsafe impl<T: IntoKey> private::Key for T {
  type Seed = <T::Key as private::Key>::Seed;

  type Hash = <T::Key as private::Key>::Hash;

  const ZERO: Self::Hash = <T::Key as private::Key>::ZERO;

  #[inline(always)]
  fn seed_nondet() -> Self::Seed {
    return <T::Key as private::Key>::seed_nondet();
  }

  #[inline(always)]
  fn seed(g: &mut impl RngCore) -> Self::Seed {
    return <T::Key as private::Key>::seed(g);
  }

  #[inline(always)]
  fn invert_seed(m: Self::Seed) -> Self::Seed {
    return <T::Key as private::Key>::invert_seed(m);
  }

  #[inline(always)]
  fn hash(k: Self, m: Self::Seed) -> Self::Hash {
    return <T::Key as private::Key>::hash(T::inject(k), m);
  }

  #[inline(always)]
  unsafe fn invert_hash(h: Self::Hash, m: Self::Seed) -> T {
    return unsafe { T::project(<T::Key as private::Key>::invert_hash(h, m)) };
  }

  #[inline(always)]
  fn slot(h: Self::Hash, w: usize) -> usize {
    return <T::Key as private::Key>::slot(h, w);
  }
}

pub(crate) mod private {
  use rand_core::RngCore;

  pub(crate) unsafe trait Key: Copy + Ord {
    type Seed: Copy;

    type Hash: Copy + Ord;

    const ZERO: Self::Hash;

    fn seed_nondet() -> Self::Seed;

    fn seed(_: &mut impl RngCore) -> Self::Seed;

    fn invert_seed(_: Self::Seed) -> Self::Seed;

    fn hash(_: Self, _: Self::Seed) -> Self::Hash;

    unsafe fn invert_hash(_: Self::Hash, _: Self::Seed) -> Self;

    fn slot(_: Self::Hash, _: usize) -> usize;
  }
}
