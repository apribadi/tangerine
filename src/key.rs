use core::num::NonZeroU32;
use core::num::NonZeroU64;
use rand_core::RngCore;

/// A sealed trait for hash map keys.
///
/// It is implemented by `NonZeroU32` and `NonZeroU64`, and by a type that can
/// be represented by one of those.

pub trait Key: private::Key {
}

impl Key for NonZeroU32 {
}

impl Key for NonZeroU64 {
}

impl<T: IntoKey> Key for T {
}

pub unsafe trait IntoKey {
  //! SAFETY: It must be safe to do `project(inject(_))`.
  //!
  //! For logical correctness, the key ought to be in some sense "the same"
  //! after a round trip, but that is not required for safety.

  type Key: Key;

  fn inject(_: Self) -> Self::Key;

  unsafe fn project(_: Self::Key) -> Self;
}

#[inline(always)]
fn umulh(x: u64, y: u64) -> u64 {
  return ((x as u128 * y as u128) >> 64) as u64;
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
  fn hash(k: Self, (a, b): Self::Seed) -> Self::Hash {
    let h = k.get();
    let h = h.wrapping_mul(a);
    let h = h.swap_bytes();
    let h = h.wrapping_mul(b);
    return h;
  }

  #[inline(always)]
  fn slot(h: Self::Hash, w: usize) -> usize {
    return umulh((h as u64) << 32, w as u64) as usize;
  }
}

unsafe impl private::Key for NonZeroU64 {
  type Seed = (u64, u64);

  type Hash = u64;

  const ZERO: Self::Hash = 0;

  #[inline(always)]
  fn seed_nondet() -> Self::Seed {
    let n = u128::from_le_bytes(dandelion::thread_local::byte_array());
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
  fn hash(k: Self, (a, b): Self::Seed) -> Self::Hash {
    let h = k.get();
    let h = h.wrapping_mul(a);
    let h = h.swap_bytes();
    let h = h.wrapping_mul(b);
    return h;
  }

  #[inline(always)]
  fn slot(h: Self::Hash, w: usize) -> usize {
    return umulh(h, w as u64) as usize;
  }
}

unsafe impl<T: IntoKey> private::Key for T {
  type Seed = <T::Key as private::Key>::Seed;

  type Hash = <T::Key as private::Key>::Hash;

  const ZERO: Self::Hash = <T::Key as private::Key>::ZERO;

  #[inline(always)]
  fn seed_nondet() -> Self::Seed {
    <T::Key as private::Key>::seed_nondet()
  }

  #[inline(always)]
  fn seed(g: &mut impl RngCore) -> Self::Seed {
    <T::Key as private::Key>::seed(g)
  }

  #[inline(always)]
  fn hash(k: Self, m: Self::Seed) -> Self::Hash {
    <T::Key as private::Key>::hash(T::inject(k), m)
  }

  #[inline(always)]
  fn slot(h: Self::Hash, w: usize) -> usize {
    <T::Key as private::Key>::slot(h, w)
  }
}

pub(crate) mod private {
  use rand_core::RngCore;

  pub(crate) unsafe trait Key {
    type Seed: Copy;

    type Hash: Copy + Ord;

    const ZERO: Self::Hash;

    fn seed_nondet() -> Self::Seed;

    fn seed(g: &mut impl RngCore) -> Self::Seed;

    fn hash(k: Self, m: Self::Seed) -> Self::Hash;

    fn slot(h: Self::Hash, w: usize) -> usize;
  }
}
