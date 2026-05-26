use rand_core::Rng;
use crate::hash::internal::Backend;
use crate::hash::Hash;
use crate::util::invert_u32;
use crate::util::invert_u64;

pub(crate) const BACKEND: Backend = Backend::Generic;

unsafe impl Hash for u32 {
  type Seed = ((u32, u32), (u32, u32));

  type Seed0 = (u32, u32);

  type Seed1 = (u32, u32);

  #[inline(always)]
  fn seed0(seed: &Self::Seed) -> Self::Seed0 {
    seed.0
  }

  #[inline(always)]
  fn seed1(seed: &Self::Seed) -> Self::Seed1 {
    seed.1
  }

  #[inline(always)]
  fn seed_nondet() -> Self::Seed {
    let n = dandelion::thread_local::u64();
    let a = 1 | (n as u32);
    let b = 1 | ((n >> 32) as u32);
    let x = invert_u32(a.wrapping_mul(b));
    let c = x.wrapping_mul(a);
    let d = x.wrapping_mul(b);
    ((a, b), (c, d))
  }

  #[inline(always)]
  fn seed(g: &mut impl Rng) -> Self::Seed {
    let n = g.next_u64();
    let a = 1 | (n as u32);
    let b = 1 | ((n >> 32) as u32);
    let x = invert_u32(a.wrapping_mul(b));
    let c = x.wrapping_mul(a);
    let d = x.wrapping_mul(b);
    ((a, b), (c, d))
  }

  #[inline(always)]
  fn hash(x: Self, m: Self::Seed0) -> Self {
    let a = m.0;
    let b = m.1;
    let x = x ^ x.rotate_left(7) ^ x.rotate_left(23);
    let x = x.wrapping_mul(a);
    let x = x.swap_bytes();
    let x = x.wrapping_mul(b).wrapping_sub(1);
    x
  }

  #[inline(always)]
  fn invert_hash(x: Self, m: Self::Seed0) -> Self {
    let a = m.0;
    let b = m.1;
    let x = x.wrapping_mul(a).wrapping_add(a);
    let x = x.swap_bytes();
    let x = x.wrapping_mul(b);
    let x = x ^ x.rotate_left(7) ^ x.rotate_left(23);
    x
  }
}

unsafe impl Hash for u64 {
  type Seed = ((u64, u64), (u64, u64));

  type Seed0 = (u64, u64);

  type Seed1 = (u64, u64);

  #[inline(always)]
  fn seed0(seed: &Self::Seed) -> Self::Seed0 {
    seed.0
  }

  #[inline(always)]
  fn seed1(seed: &Self::Seed) -> Self::Seed1 {
    seed.1
  }

  #[inline(always)]
  fn seed_nondet() -> Self::Seed {
    let n = dandelion::thread_local::u128();
    let a = 1 | (n as u64);
    let b = 1 | ((n >> 64) as u64);
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
    let x = x ^ x.rotate_left(17) ^ x.rotate_left(49);
    let x = x.wrapping_mul(a);
    let x = x.swap_bytes();
    let x = x.wrapping_mul(b).wrapping_sub(1);
    x
  }

  #[inline(always)]
  fn invert_hash(x: Self, m: Self::Seed1) -> Self {
    let c = m.0;
    let d = m.1;
    let x = x.wrapping_mul(c).wrapping_add(c);
    let x = x.swap_bytes();
    let x = x.wrapping_mul(d);
    let x = x ^ x.rotate_left(17) ^ x.rotate_left(49);
    x
  }
}
