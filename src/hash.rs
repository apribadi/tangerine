use rand_core::Rng;

use crate::util::invert_u64;

pub(crate) unsafe trait Hash {
  type Seed: Copy;

  type Seed0: Copy;

  type Seed1: Copy;

  fn seed0(_: Self::Seed) -> Self::Seed0;

  fn seed1(_: Self::Seed) -> Self::Seed1;

  fn seed_nondet() -> Self::Seed;

  fn seed(_: &mut impl Rng) -> Self::Seed;

  fn hash(_: Self, _: Self::Seed0) -> Self;

  fn invert_hash(_: Self, _: Self::Seed1) -> Self;
}

unsafe impl Hash for u64 {
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
