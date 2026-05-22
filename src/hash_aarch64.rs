use rand_core::Rng;

use crate::hash::Hash;
use crate::util::invert_u32;
use crate::util::invert_u64;

#[inline(always)]
fn crc32cw(a: u32, x: u32) -> u32 {
  unsafe { core::arch::aarch64::__crc32cw(a, x) }
}

#[inline(always)]
fn crc32cd(a: u32, x: u64) -> u32 {
  unsafe { core::arch::aarch64::__crc32cd(a, x) }
}

#[inline(always)]
fn widening_carryless_mul_u32(x: u32, y: u32) -> u64 {
  #[cfg(not(miri))]
  unsafe { core::arch::aarch64::vmull_p64(x as u64, y as u64) as u64 }
  #[cfg(miri)]
  x.widening_carryless_mul(y)
}

#[inline(always)]
fn invert_crc32cw(x: u32) -> u32 {
  // a ^ x == invert_crc32cw(crc32cw(a, x))
  crc32cd(0, widening_carryless_mul_u32(x, 0xc915_ea3b))
}

unsafe impl Hash for u32 {
  type Seed = (u32, u32);

  type Seed0 = u32;

  type Seed1 = u32;

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
    let x = crc32cw(0, x);
    let x = x.wrapping_mul(m).wrapping_sub(1);
    x
  }

  #[inline(always)]
  fn invert_hash(x: Self, m: Self::Seed1) -> Self {
    let x = x.wrapping_mul(m).wrapping_add(m);
    let x = invert_crc32cw(x);
    x
  }
}

unsafe impl Hash for u64 {
  type Seed = (u64, u64);

  type Seed0 = u64;

  type Seed1 = u64;

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
    let a = 1 | dandelion::thread_local::u64();
    let b = invert_u64(a);
    (a, b)
  }

  #[inline(always)]
  fn seed(g: &mut impl Rng) -> Self::Seed {
    let a = 1 | g.next_u64();
    let b = invert_u64(a);
    (a, b)
  }

  #[inline(always)]
  fn hash(x: Self, m: Self::Seed0) -> Self {
    let x = (x as u32 as u64) ^ ((crc32cd(0, x) as u64) << 32);
    let x = x.wrapping_mul(m).wrapping_sub(1);
    x
  }

  #[inline(always)]
  fn invert_hash(x: Self, m: Self::Seed1) -> Self {
    let x = x.wrapping_mul(m).wrapping_add(m);
    let u = x as u32;
    let v = invert_crc32cw((x >> 32) as u32) ^ crc32cw(0, u);
    (u as u64) ^ ((v as u64) << 32)
  }
}
