use rand_core::Rng;

use crate::private_trait::Hash;
use crate::util::invert_u32;
use crate::util::invert_u64;

#[inline(always)]
fn crc32c_u32(a: u32, x: u32) -> u32 {
  unsafe { core::arch::aarch64::__crc32cw(a, x) }
}

#[inline(always)]
fn crc32c_u64(a: u32, x: u64) -> u32 {
  unsafe { core::arch::aarch64::__crc32cd(a, x) }
}

#[inline(always)]
fn widening_carryless_mul_u32(x: u32, y: u32) -> u64 {
  #[cfg(not(miri))]
  unsafe { core::arch::aarch64::vmull_p64(x as u64, y as u64) as u64 }
  #[cfg(miri)]
  x.widening_carryless_mul(y)
}

unsafe impl Hash for u32 {
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
    let x = crc32c_u32(0, x);
    let x = x.wrapping_mul(m).wrapping_sub(1);
    x
  }

  #[inline(always)]
  fn invert_hash(x: Self, m: Self::Seed1) -> Self {
    let x = x.wrapping_mul(m).wrapping_add(m);
    let x = crc32c_u64(0, widening_carryless_mul_u32(x, 0xc915_ea3b));
    x
  }
}

unsafe impl Hash for u64 {
  type Seed = (u64, u64);

  type Seed0 = u64;

  type Seed1 = u64;

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
    let a = x as u32;
    let b = crc32c_u64(0, x);
    let x = (a as u64) ^ ((b as u64) << 32);
    let x = x.wrapping_mul(m);
    let x = x.wrapping_sub(1);
    x
  }

  #[inline(always)]
  fn invert_hash(x: Self, m: Self::Seed1) -> Self {
    // TODO: invert
    let _ = x;
    let _ = m;
    unimplemented!()
  }
}
