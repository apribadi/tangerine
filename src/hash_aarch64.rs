use rand_core::Rng;
use crate::key::private::Hash;
use crate::util::invert_u32;

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
  // NOTE: not currently supported by Miri
  unsafe { core::arch::aarch64::vmull_p64(x, y) }
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
    let x = crc32cw(0, x);
    let x = x.wrapping_mul(m);
    x
  }

  #[inline(always)]
  fn invert_hash(x: Self, m: Self::Seed1) -> Self {
    let x = x.wrapping_mul(m);
    let x = crc32cd(0, vmull_p64(x as u64, 0xc915_ea3b) as u64);
    x
  }
}
