#![allow(missing_docs)]

use rand_core::Rng;

pub(crate) unsafe trait Hash {
  type Seed;

  type Seed0: Copy;

  type Seed1: Copy;

  fn seed0(_: &Self::Seed) -> Self::Seed0;

  fn seed1(_: &Self::Seed) -> Self::Seed1;

  fn seed_nondet() -> Self::Seed;

  fn seed(_: &mut impl Rng) -> Self::Seed;

  fn hash(_: Self, _: Self::Seed0) -> Self;

  fn invert_hash(_: Self, _: Self::Seed1) -> Self;
}

pub mod internal {
  use super::Hash;
  use super::Rng;

  pub struct Hash32(<u32 as Hash>::Seed);

  impl Hash32 {
    pub fn new(g: &mut impl Rng) -> Self {
      Self(<u32 as Hash>::seed(g))
    }

    pub fn hash(&self, x: u32) -> u32 {
      <u32 as Hash>::hash(x, <u32 as Hash>::seed0(&self.0))
    }

    pub fn invert_hash(&self, x: u32) -> u32 {
      <u32 as Hash>::invert_hash(x, <u32 as Hash>::seed1(&self.0))
    }
  }

  pub struct Hash64(<u64 as Hash>::Seed);

  impl Hash64 {
    pub fn new(g: &mut impl Rng) -> Self {
      Self(<u64 as Hash>::seed(g))
    }

    pub fn hash(&self, x: u64) -> u64 {
      <u64 as Hash>::hash(x, <u64 as Hash>::seed0(&self.0))
    }

    pub fn invert_hash(&self, x: u64) -> u64 {
      <u64 as Hash>::invert_hash(x, <u64 as Hash>::seed1(&self.0))
    }
  }
}
