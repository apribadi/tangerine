#![allow(missing_docs)]

use rand_core::Rng;
use self::internal::Backend;

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

cfg_select! {
  all(
      target_arch = "aarch64",
      target_feature = "aes",
      target_feature = "crc",
      target_feature = "neon",
    ) =>
  {
    #[path = "hash_aarch64.rs"]
    mod aarch64;

    const BACKEND: Backend = Backend::AArch64;
  }
  _ => {
    #[path = "hash_generic.rs"]
    mod generic;

    const BACKEND: Backend = Backend::Generic;
  }
}

pub mod internal {
  use super::Hash;
  use super::Rng;

  pub enum Backend {
    AArch64,
    Generic,
  }

  pub const BACKEND: Backend = super::BACKEND;

  pub struct Hash8(<u8 as Hash>::Seed);

  impl Hash8 {
    pub fn with_seed(g: &mut impl Rng) -> Self {
      Self(<u8 as Hash>::seed(g))
    }

    pub fn hash(&self, x: u8) -> u8 {
      <u8 as Hash>::hash(x, <u8 as Hash>::seed0(&self.0))
    }

    pub fn invert_hash(&self, x: u8) -> u8 {
      <u8 as Hash>::invert_hash(x, <u8 as Hash>::seed1(&self.0))
    }
  }

  pub struct Hash32(<u32 as Hash>::Seed);

  impl Hash32 {
    pub fn with_seed(g: &mut impl Rng) -> Self {
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
    pub fn with_seed(g: &mut impl Rng) -> Self {
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
