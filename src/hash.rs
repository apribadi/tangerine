//! hashing

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

// TODO: x86-64
cfg_select! {
  feature = "use-basic-hash" => {
    #[path = "hash_basic.rs"]
    mod backend;
  }
  all(
      target_arch = "aarch64",
      target_feature = "aes",
      target_feature = "crc",
      target_feature = "neon",
    ) =>
  {
    #[path = "hash_aarch64.rs"]
    mod backend;
  }
  _ => {
    #[path = "hash_basic.rs"]
    mod backend;
  }
}

pub mod internal {
  //! Unstable API exposing implementation details for benchmarks and tests.

  #![allow(missing_docs)]

  use rand_core::Rng;

  pub enum Backend {
    AArch64,
    Basic,
  }

  pub const BACKEND: Backend = super::backend::BACKEND;

  #[allow(private_bounds)]
  pub trait Hash: super::Hash {
  }

  impl<T: super::Hash> Hash for T {
  }

  pub struct Hasher<T: Hash>(<T as super::Hash>::Seed);

  impl<T: Hash> Hasher<T> {
    pub fn with_seed(g: &mut impl Rng) -> Self {
      Self(<T as super::Hash>::seed(g))
    }

    pub fn hash(&self, x: T) -> T {
      <T as super::Hash>::hash(x, <T as super::Hash>::seed0(&self.0))
    }

    pub fn invert_hash(&self, x: T) -> T {
      <T as super::Hash>::invert_hash(x, <T as super::Hash>::seed1(&self.0))
    }
  }
}
