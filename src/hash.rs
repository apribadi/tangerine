//! Hashing

use rand_core::Rng;

pub(crate) trait Hash<T> {
  fn new(_: &mut impl Rng) -> Self;

  fn new_nondet() -> Self;

  fn forward(&self) -> impl Copy + Fn(T) -> T;

  fn inverse(&self) -> impl Copy + Fn(T) -> T;
}

// TODO: x86-64
cfg_select! {
  all(
      not(feature = "use-basic-hash"),
      target_arch = "aarch64",
      target_feature = "aes",
      target_feature = "crc",
      target_feature = "neon",
    ) =>
  {
    #[path = "hash_aarch64.rs"]
    pub(crate) mod backend;
  }
  _ => {
    #[path = "hash_basic.rs"]
    pub(crate) mod backend;
  }
}

pub mod internal {
  //! Unstable API exposing implementation details for benchmarks and tests.

  #![allow(missing_docs)]

  use rand_core::Rng;
  use crate::hash::Hash as _;

  pub enum Backend {
    AArch64,
    Basic,
  }

  pub const BACKEND: Backend = super::backend::BACKEND;

  pub trait Hash<T> {
    fn new(g: &mut impl Rng) -> Self;

    fn hash(&self, x: T) -> T;

    fn invert_hash(&self, x: T) -> T;
  }

  pub struct HashU8(super::backend::HashU8);

  pub struct HashU16(super::backend::HashU16);

  pub struct HashU32(super::backend::HashU32);

  pub struct HashU64(super::backend::HashU64);

  impl Hash<u8> for HashU8 {
    fn new(g: &mut impl Rng) -> Self {
      Self(super::backend::HashU8::new(g))
    }

    fn hash(&self, x: u8) -> u8 {
      self.0.forward()(x)
    }

    fn invert_hash(&self, x: u8) -> u8 {
      self.0.inverse()(x)
    }
  }

  impl Hash<u16> for HashU16 {
    fn new(g: &mut impl Rng) -> Self {
      Self(super::backend::HashU16::new(g))
    }

    fn hash(&self, x: u16) -> u16 {
      self.0.forward()(x)
    }

    fn invert_hash(&self, x: u16) -> u16 {
      self.0.inverse()(x)
    }
  }

  impl Hash<u32> for HashU32 {
    fn new(g: &mut impl Rng) -> Self {
      Self(super::backend::HashU32::new(g))
    }

    fn hash(&self, x: u32) -> u32 {
      self.0.forward()(x)
    }

    fn invert_hash(&self, x: u32) -> u32 {
      self.0.inverse()(x)
    }
  }

  impl Hash<u64> for HashU64 {
    fn new(g: &mut impl Rng) -> Self {
      Self(super::backend::HashU64::new(g))
    }

    fn hash(&self, x: u64) -> u64 {
      self.0.forward()(x)
    }

    fn invert_hash(&self, x: u64) -> u64 {
      self.0.inverse()(x)
    }
  }
}
