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

  #[derive(Clone, Copy)]
  pub struct Seed0(<u32 as Hash>::Seed0);

  #[derive(Clone, Copy)]
  pub struct Seed1(<u32 as Hash>::Seed1);

  pub fn seed(g: &mut impl Rng) -> (Seed0, Seed1) {
    let m = <u32 as Hash>::seed(g);
    (Seed0(<u32 as Hash>::seed0(&m)), Seed1(<u32 as Hash>::seed1(&m)))
  }

  pub fn hash(x: u32, m: Seed0) -> u32 {
    <u32 as Hash>::hash(x, m.0)
  }

  pub fn invert_hash(x: u32, m: Seed1) -> u32 {
    <u32 as Hash>::invert_hash(x, m.0)
  }
}
