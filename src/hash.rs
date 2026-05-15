use rand_core::Rng;

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
