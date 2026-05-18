use rand_core::Rng;

pub(crate) unsafe trait Hash {
  type Seed0: Copy;

  type Seed1: Copy;

  fn seed_nondet() -> (Self::Seed0, Self::Seed1);

  fn seed(_: &mut impl Rng) -> (Self::Seed0, Self::Seed1);

  fn hash(_: Self, _: Self::Seed0) -> Self;

  fn invert_hash(_: Self, _: Self::Seed1) -> Self;
}
