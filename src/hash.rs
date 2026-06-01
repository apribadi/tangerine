use rand_core::Rng;

pub(crate) trait Hash<T> {
  type Seed;

  fn seed(_: &mut impl Rng) -> Self::Seed;

  fn seed_nondet() -> Self::Seed;

  fn new(_: Self::Seed) -> Self;

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
