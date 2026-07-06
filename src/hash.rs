use rand_core::Rng;

pub(crate) trait Hash<T>: Copy {
  fn seed(_: &mut impl Rng) -> Self;

  fn hash(&self, _: T) -> T;

  fn invert_hash(&self, _: T) -> T;
}

// TODO: x86-64
cfg_select! {
  all(
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
    #[path = "hash_unknown.rs"]
    pub(crate) mod backend;
  }
}
