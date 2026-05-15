#![cfg_attr(miri, feature(uint_carryless_mul))]
#![doc = include_str!("../README.md")]

pub mod key;
pub mod map;
pub mod set;

mod hash;
mod util;
mod word;

cfg_select! {
  all(
      target_arch = "aarch64",
      target_feature = "aes",
      target_feature = "crc",
      target_feature = "neon",
    ) =>
  {
    mod hash_aarch64;
  }
  _ => {
    mod hash_fallback;
  }
}
