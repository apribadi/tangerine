#![doc = include_str!("../README.md")]

pub mod key;
pub mod map;
pub mod set;

/// ?

pub fn foo(t: &mut map::HashMap<std::num::NonZeroU64, u64>, k: std::num::NonZeroU64, v: u64) {
  t.insert(k, v);
}
