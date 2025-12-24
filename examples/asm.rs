//!?

use std::num::NonZeroU64;
use std::hint::black_box;
use tangerine::map::HashMap;

fn get_mut(t: &mut HashMap<NonZeroU64, u64>, k: NonZeroU64) -> Option<&mut u64> {
  return t.get_mut(k);
}

fn insert(t: &mut HashMap<NonZeroU64, u64>, k: NonZeroU64, v: u64) {
  t.insert(k, v);
}

fn remove(t: &mut HashMap<NonZeroU64, u64>, k: NonZeroU64) {
  t.remove(k);
}

/// ?

pub fn main() {
  let _ = black_box(get_mut as *const u8);
  let _ = black_box(insert as *const u8);
  let _ = black_box(remove as *const u8);
}
