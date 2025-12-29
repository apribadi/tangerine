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

fn clear(t: &mut HashMap<NonZeroU64, u64>) {
  t.clear();
}

fn reset(t: &mut HashMap<NonZeroU64, u64>) {
  t.reset();
}

fn sum_fold(t: &mut HashMap<NonZeroU64, u64>) -> u64 {
  return t.values().fold(0, |x, &y| x.wrapping_add(y));
}

fn sum_loop(t: &mut HashMap<NonZeroU64, u64>) -> u64 {
  let mut x = 0u64;
  for &y in t.values() { x = x.wrapping_add(y); }
  return x;
}

/// ?

pub fn main() {
  let _ =
    black_box([
      get_mut as *const u8,
      insert as *const u8,
      remove as *const u8,
      clear as *const u8,
      reset as *const u8,
      sum_fold as *const u8,
      sum_loop as *const u8,
    ]);
}
