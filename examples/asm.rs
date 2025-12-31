//!?

use std::num::NonZeroU64;
use std::hint::black_box;
use tangerine::map::HashMap;

fn new() -> HashMap<NonZeroU64, u64> {
  return HashMap::new();
}

fn contains_key(t: &HashMap<NonZeroU64, u64>, k: NonZeroU64) -> bool {
  return t.contains_key(k);
}

fn get(t: &HashMap<NonZeroU64, u64>, k: NonZeroU64) -> Option<&u64> {
  return t.get(k);
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

fn clone(t: &HashMap<NonZeroU64, u64>) -> HashMap<NonZeroU64, u64> {
  return t.clone();
}

fn sum_fold(t: &mut HashMap<NonZeroU64, u64>) -> u64 {
  return t.values().fold(0, |x, &y| x.wrapping_add(y));
}

fn sum_loop(t: &mut HashMap<NonZeroU64, u64>) -> u64 {
  let mut x = 0u64;
  for &y in t.values() { x = x.wrapping_add(y); }
  return x;
}

fn std_clear(t: &mut std::collections::HashMap<NonZeroU64, u64>) {
  t.clear();
}

/// ?

pub fn main() {
  let _ =
    black_box([
      new as *mut u8,
      contains_key as *mut u8,
      get as *mut u8,
      insert as *mut u8,
      remove as *mut u8,
      clear as *mut u8,
      reset as *mut u8,
      clone as *mut u8,
      sum_fold as *mut u8,
      sum_loop as *mut u8,
      std_clear as *mut u8,
    ]);
}
