#![allow(missing_docs)]

use std::num::NonZeroU32;
use std::hint::black_box;
use tangerine::map::HashMap;

fn drop(_: HashMap<NonZeroU32, usize>) {
}

fn new() -> HashMap<NonZeroU32, usize> {
  HashMap::new()
}

fn len(t: &HashMap<NonZeroU32, usize>) -> usize {
  t.len()
}

fn is_empty(t: &HashMap<NonZeroU32, usize>) -> bool {
  t.is_empty()
}

fn contains_key(t: &HashMap<NonZeroU32, usize>, k: NonZeroU32) -> bool {
  t.contains_key(k)
}

fn get(t: &HashMap<NonZeroU32, usize>, k: NonZeroU32) -> Option<&usize> {
  t.get(k)
}

fn get_value(t: &HashMap<NonZeroU32, usize>, k: NonZeroU32) -> Option<usize> {
  match t.get(k) { None => None, Some(&y) => Some(y) }
}

fn insert(t: &mut HashMap<NonZeroU32, usize>, k: NonZeroU32, v: usize) -> Option<usize> {
  t.insert(k, v)
}

fn remove(t: &mut HashMap<NonZeroU32, usize>, k: NonZeroU32) -> Option<usize> {
  t.remove(k)
}

fn clear(t: &mut HashMap<NonZeroU32, usize>) {
  t.clear();
}

fn reset(t: &mut HashMap<NonZeroU32, usize>) {
  t.reset();
}

fn clone(t: &HashMap<NonZeroU32, usize>) -> HashMap<NonZeroU32, usize> {
  t.clone()
}

fn sum_fold(t: &mut HashMap<NonZeroU32, usize>) -> usize {
  t.values().fold(0, |x, &y| x.wrapping_add(y))
}

fn sum_loop(t: &mut HashMap<NonZeroU32, usize>) -> usize {
  let mut x = 0usize;
  for &y in t.values() { x = x.wrapping_add(y); }
  x
}

fn std_clear(t: &mut std::collections::HashMap<NonZeroU32, usize>) {
  t.clear();
}

fn main() {
  let _ =
    black_box([
      drop as *mut u8,
      new as *mut u8,
      len as *mut u8,
      is_empty as *mut u8,
      contains_key as *mut u8,
      get as *mut u8,
      get_value as *mut u8,
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
