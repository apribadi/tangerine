#![allow(missing_docs)]

use std::num::NonZeroU32;
use std::num::NonZeroU64;
use tangerine::map::HashMap;
use tangerine::map::Entry;

pub fn drop(_: HashMap<NonZeroU32, NonZeroU64>) {
}

pub fn new() -> HashMap<NonZeroU32, NonZeroU64> {
  HashMap::new()
}

pub fn len(t: &HashMap<NonZeroU32, NonZeroU64>) -> usize {
  t.len()
}

pub fn is_empty(t: &HashMap<NonZeroU32, NonZeroU64>) -> bool {
  t.is_empty()
}

pub fn contains_key(t: &HashMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> bool {
  t.contains_key(k)
}

pub fn get(t: &HashMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> Option<&NonZeroU64> {
  t.get(k)
}

pub fn get_value(t: &HashMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> Option<NonZeroU64> {
  match t.get(k) { None => None, Some(&y) => Some(y) }
}

pub fn insert(t: &mut HashMap<NonZeroU32, NonZeroU64>, k: NonZeroU32, v: NonZeroU64) -> Option<NonZeroU64> {
  t.insert(k, v)
}

pub fn entry_insert(t: &mut HashMap<NonZeroU32, NonZeroU64>, key: NonZeroU32, value: NonZeroU64) -> Option<NonZeroU64> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(core::mem::replace(entry.into_mut_ref(), value)),
    Entry::Vacant(entry) => { let _ = entry.insert(value); None }
  }
}
pub fn entry_try_insert(
    t: &mut HashMap<NonZeroU32, NonZeroU64>,
    key: NonZeroU32,
    value: NonZeroU64
  ) -> Result<&mut NonZeroU64, (&mut NonZeroU64, NonZeroU64)>
{
  match t.entry(key) {
    Entry::Occupied(entry) => Err((entry.into_mut_ref(), value)),
    Entry::Vacant(entry) => Ok(entry.insert(value)),
  }
}

pub fn remove(t: &mut HashMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> Option<NonZeroU64> {
  t.remove(k)
}

pub fn entry_remove(t: &mut HashMap<NonZeroU32, NonZeroU64>, key: NonZeroU32) -> Option<NonZeroU64> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(entry.remove()),
    Entry::Vacant(_) => None,
  }
}

pub fn clear(t: &mut HashMap<NonZeroU32, NonZeroU64>) {
  t.clear();
}

pub fn reset(t: &mut HashMap<NonZeroU32, NonZeroU64>) {
  t.reset();
}

pub fn clone(t: &HashMap<NonZeroU32, NonZeroU64>) -> HashMap<NonZeroU32, NonZeroU64> {
  t.clone()
}

pub fn sum_fold(t: &mut HashMap<NonZeroU32, u64>) -> u64 {
  t.values().fold(0, |x, &y| x.wrapping_add(y))
}

pub fn sum_loop(t: &mut HashMap<NonZeroU32, u64>) -> u64 {
  let mut x = 0u64;
  for &y in t.values() { x = x.wrapping_add(y); }
  x
}

pub fn std_clear(t: &mut std::collections::HashMap<NonZeroU32, NonZeroU64>) {
  t.clear();
}
