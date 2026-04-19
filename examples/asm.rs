#![allow(missing_docs)]

use dandelion::Rng;
use std::num::NonZeroU32;
use std::num::NonZeroU64;
use tangerine::map::Entry;
use tangerine::map::IntMap;

pub fn drop(_: IntMap<NonZeroU32, NonZeroU64>) {
}

pub fn new() -> IntMap<NonZeroU32, NonZeroU64> {
  IntMap::new()
}

pub fn new_seeded(rng: &mut Rng) -> IntMap<NonZeroU32, NonZeroU64> {
  IntMap::new_seeded(rng)
}

pub fn len(t: &IntMap<NonZeroU32, NonZeroU64>) -> usize {
  t.len()
}

pub fn is_empty(t: &IntMap<NonZeroU32, NonZeroU64>) -> bool {
  t.is_empty()
}

pub fn contains_key(t: &IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> bool {
  t.contains_key(k)
}

pub fn get(t: &IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> Option<&NonZeroU64> {
  t.get(k)
}

pub fn get_value(t: &IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> Option<NonZeroU64> {
  match t.get(k) { None => None, Some(&y) => Some(y) }
}

pub fn insert(t: &mut IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32, v: NonZeroU64) -> Option<NonZeroU64> {
  t.insert(k, v)
}

pub fn entry_insert(t: &mut IntMap<NonZeroU32, NonZeroU64>, key: NonZeroU32, value: NonZeroU64) -> Option<NonZeroU64> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(core::mem::replace(entry.into_mut_ref(), value)),
    Entry::Vacant(entry) => { let _ = entry.insert(value); None }
  }
}
pub fn entry_try_insert(
    t: &mut IntMap<NonZeroU32, NonZeroU64>,
    key: NonZeroU32,
    value: NonZeroU64
  ) -> Result<&mut NonZeroU64, (&mut NonZeroU64, NonZeroU64)>
{
  match t.entry(key) {
    Entry::Occupied(entry) => Err((entry.into_mut_ref(), value)),
    Entry::Vacant(entry) => Ok(entry.insert(value)),
  }
}

pub fn remove(t: &mut IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> Option<NonZeroU64> {
  t.remove(k)
}

pub fn entry_remove(t: &mut IntMap<NonZeroU32, NonZeroU64>, key: NonZeroU32) -> Option<NonZeroU64> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(entry.remove()),
    Entry::Vacant(_) => None,
  }
}

pub fn clear(t: &mut IntMap<NonZeroU32, NonZeroU64>) {
  t.clear();
}

pub fn reset(t: &mut IntMap<NonZeroU32, NonZeroU64>) {
  t.reset();
}

pub fn clone(t: &IntMap<NonZeroU32, NonZeroU64>) -> IntMap<NonZeroU32, NonZeroU64> {
  t.clone()
}

pub fn sum_fold(t: &mut IntMap<NonZeroU32, u64>) -> u64 {
  t.values().fold(0, |x, &y| x.wrapping_add(y))
}

pub fn sum_loop(t: &mut IntMap<NonZeroU32, u64>) -> u64 {
  let mut x = 0u64;
  for &y in t.values() { x = x.wrapping_add(y); }
  x
}

pub fn std_clear(t: &mut std::collections::HashMap<NonZeroU32, NonZeroU64>) {
  t.clear();
}

/*
#[allow(missing_docs)]
#[inline(never)]
pub fn entry_incr(t: &mut ExampleMap, key: ExampleKey) {
  match t.entry(key) {
    Entry::Occupied(entry) => { *entry.into_mut_ref() += 1; }
    Entry::Vacant(entry) => { let _ = entry.insert(1); }
  }
}

#[allow(missing_docs)]
#[inline(never)]
pub fn entry_decr(t: &mut ExampleMap, key: ExampleKey) {
  match t.entry(key) {
    Entry::Occupied(mut entry) => {
      if *entry.get_mut() <= 1 {
        let _ = entry.remove();
      } else {
        *entry.into_mut_ref() -= 1;
      }
    }
    Entry::Vacant(_) => { }
  }
}
*/
