#![allow(missing_docs)]

use dandelion::Rng;
use std::mem::replace;
use std::num::NonZeroU32;
use std::num::NonZeroU64;
use tangerine::map::Entry;
use tangerine::map::IntMap;
use tangerine::set::IntSet;

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

pub fn get_branchy(t: &IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> Option<&NonZeroU64> {
  tangerine::map::internal::get_branchy(t, k)
}

pub fn get_value(t: &IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> Option<NonZeroU64> {
  match t.get(k) { None => None, Some(&y) => Some(y) }
}

pub fn get_disjoint_mut(t: &mut IntMap<NonZeroU32, NonZeroU64>, ks: [NonZeroU32; 4]) -> [Option<&mut NonZeroU64>; 4] {
  t.get_disjoint_mut(ks)
}

pub fn insert(t: &mut IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32, v: NonZeroU64) -> Option<NonZeroU64> {
  t.insert(k, v)
}

pub fn entry_insert(t: &mut IntMap<NonZeroU32, NonZeroU64>, key: NonZeroU32, value: NonZeroU64) -> Option<NonZeroU64> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(replace(entry.into_mut(), value)),
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
    Entry::Occupied(entry) => Err((entry.into_mut(), value)),
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

pub fn iter_fold(t: &mut IntMap<NonZeroU32, u64>) -> u64 {
  t.values().fold(0, |x, &y| x ^ y)
}

pub fn iter_for_each(t: &mut IntMap<NonZeroU32, u64>) -> u64 {
  let mut x = 0u64;
  t.values().for_each(|&y| { x ^= y; });
  x
}

pub fn iter_loop(t: &mut IntMap<NonZeroU32, u64>) -> u64 {
  let mut x = 0u64;
  for &y in t.values() { x ^= y; }
  x
}

pub fn inc(t: &mut IntMap<NonZeroU32, u64>, key: NonZeroU32) {
  *t.get_or_insert(key, 0) += 1;
}

pub fn entry_inc(t: &mut IntMap<NonZeroU32, NonZeroU64>, key: NonZeroU32) {
  match t.entry(key) {
    Entry::Occupied(mut entry) => {
      let value = entry.get_mut();
      *value = (*value).saturating_add(1);
    }
    Entry::Vacant(e) => {
      let _ = e.insert(NonZeroU64::MIN);
    }
  }
}

pub fn entry_dec(t: &mut IntMap<NonZeroU32, NonZeroU64>, key: NonZeroU32) {
  match t.entry(key) {
    Entry::Occupied(mut entry) => {
      let value = entry.get_mut();
      match NonZeroU64::new((*value).get() - 1) {
        None => {
          let _ = entry.remove();
        }
        Some(n) => {
          *value = n;
        }
      }
    }
    Entry::Vacant(_) => {
    }
  }
}

pub fn set_contains(t: &IntSet<NonZeroU32>, k: NonZeroU32) -> bool {
  t.contains(k)
}

pub fn set_insert(t: &mut IntSet<NonZeroU32>, k: NonZeroU32) -> bool {
  t.insert(k)
}

pub fn set_remove(t: &mut IntSet<NonZeroU32>, k: NonZeroU32) -> bool {
  t.remove(k)
}

pub fn hashbrown_clear(t: &mut foldhash::HashMap<NonZeroU32, NonZeroU64>) {
  t.clear();
}

pub fn hashbrown_entry_inc(t: &mut foldhash::HashMap<NonZeroU32, NonZeroU64>, key: NonZeroU32) {
  match t.entry(key) {
    std::collections::hash_map::Entry::Occupied(mut entry) => {
      let value = entry.get_mut();
      *value = (*value).saturating_add(1);
    }
    std::collections::hash_map::Entry::Vacant(e) => {
      let _ = e.insert(NonZeroU64::MIN);
    }
  }
}

pub fn hashbrown_entry_dec(t: &mut foldhash::HashMap<NonZeroU32, NonZeroU64>, key: NonZeroU32) {
  match t.entry(key) {
    std::collections::hash_map::Entry::Occupied(mut entry) => {
      let value = entry.get_mut();
      match NonZeroU64::new((*value).get() - 1) {
        None => {
          let _ = entry.remove();
        }
        Some(n) => {
          *value = n;
        }
      }
    }
    std::collections::hash_map::Entry::Vacant(_) => {
    }
  }
}
