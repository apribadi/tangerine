#![allow(missing_docs)]

use dandelion::Rng;
use std::mem::replace;
use std::num::NonZeroU64;
use tangerine::map::Entry;
use tangerine::map::IntMap;

pub fn drop(_: IntMap<NonZeroU64, NonZeroU64>) {
}

pub fn new() -> IntMap<NonZeroU64, NonZeroU64> {
  IntMap::new()
}

pub fn with_seed(rng: &mut Rng) -> IntMap<NonZeroU64, NonZeroU64> {
  IntMap::with_seed(rng)
}

#[inline(never)]
pub fn len(t: &IntMap<NonZeroU64, NonZeroU64>) -> usize {
  t.len()
}

pub fn is_empty(t: &IntMap<NonZeroU64, NonZeroU64>) -> bool {
  t.is_empty()
}

pub fn contains_key(t: &IntMap<NonZeroU64, NonZeroU64>, k: NonZeroU64) -> bool {
  t.contains_key(k)
}

pub fn prefetch(t: &IntMap<NonZeroU64, NonZeroU64>, k: NonZeroU64) {
  t.prefetch(k)
}

pub fn get(t: &IntMap<NonZeroU64, NonZeroU64>, k: NonZeroU64) -> Option<&NonZeroU64> {
  t.get(k)
}

pub fn get_value(t: &IntMap<NonZeroU64, NonZeroU64>, k: NonZeroU64) -> Option<NonZeroU64> {
  match t.get(k) { None => None, Some(&y) => Some(y) }
}

pub fn prefetch_get(t: &IntMap<NonZeroU64, NonZeroU64>, k: NonZeroU64) -> Option<&NonZeroU64> {
  t.prefetch(k);
  t.get(k)
}

pub fn get_mut(t: &mut IntMap<NonZeroU64, NonZeroU64>, k: NonZeroU64) -> Option<&mut NonZeroU64> {
  t.get_mut(k)
}

pub fn get_disjoint_mut_0(t: &mut IntMap<NonZeroU64, NonZeroU64>, ks: [NonZeroU64; 0]) -> [Option<&mut NonZeroU64>; 0] {
  t.get_disjoint_mut(ks)
}

pub fn get_disjoint_mut_4(t: &mut IntMap<NonZeroU64, NonZeroU64>, ks: [NonZeroU64; 4]) -> [Option<&mut NonZeroU64>; 4] {
  t.get_disjoint_mut(ks)
}

pub fn insert(t: &mut IntMap<NonZeroU64, NonZeroU64>, k: NonZeroU64, v: NonZeroU64) -> Option<NonZeroU64> {
  t.insert(k, v)
}

pub fn remove(t: &mut IntMap<NonZeroU64, NonZeroU64>, k: NonZeroU64) -> Option<NonZeroU64> {
  t.remove(k)
}

pub fn clear(t: &mut IntMap<NonZeroU64, NonZeroU64>) {
  t.clear();
}

pub fn clear_needs_drop(t: &mut IntMap<NonZeroU64, Box<u64>>) {
  t.clear();
}

pub fn reset(t: &mut IntMap<NonZeroU64, NonZeroU64>) {
  t.reset();
}

pub fn reset_needs_drop(t: &mut IntMap<NonZeroU64, Box<u64>>) {
  t.reset();
}

pub fn clone(t: &IntMap<NonZeroU64, NonZeroU64>) -> IntMap<NonZeroU64, NonZeroU64> {
  t.clone()
}

pub fn iter_keys_loop(t: &mut IntMap<NonZeroU64, NonZeroU64>) -> u64 {
  let mut x = 0u64;
  for y in t.keys() { x ^= y.get(); }
  x
}

pub fn iter_values_fold(t: &mut IntMap<NonZeroU64, NonZeroU64>) -> u64 {
  t.values().fold(0, |x, &y| x ^ y.get())
}

pub fn iter_values_for_each(t: &mut IntMap<NonZeroU64, NonZeroU64>) -> u64 {
  let mut x = 0u64;
  t.values().for_each(|&y| { x ^= y.get(); });
  x
}

pub fn iter_values_loop(t: &mut IntMap<NonZeroU64, NonZeroU64>) -> u64 {
  let mut x = 0u64;
  for &y in t.values() { x ^= y.get(); }
  x
}

#[inline(never)]
pub fn num_slots(t: &IntMap<NonZeroU64, NonZeroU64>) -> usize {
  tangerine::map::internal::num_slots(t)
}

#[inline(never)]
pub fn displacement_histogram(t: &IntMap<NonZeroU64, NonZeroU64>) -> [usize; 10] {
  tangerine::map::internal::displacement_histogram(t)
}

pub fn entry_insert(t: &mut IntMap<NonZeroU64, NonZeroU64>, key: NonZeroU64, value: NonZeroU64) -> Option<NonZeroU64> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(replace(entry.into_mut(), value)),
    Entry::Vacant(entry) => { let _ = entry.insert(value); None }
  }
}

pub fn entry_try_insert(
    t: &mut IntMap<NonZeroU64, NonZeroU64>,
    key: NonZeroU64,
    value: NonZeroU64
  ) -> Result<&mut NonZeroU64, (&mut NonZeroU64, NonZeroU64)>
{
  match t.entry(key) {
    Entry::Occupied(entry) => Err((entry.into_mut(), value)),
    Entry::Vacant(entry) => Ok(entry.insert(value)),
  }
}

pub fn entry_remove(t: &mut IntMap<NonZeroU64, NonZeroU64>, key: NonZeroU64) -> Option<NonZeroU64> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(entry.remove()),
    Entry::Vacant(_) => None,
  }
}

pub fn entry_inc(t: &mut IntMap<NonZeroU64, NonZeroU64>, key: NonZeroU64) {
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

pub fn entry_dec(t: &mut IntMap<NonZeroU64, NonZeroU64>, key: NonZeroU64) {
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
