#![allow(missing_docs)]

use dandelion::Rng;
use std::mem::replace;
use std::num::NonZeroU32;
use std::num::NonZeroU64;
use tangerine::map::Entry;
use tangerine::map::IntMap;

#[inline(never)]
pub fn drop(_: IntMap<NonZeroU32, NonZeroU64>) {
}

#[inline(never)]
pub fn new() -> IntMap<NonZeroU32, NonZeroU64> {
  IntMap::new()
}

#[inline(never)]
pub fn with_seed(rng: &mut Rng) -> IntMap<NonZeroU32, NonZeroU64> {
  IntMap::with_seed(rng)
}

#[inline(never)]
pub fn len(t: &IntMap<NonZeroU32, NonZeroU64>) -> usize {
  t.len()
}

#[inline(never)]
pub fn is_empty(t: &IntMap<NonZeroU32, NonZeroU64>) -> bool {
  t.is_empty()
}

#[inline(never)]
pub fn contains_key(t: &IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> bool {
  t.contains_key(k)
}

#[inline(never)]
pub fn prefetch(t: &IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) {
  t.prefetch(k)
}

#[inline(never)]
pub fn get(t: &IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> Option<&NonZeroU64> {
  t.get(k)
}

#[inline(never)]
pub fn get_value(t: &IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> Option<NonZeroU64> {
  match t.get(k) { None => None, Some(&y) => Some(y) }
}

#[inline(never)]
pub fn get_mut(t: &mut IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> Option<&mut NonZeroU64> {
  t.get_mut(k)
}

#[inline(never)]
pub fn get_disjoint_mut_0(t: &mut IntMap<NonZeroU32, NonZeroU64>, ks: [NonZeroU32; 0]) -> [Option<&mut NonZeroU64>; 0] {
  t.get_disjoint_mut(ks)
}

#[inline(never)]
pub fn get_disjoint_mut_4(t: &mut IntMap<NonZeroU32, NonZeroU64>, ks: [NonZeroU32; 4]) -> [Option<&mut NonZeroU64>; 4] {
  t.get_disjoint_mut(ks)
}

#[inline(never)]
pub fn get_or_insert(t: &mut IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> &mut NonZeroU64 {
  t.get_or_insert(k, NonZeroU64::MIN)
}

#[inline(never)]
pub fn get_or_insert_with(t: &mut IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> &mut NonZeroU64 {
  t.get_or_insert_with(k, || NonZeroU64::MIN)
}

#[inline(never)]
pub fn prefetch_get(t: &IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> Option<&NonZeroU64> {
  t.prefetch(k);
  t.get(k)
}

#[inline(never)]
pub fn insert(t: &mut IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32, v: NonZeroU64) -> Option<NonZeroU64> {
  t.insert(k, v)
}

#[inline(never)]
pub fn remove(t: &mut IntMap<NonZeroU32, NonZeroU64>, k: NonZeroU32) -> Option<NonZeroU64> {
  t.remove(k)
}

#[inline(never)]
pub fn clear(t: &mut IntMap<NonZeroU32, NonZeroU64>) {
  t.clear();
}

#[inline(never)]
pub fn clear_needs_drop(t: &mut IntMap<NonZeroU32, Box<u64>>) {
  t.clear();
}

#[inline(never)]
pub fn reset(t: &mut IntMap<NonZeroU32, NonZeroU64>) {
  t.reset();
}

#[inline(never)]
pub fn reset_needs_drop(t: &mut IntMap<NonZeroU32, Box<u64>>) {
  t.reset();
}

#[inline(never)]
pub fn clone(t: &IntMap<NonZeroU32, NonZeroU64>) -> IntMap<NonZeroU32, NonZeroU64> {
  t.clone()
}

#[inline(never)]
pub fn iter(t: &IntMap<NonZeroU32, NonZeroU64>) -> impl ExactSizeIterator<Item = (NonZeroU32, &NonZeroU64)> {
  t.iter()
}

#[inline(never)]
pub fn values(t: &IntMap<NonZeroU32, NonZeroU64>) -> impl ExactSizeIterator<Item = &NonZeroU64> {
  t.values()
}

#[inline(never)]
pub fn iter_keys_loop(t: &mut IntMap<NonZeroU32, NonZeroU64>) -> u32 {
  let mut x = 0u32;
  for y in t.keys() { x ^= y.get(); }
  x
}

#[inline(never)]
pub fn iter_values_fold(t: &mut IntMap<NonZeroU32, NonZeroU64>) -> u64 {
  t.values().fold(0, |x, &y| x ^ y.get())
}

#[inline(never)]
pub fn iter_values_for_each(t: &mut IntMap<NonZeroU32, NonZeroU64>) -> u64 {
  let mut x = 0u64;
  t.values().for_each(|&y| { x ^= y.get(); });
  x
}

#[inline(never)]
pub fn iter_values_loop(t: &mut IntMap<NonZeroU32, NonZeroU64>) -> u64 {
  let mut x = 0u64;
  for &y in t.values() { x ^= y.get(); }
  x
}

#[inline(never)]
pub fn num_slots(t: &IntMap<NonZeroU32, NonZeroU64>) -> usize {
  tangerine::map::internal::num_slots(t)
}

#[inline(never)]
pub fn displacement_histogram(t: &IntMap<NonZeroU32, NonZeroU64>) -> [usize; 10] {
  tangerine::map::internal::displacement_histogram(t)
}

#[inline(never)]
pub fn entry(t: &mut IntMap<NonZeroU32, NonZeroU64>, key: NonZeroU32) -> Entry<'_, NonZeroU32, NonZeroU64> {
  t.entry(key)
}

#[inline(never)]
pub fn entry_get_mut(t: &mut IntMap<NonZeroU32, NonZeroU64>, key: NonZeroU32) -> Option<&mut NonZeroU64> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(entry.into_mut()),
    Entry::Vacant(_) => None,
  }
}

#[inline(never)]
pub fn entry_insert(t: &mut IntMap<NonZeroU32, NonZeroU64>, key: NonZeroU32, value: NonZeroU64) -> Option<NonZeroU64> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(replace(entry.into_mut(), value)),
    Entry::Vacant(entry) => { let _ = entry.insert(value); None }
  }
}

#[inline(never)]
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

#[inline(never)]
pub fn entry_remove(t: &mut IntMap<NonZeroU32, NonZeroU64>, key: NonZeroU32) -> Option<NonZeroU64> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(entry.remove()),
    Entry::Vacant(_) => None,
  }
}

#[inline(never)]
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

#[inline(never)]
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
