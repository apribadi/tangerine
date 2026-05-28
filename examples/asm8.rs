#![allow(missing_docs)]

use dandelion::Rng;
use std::mem::replace;
use std::num::NonZeroU8;
use tangerine::map::Entry;
use tangerine::map::IntMap;

#[inline(never)]
pub fn drop(_: IntMap<NonZeroU8, NonZeroU8>) {
}

#[inline(never)]
pub fn new() -> IntMap<NonZeroU8, NonZeroU8> {
  IntMap::new()
}

#[inline(never)]
pub fn with_seed(rng: &mut Rng) -> IntMap<NonZeroU8, NonZeroU8> {
  IntMap::with_seed(rng)
}

#[inline(never)]
pub fn len(t: &IntMap<NonZeroU8, NonZeroU8>) -> usize {
  t.len()
}

#[inline(never)]
pub fn is_empty(t: &IntMap<NonZeroU8, NonZeroU8>) -> bool {
  t.is_empty()
}

#[inline(never)]
pub fn contains_key(t: &IntMap<NonZeroU8, NonZeroU8>, k: NonZeroU8) -> bool {
  t.contains_key(k)
}

#[inline(never)]
pub fn prefetch(t: &IntMap<NonZeroU8, NonZeroU8>, k: NonZeroU8) {
  t.prefetch(k)
}

#[inline(never)]
pub fn get(t: &IntMap<NonZeroU8, NonZeroU8>, k: NonZeroU8) -> Option<&NonZeroU8> {
  t.get(k)
}

#[inline(never)]
pub fn get_value(t: &IntMap<NonZeroU8, NonZeroU8>, k: NonZeroU8) -> Option<NonZeroU8> {
  match t.get(k) { None => None, Some(&y) => Some(y) }
}

#[inline(never)]
pub fn get_mut(t: &mut IntMap<NonZeroU8, NonZeroU8>, k: NonZeroU8) -> Option<&mut NonZeroU8> {
  t.get_mut(k)
}

#[inline(never)]
pub fn get_disjoint_mut_0(t: &mut IntMap<NonZeroU8, NonZeroU8>, ks: [NonZeroU8; 0]) -> [Option<&mut NonZeroU8>; 0] {
  t.get_disjoint_mut(ks)
}

#[inline(never)]
pub fn get_disjoint_mut_4(t: &mut IntMap<NonZeroU8, NonZeroU8>, ks: [NonZeroU8; 4]) -> [Option<&mut NonZeroU8>; 4] {
  t.get_disjoint_mut(ks)
}

#[inline(never)]
pub fn get_or_insert(t: &mut IntMap<NonZeroU8, NonZeroU8>, k: NonZeroU8) -> &mut NonZeroU8 {
  t.get_or_insert(k, NonZeroU8::MIN)
}

#[inline(never)]
pub fn get_or_insert_with(t: &mut IntMap<NonZeroU8, NonZeroU8>, k: NonZeroU8) -> &mut NonZeroU8 {
  t.get_or_insert_with(k, || NonZeroU8::MIN)
}

#[inline(never)]
pub fn prefetch_get(t: &IntMap<NonZeroU8, NonZeroU8>, k: NonZeroU8) -> Option<&NonZeroU8> {
  t.prefetch(k);
  t.get(k)
}

#[inline(never)]
pub fn insert(t: &mut IntMap<NonZeroU8, NonZeroU8>, k: NonZeroU8, v: NonZeroU8) -> Option<NonZeroU8> {
  t.insert(k, v)
}

#[inline(never)]
pub fn remove(t: &mut IntMap<NonZeroU8, NonZeroU8>, k: NonZeroU8) -> Option<NonZeroU8> {
  t.remove(k)
}

#[inline(never)]
pub fn clear(t: &mut IntMap<NonZeroU8, NonZeroU8>) {
  t.clear();
}

#[inline(never)]
pub fn clear_needs_drop(t: &mut IntMap<NonZeroU8, Box<u8>>) {
  t.clear();
}

#[inline(never)]
pub fn reset(t: &mut IntMap<NonZeroU8, NonZeroU8>) {
  t.reset();
}

#[inline(never)]
pub fn reset_needs_drop(t: &mut IntMap<NonZeroU8, Box<u8>>) {
  t.reset();
}

#[inline(never)]
pub fn clone(t: &IntMap<NonZeroU8, NonZeroU8>) -> IntMap<NonZeroU8, NonZeroU8> {
  t.clone()
}

#[inline(never)]
pub fn iter(t: &IntMap<NonZeroU8, NonZeroU8>) -> impl ExactSizeIterator<Item = (NonZeroU8, &NonZeroU8)> {
  t.iter()
}

#[inline(never)]
pub fn values(t: &IntMap<NonZeroU8, NonZeroU8>) -> impl ExactSizeIterator<Item = &NonZeroU8> {
  t.values()
}

#[inline(never)]
pub fn iter_keys_loop(t: &mut IntMap<NonZeroU8, NonZeroU8>) -> u8 {
  let mut x = 0u8;
  for y in t.keys() { x ^= y.get(); }
  x
}

#[inline(never)]
pub fn iter_values_fold(t: &mut IntMap<NonZeroU8, NonZeroU8>) -> u8 {
  t.values().fold(0, |x, &y| x ^ y.get())
}

#[inline(never)]
pub fn iter_values_for_each(t: &mut IntMap<NonZeroU8, NonZeroU8>) -> u8 {
  let mut x = 0u8;
  t.values().for_each(|&y| { x ^= y.get(); });
  x
}

#[inline(never)]
pub fn iter_values_loop(t: &mut IntMap<NonZeroU8, NonZeroU8>) -> u8 {
  let mut x = 0u8;
  for &y in t.values() { x ^= y.get(); }
  x
}

#[inline(never)]
pub fn num_slots(t: &IntMap<NonZeroU8, NonZeroU8>) -> usize {
  tangerine::map::internal::num_slots(t)
}

#[inline(never)]
pub fn probe_count_histogram(t: &IntMap<NonZeroU8, NonZeroU8>) -> [usize; 20] {
  tangerine::map::internal::probe_count_histogram(t)
}

#[inline(never)]
pub fn entry(t: &mut IntMap<NonZeroU8, NonZeroU8>, key: NonZeroU8) -> Entry<'_, NonZeroU8, NonZeroU8> {
  t.entry(key)
}

#[inline(never)]
pub fn entry_get_mut(t: &mut IntMap<NonZeroU8, NonZeroU8>, key: NonZeroU8) -> Option<&mut NonZeroU8> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(entry.into_mut()),
    Entry::Vacant(_) => None,
  }
}

#[inline(never)]
pub fn entry_insert(t: &mut IntMap<NonZeroU8, NonZeroU8>, key: NonZeroU8, value: NonZeroU8) -> Option<NonZeroU8> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(replace(entry.into_mut(), value)),
    Entry::Vacant(entry) => { let _ = entry.insert(value); None }
  }
}

#[inline(never)]
pub fn entry_try_insert(
    t: &mut IntMap<NonZeroU8, NonZeroU8>,
    key: NonZeroU8,
    value: NonZeroU8
  ) -> Result<&mut NonZeroU8, (&mut NonZeroU8, NonZeroU8)>
{
  match t.entry(key) {
    Entry::Occupied(entry) => Err((entry.into_mut(), value)),
    Entry::Vacant(entry) => Ok(entry.insert(value)),
  }
}

#[inline(never)]
pub fn entry_remove(t: &mut IntMap<NonZeroU8, NonZeroU8>, key: NonZeroU8) -> Option<NonZeroU8> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(entry.remove()),
    Entry::Vacant(_) => None,
  }
}

#[inline(never)]
pub fn entry_inc(t: &mut IntMap<NonZeroU8, NonZeroU8>, key: NonZeroU8) {
  match t.entry(key) {
    Entry::Occupied(mut entry) => {
      let value = entry.get_mut();
      *value = (*value).saturating_add(1);
    }
    Entry::Vacant(e) => {
      let _ = e.insert(NonZeroU8::MIN);
    }
  }
}

#[inline(never)]
pub fn entry_dec(t: &mut IntMap<NonZeroU8, NonZeroU8>, key: NonZeroU8) {
  match t.entry(key) {
    Entry::Occupied(mut entry) => {
      let value = entry.get_mut();
      match NonZeroU8::new((*value).get() - 1) {
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
