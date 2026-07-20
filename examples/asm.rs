#![allow(missing_docs)]

use dandelion::Rng;
use std::mem::replace;
use tangerine::map::Entry;
use tangerine::map::IntMap;

type Key = std::num::NonZeroU32;

type Value = std::num::NonZeroU32;

const DEFAULT_VALUE: Value = std::num::NonZeroU32::MIN;

#[inline(never)]
pub fn drop(_: IntMap<Key, Value>) {
}

#[inline(never)]
pub fn new() -> IntMap<Key, Value> {
  IntMap::new()
}

#[inline(never)]
pub fn with_seed(rng: &mut Rng) -> IntMap<Key, Value> {
  IntMap::with_seed(rng)
}

#[inline(never)]
pub fn len(t: &IntMap<Key, Value>) -> usize {
  t.len()
}

#[inline(never)]
pub fn is_empty(t: &IntMap<Key, Value>) -> bool {
  t.is_empty()
}

#[inline(never)]
pub fn contains_key(t: &IntMap<Key, Value>, k: Key) -> bool {
  t.contains_key(k)
}

#[inline(never)]
pub fn prefetch(t: &IntMap<Key, Value>, k: Key) {
  t.prefetch(k)
}

#[inline(never)]
pub fn get(t: &IntMap<Key, Value>, k: Key) -> Option<&Value> {
  t.get(k)
}

#[inline(never)]
pub fn get_value(t: &IntMap<Key, Value>, k: Key) -> Option<Value> {
  match t.get(k) { None => None, Some(&y) => Some(y) }
}

#[inline(never)]
pub fn get_mut(t: &mut IntMap<Key, Value>, k: Key) -> Option<&mut Value> {
  t.get_mut(k)
}

#[inline(never)]
pub fn get_disjoint_mut_0(t: &mut IntMap<Key, Value>, ks: [Key; 0]) -> [Option<&mut Value>; 0] {
  t.get_disjoint_mut(ks)
}

#[inline(never)]
pub fn get_disjoint_mut_4(t: &mut IntMap<Key, Value>, ks: [Key; 4]) -> [Option<&mut Value>; 4] {
  t.get_disjoint_mut(ks)
}

#[inline(never)]
pub fn get_or_insert(t: &mut IntMap<Key, Value>, k: Key) -> &mut Value {
  t.get_or_insert(k, DEFAULT_VALUE)
}

#[inline(never)]
pub fn get_or_insert_with(t: &mut IntMap<Key, Value>, k: Key) -> &mut Value {
  t.get_or_insert_with(k, || DEFAULT_VALUE)
}

#[inline(never)]
pub fn prefetch_get(t: &IntMap<Key, Value>, k: Key) -> Option<&Value> {
  t.prefetch(k);
  t.get(k)
}

#[inline(never)]
pub fn insert(t: &mut IntMap<Key, Value>, k: Key, v: Value) -> Option<Value> {
  t.insert(k, v)
}

#[inline(never)]
pub fn insert0(t: &mut IntMap<Key, Value>, k: Key, v: Value) -> Option<Value> {
  t.insert0(k, v)
}

#[inline(never)]
pub fn remove(t: &mut IntMap<Key, Value>, k: Key) -> Option<Value> {
  t.remove(k)
}

#[inline(never)]
pub fn clear(t: &mut IntMap<Key, Value>) {
  t.clear();
}

#[inline(never)]
pub fn clear_needs_drop(t: &mut IntMap<Key, Box<u32>>) {
  t.clear();
}

#[inline(never)]
pub fn reset(t: &mut IntMap<Key, Value>) {
  t.reset();
}

#[inline(never)]
pub fn reset_needs_drop(t: &mut IntMap<Key, Box<u32>>) {
  t.reset();
}

#[inline(never)]
pub fn clone(t: &IntMap<Key, Value>) -> IntMap<Key, Value> {
  t.clone()
}

#[inline(never)]
pub fn iter(t: &IntMap<Key, Value>) -> impl ExactSizeIterator<Item = (Key, &Value)> {
  t.iter()
}

#[inline(never)]
pub fn values(t: &IntMap<Key, Value>) -> impl ExactSizeIterator<Item = &Value> {
  t.values()
}

#[inline(never)]
pub fn iter_keys_loop(t: &mut IntMap<Key, Value>) -> u32 {
  let mut x = 0;
  for y in t.keys() { x ^= y.get(); }
  x.leading_zeros()
}

#[inline(never)]
pub fn iter_values_fold(t: &mut IntMap<Key, Value>) -> u32 {
  t.values().fold(0, |x, &y| x ^ y.get()).leading_zeros()
}

#[inline(never)]
pub fn iter_values_for_each(t: &mut IntMap<Key, Value>) -> u32 {
  let mut x = 0;
  t.values().for_each(|&y| { x ^= y.get(); });
  x.leading_zeros()
}

#[inline(never)]
pub fn iter_values_loop(t: &mut IntMap<Key, Value>) -> u32 {
  let mut x = 0;
  for &y in t.values() { x ^= y.get(); }
  x.leading_zeros()
}

#[inline(never)]
pub fn num_slots(t: &IntMap<Key, Value>) -> usize {
  tangerine::map::internal::num_slots(t)
}

#[inline(never)]
pub fn probe_count_histogram(t: &IntMap<Key, Value>) -> [usize; 20] {
  tangerine::map::internal::probe_count_histogram(t)
}

#[inline(never)]
pub fn entry(t: &mut IntMap<Key, Value>, key: Key) -> Entry<'_, Key, Value> {
  t.entry(key)
}

#[inline(never)]
pub fn entry_get_mut(t: &mut IntMap<Key, Value>, key: Key) -> Option<&mut Value> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(entry.into_mut()),
    Entry::Vacant(_) => None,
  }
}

#[inline(never)]
pub fn entry_insert(t: &mut IntMap<Key, Value>, key: Key, value: Value) -> Option<Value> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(replace(entry.into_mut(), value)),
    Entry::Vacant(entry) => { let _ = entry.insert(value); None }
  }
}

#[inline(never)]
pub fn entry_try_insert(
    t: &mut IntMap<Key, Value>,
    key: Key,
    value: Value
  ) -> Result<&mut Value, (&mut Value, Value)>
{
  match t.entry(key) {
    Entry::Occupied(entry) => Err((entry.into_mut(), value)),
    Entry::Vacant(entry) => Ok(entry.insert(value)),
  }
}

#[inline(never)]
pub fn entry_remove(t: &mut IntMap<Key, Value>, key: Key) -> Option<Value> {
  match t.entry(key) {
    Entry::Occupied(entry) => Some(entry.remove()),
    Entry::Vacant(_) => None,
  }
}

#[inline(never)]
pub fn entry_inc(t: &mut IntMap<Key, Value>, key: Key) {
  match t.entry(key) {
    Entry::Occupied(mut entry) => {
      let value = entry.get_mut();
      *value = (*value).saturating_add(1);
    }
    Entry::Vacant(e) => {
      let _ = e.insert(DEFAULT_VALUE);
    }
  }
}

#[inline(never)]
pub fn entry_dec(t: &mut IntMap<Key, Value>, key: Key) {
  match t.entry(key) {
    Entry::Occupied(mut entry) => {
      let value = entry.get_mut();
      match Value::new((*value).get() - 1) {
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

#[inline(never)]
pub fn std_remove(t: &mut std::collections::HashMap<Key, Value, foldhash::fast::RandomState>, k: Key) -> Option<Value> {
  t.remove(&k)
}

#[inline(never)]
pub fn std_insert(t: &mut std::collections::HashMap<Key, Value, foldhash::fast::RandomState>, k: Key, v: Value) -> Option<Value> {
  t.insert(k, v)
}
