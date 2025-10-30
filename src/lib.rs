#![doc = include_str!("../README.md")]

pub mod key;
pub mod map;

// TODO: set

/*
use core::num::NonZeroU64;
use dandelion::Rng;
use map::HashMap;

#[inline(never)]
pub fn new() -> HashMap<NonZeroU64, u32> {
  return HashMap::new();
}

#[inline(never)]
pub fn new_seeded(rng: &mut Rng) -> HashMap<NonZeroU64, u32> {
  return HashMap::new_seeded(rng);
}

#[inline(never)]
pub fn len(t: &HashMap<NonZeroU64, u32>) -> usize {
  return t.len();
}

#[inline(never)]
pub fn is_empty(t: &HashMap<NonZeroU64, u32>) -> bool {
  return t.is_empty();
}

#[inline(never)]
pub fn contains_key(t: &HashMap<NonZeroU64, u32>, k: NonZeroU64) -> bool {
  return t.contains_key(k);
}

#[inline(never)]
pub fn get(t: &HashMap<NonZeroU64, u32>, k: NonZeroU64) -> Option<&u32> {
  return t.get(k);
}

#[inline(never)]
pub fn get_value(t: &HashMap<NonZeroU64, u32>, k: NonZeroU64) -> u32 {
  return match t.get(k) { None => 0, Some(v) => *v, };
}

#[inline(never)]
pub fn get_mut(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64) -> Option<&mut u32> {
  return t.get_mut(k);
}

#[inline(never)]
pub fn insert(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64, v: u32) -> Option<u32> {
  return t.insert(k, v);
}

#[inline(never)]
pub fn insert_drop(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64, v: u32) {
  let _ = t.insert(k, v);
}

#[inline(never)]
pub fn remove(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64) -> Option<u32> {
  return t.remove(k);
}

#[inline(never)]
pub fn remove_drop(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64) {
  let _ = t.remove(k);
}

#[inline(never)]
pub fn clear(t: &mut HashMap<NonZeroU64, u32>) {
  t.clear();
}

#[inline(never)]
pub fn reset(t: &mut HashMap<NonZeroU64, u32>) {
  t.reset();
}

#[inline(never)]
pub fn index(t: &HashMap<NonZeroU64, u32>, k: NonZeroU64) -> &u32 {
  return &t[k];
}

#[inline(never)]
pub fn index_mut(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64) -> &mut u32 {
  return &mut t[k];
}

#[inline(never)]
pub fn num_slots(t: &HashMap<NonZeroU64, u32>) -> usize {
  return map::internal::num_slots(t);
}

#[inline(never)]
pub fn allocation_size(t: &HashMap<NonZeroU64, u32>) -> usize {
  return map::internal::allocation_size(t);
}

#[inline(never)]
pub fn load_factor(t: &HashMap<NonZeroU64, u32>) -> f64 {
  return map::internal::load_factor(t);
}
*/
