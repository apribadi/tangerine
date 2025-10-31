#![allow(missing_docs)]

use core::num::NonZeroU64;
use dandelion::Rng;
use tangerine::map::HashMap;
use tangerine::map;

#[inline(never)]
fn new() -> HashMap<NonZeroU64, u32> {
  return HashMap::new();
}

#[inline(never)]
fn new_seeded(rng: &mut Rng) -> HashMap<NonZeroU64, u32> {
  return HashMap::new_seeded(rng);
}

#[inline(never)]
fn len(t: &HashMap<NonZeroU64, u32>) -> usize {
  return t.len();
}

#[inline(never)]
fn is_empty(t: &HashMap<NonZeroU64, u32>) -> bool {
  return t.is_empty();
}

#[inline(never)]
fn contains_key(t: &HashMap<NonZeroU64, u32>, k: NonZeroU64) -> bool {
  return t.contains_key(k);
}

#[inline(never)]
fn get(t: &HashMap<NonZeroU64, u32>, k: NonZeroU64) -> Option<&u32> {
  return t.get(k);
}

#[inline(never)]
fn get_value(t: &HashMap<NonZeroU64, u32>, k: NonZeroU64) -> u32 {
  return match t.get(k) { None => 0, Some(v) => *v, };
}

#[inline(never)]
fn get_mut(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64) -> Option<&mut u32> {
  return t.get_mut(k);
}

#[inline(never)]
fn insert(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64, v: u32) -> Option<u32> {
  return t.insert(k, v);
}

#[inline(never)]
fn insert_drop(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64, v: u32) {
  let _ = t.insert(k, v);
}

#[inline(never)]
fn remove(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64) -> Option<u32> {
  return t.remove(k);
}

#[inline(never)]
fn remove_drop(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64) {
  let _ = t.remove(k);
}

#[inline(never)]
fn clear(t: &mut HashMap<NonZeroU64, u32>) {
  t.clear();
}

#[inline(never)]
fn reset(t: &mut HashMap<NonZeroU64, u32>) {
  t.reset();
}

#[inline(never)]
fn index(t: &HashMap<NonZeroU64, u32>, k: NonZeroU64) -> &u32 {
  return &t[k];
}

#[inline(never)]
fn index_mut(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64) -> &mut u32 {
  return &mut t[k];
}

#[inline(never)]
fn num_slots(t: &HashMap<NonZeroU64, u32>) -> usize {
  return map::internal::num_slots(t);
}

#[inline(never)]
fn allocation_size(t: &HashMap<NonZeroU64, u32>) -> usize {
  return map::internal::allocation_size(t);
}

#[inline(never)]
pub fn load_factor(t: &HashMap<NonZeroU64, u32>) -> f64 {
  return map::internal::load_factor(t);
}

fn main() {
  std::hint::black_box(new);
  std::hint::black_box(load_factor);
}
