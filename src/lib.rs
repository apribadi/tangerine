pub mod map;

use dandelion::Rng;
use map::HashMap;
use core::num::NonZeroU64;

#[inline(never)]
pub fn new() -> HashMap<NonZeroU64, u32> {
  HashMap::new()
}

#[inline(never)]
pub fn new_seeded(rng: &mut Rng) -> HashMap<NonZeroU64, u32> {
  HashMap::new_seeded(rng)
}

#[inline(never)]
pub fn len(t: &HashMap<NonZeroU64, u32>) -> usize {
  t.len()
}

#[inline(never)]
pub fn is_empty(t: &HashMap<NonZeroU64, u32>) -> bool {
  t.is_empty()
}

#[inline(never)]
pub fn contains_key(t: &HashMap<NonZeroU64, u32>, k: NonZeroU64) -> bool {
  t.contains_key(k)
}

#[inline(never)]
pub fn get(t: &HashMap<NonZeroU64, u32>, k: NonZeroU64) -> Option<&u32> {
  t.get(k)
}

#[inline(never)]
pub fn get_value(t: &HashMap<NonZeroU64, u32>, k: NonZeroU64) -> u32 {
  match t.get(k) { None => 0, Some(v) => *v, }
}

#[inline(never)]
pub fn get_mut(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64) -> Option<&mut u32> {
  t.get_mut(k)
}

#[inline(never)]
pub fn insert(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64, v: u32) -> Option<u32> {
  t.insert(k, v)
}

#[inline(never)]
pub fn insert_drop(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64, v: u32) {
  let _: _ = t.insert(k, v);
}

#[inline(never)]
pub fn remove(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64) -> Option<u32> {
  t.remove(k)
}

#[inline(never)]
pub fn remove_drop(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64) {
  let _: _ = t.remove(k);
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
  &t[k]
}

#[inline(never)]
pub fn index_mut(t: &mut HashMap<NonZeroU64, u32>, k: NonZeroU64) -> &mut u32 {
  &mut t[k]
}

#[inline(never)]
pub fn num_slots(t: &HashMap<NonZeroU64, u32>) -> usize {
  map::internal::num_slots(t)
}

#[inline(never)]
pub fn num_bytes(t: &HashMap<NonZeroU64, u32>) -> usize {
  map::internal::num_bytes(t)
}

#[inline(never)]
pub fn load_factor(t: &HashMap<NonZeroU64, u32>) -> f64 {
  map::internal::load_factor(t)
}

/*
#[inline(never)]
pub fn foo(h: u64, w: usize) -> usize {
  <NonZeroU64 as map::Key>::slot(h, w)
}

#[inline(never)]
pub fn bar(t: &HashMap<NonZeroU64, u32>) -> usize {
  t.num_slots()
}
*/
