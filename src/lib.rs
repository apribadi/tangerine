pub mod map;

use dandelion::Rng;
use map::HashMapNZ64;
use core::num::NonZeroU64;

#[inline(never)]
pub fn u32_new() -> HashMapNZ64<u32> {
  HashMapNZ64::new()
}

#[inline(never)]
pub fn u32_new_seeded(rng: &mut Rng) -> HashMapNZ64<u32> {
  HashMapNZ64::new_seeded(rng)
}

#[inline(never)]
pub fn u32_len(t: &HashMapNZ64<u32>) -> usize {
  t.len()
}

#[inline(never)]
pub fn u32_is_empty(t: &HashMapNZ64<u32>) -> bool {
  t.is_empty()
}

#[inline(never)]
pub fn u32_contains_key(t: &HashMapNZ64<u32>, k: NonZeroU64) -> bool {
  t.contains_key(k)
}

#[inline(never)]
pub fn u32_get(t: &HashMapNZ64<u32>, k: NonZeroU64) -> Option<&u32> {
  t.get(k)
}

#[inline(never)]
pub fn u32_get_value(t: &HashMapNZ64<u32>, k: NonZeroU64) -> u32 {
  match t.get(k) { None => 0, Some(v) => *v, }
}

#[inline(never)]
pub fn u32_get_mut(t: &mut HashMapNZ64<u32>, k: NonZeroU64) -> Option<&mut u32> {
  t.get_mut(k)
}

#[inline(never)]
pub fn u32_insert(t: &mut HashMapNZ64<u32>, k: NonZeroU64, v: u32) -> Option<u32> {
  t.insert(k, v)
}

#[inline(never)]
pub fn u32_insert_drop(t: &mut HashMapNZ64<u32>, k: NonZeroU64, v: u32) {
  let _: _ = t.insert(k, v);
}

#[inline(never)]
pub fn u32_remove(t: &mut HashMapNZ64<u32>, k: NonZeroU64) -> Option<u32> {
  t.remove(k)
}

#[inline(never)]
pub fn u32_remove_drop(t: &mut HashMapNZ64<u32>, k: NonZeroU64) {
  let _: _ = t.remove(k);
}

#[inline(never)]
pub fn u32_remove_hash(t: &mut HashMapNZ64<u32>, k: NonZeroU64) -> u32 {
  let m = k.get() as u32;
  let v =
    match t.remove(k) {
      None => 0,
      Some(v) => v,
    };
  let v = v.wrapping_mul(m).swap_bytes();
  let v = v.wrapping_mul(m).swap_bytes();
  let v = v.wrapping_mul(m).swap_bytes();
  let v = v.wrapping_mul(m).swap_bytes();
  let v = v.wrapping_mul(m).swap_bytes();
  let v = v.wrapping_mul(m).swap_bytes();
  let v = v.wrapping_mul(m).swap_bytes();
  let v = v.wrapping_mul(m).swap_bytes();
  let v = v.wrapping_mul(m).swap_bytes();
  let v = v.wrapping_mul(m).swap_bytes();
  v
}

#[inline(never)]
pub fn u32_clear(t: &mut HashMapNZ64<u32>) {
  t.clear();
}

#[inline(never)]
pub fn u32_reset(t: &mut HashMapNZ64<u32>) {
  t.reset();
}

#[inline(never)]
pub fn u32_internal_num_slots(t: &HashMapNZ64<u32>) -> usize {
  map::internal::num_slots(t)
}

#[inline(never)]
pub fn u32_internal_num_bytes(t: &HashMapNZ64<u32>) -> usize {
  map::internal::num_bytes(t)
}

#[inline(never)]
pub fn u32_internal_load(t: &HashMapNZ64<u32>) -> f64 {
  map::internal::load(t)
}
