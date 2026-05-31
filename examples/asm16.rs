#![allow(missing_docs)]

use std::num::NonZeroU16;
use tangerine::map::IntMap;

#[inline(never)]
pub fn get_value(t: &IntMap<NonZeroU16, NonZeroU16>, k: NonZeroU16) -> Option<NonZeroU16> {
  match t.get(k) { None => None, Some(&y) => Some(y) }
}

#[inline(never)]
pub fn insert(t: &mut IntMap<NonZeroU16, NonZeroU16>, k: NonZeroU16, v: NonZeroU16) -> Option<NonZeroU16> {
  t.insert(k, v)
}

#[inline(never)]
pub fn remove(t: &mut IntMap<NonZeroU16, NonZeroU16>, k: NonZeroU16) -> Option<NonZeroU16> {
  t.remove(k)
}

