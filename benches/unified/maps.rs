#![allow(unused)]
use std::num::NonZeroU32;

pub(crate) trait Map<T> {
  fn new() -> Self;

  fn len(&self) -> usize;

  fn get(&self, _: NonZeroU32) -> Option<&T>;

  fn insert(&mut self, _: NonZeroU32, _: T) -> Option<T>;

  fn remove(&mut self, _: NonZeroU32) -> Option<T>;

  fn for_each<F: FnMut((NonZeroU32, &T))>(&self, f: F);
}

impl<T> Map<T> for tangerine::map::IntMap<NonZeroU32, T> {
  #[inline(always)]
  fn new() -> Self { tangerine::map::IntMap::new() }

  #[inline(always)]
  fn len(&self) -> usize { self.len() }

  #[inline(always)]
  fn get(&self, k: NonZeroU32) -> Option<&T> { self.get(k) }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU32, v: T) -> Option<T> { self.insert(k, v) }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU32) -> Option<T> { self.remove(k) }

  fn for_each<F: FnMut((NonZeroU32, &T))>(&self, f: F) { self.iter().for_each(f) }
}

impl<T, S: Default + std::hash::BuildHasher> Map<T> for std::collections::HashMap<NonZeroU32, T, S> {
  #[inline(always)]
  fn new() -> Self { std::collections::HashMap::with_hasher(S::default()) }

  #[inline(always)]
  fn len(&self) -> usize { self.len() }

  #[inline(always)]
  fn get(&self, k: NonZeroU32) -> Option<&T> { self.get(&k) }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU32, v: T) -> Option<T> { self.insert(k, v) }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU32) -> Option<T> { self.remove(&k) }

  fn for_each<F: FnMut((NonZeroU32, &T))>(&self, mut f: F) { self.iter().for_each(|(&x, y)| f((x, y))) }
}
