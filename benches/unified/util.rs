use std::num::NonZeroU64;

pub(crate) trait Map<T> {
  fn new() -> Self;

  fn get(&self, _: NonZeroU64) -> Option<&T>;

  fn insert(&mut self, _: NonZeroU64, _: T);

  fn remove(&mut self, _: NonZeroU64);
}

impl<T> Map<T> for tangerine::map::HashMap<NonZeroU64, T> {
  #[inline(always)]
  fn new() -> Self { tangerine::map::HashMap::new() }

  #[inline(always)]
  fn get(&self, k: NonZeroU64) -> Option<&T> { self.get(k) }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU64, v: T) { self.insert(k, v); }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU64) { self.remove(k); }
}

impl<T> Map<T> for tangerine::two::HashMap<T> {
  #[inline(always)]
  fn new() -> Self { tangerine::two::HashMap::new() }

  #[inline(always)]
  fn get(&self, k: NonZeroU64) -> Option<&T> { self.get(k) }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU64, v: T) { let _ = self.insert(k, v); }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU64) { let _ = self.remove(k); }
}

impl<T> Map<T> for ahash::AHashMap<NonZeroU64, T> {
  #[inline(always)]
  fn new() -> Self { ahash::AHashMap::new() }

  #[inline(always)]
  fn get(&self, k: NonZeroU64) -> Option<&T> { self.get(&k) }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU64, v: T) { let _: Option<_> = self.insert(k, v); }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU64) { let _: Option<_> = self.remove(&k); }
}

impl<T> Map<T> for foldhash::HashMap<NonZeroU64, T> {
  #[inline(always)]
  fn new() -> Self { <foldhash::HashMap<_, _> as foldhash::HashMapExt>::new() }

  #[inline(always)]
  fn get(&self, k: NonZeroU64) -> Option<&T> { self.get(&k) }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU64, v: T) { let _: Option<_> = self.insert(k, v); }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU64) { let _: Option<_> = self.remove(&k); }
}
