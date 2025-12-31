use std::num::NonZeroU64;

pub(crate) trait Map {
  fn new() -> Self;

  fn insert(&mut self, _: NonZeroU64, _: u64);

  fn remove(&mut self, _: NonZeroU64);
}

impl Map for tangerine::map::HashMap<NonZeroU64, u64> {
  #[inline(always)]
  fn new() -> Self { tangerine::map::HashMap::new() }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU64, v: u64) { self.insert(k, v); }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU64) { self.remove(k); }
}

impl Map for ahash::AHashMap<NonZeroU64, u64> {
  #[inline(always)]
  fn new() -> Self { ahash::AHashMap::new() }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU64, v: u64) { let _: Option<_> = self.insert(k, v); }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU64) { let _: Option<_> = self.remove(&k); }
}

impl Map for foldhash::HashMap<NonZeroU64, u64> {
  #[inline(always)]
  fn new() -> Self { <foldhash::HashMap<_, _> as foldhash::HashMapExt>::new() }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU64, v: u64) { let _: Option<_> = self.insert(k, v); }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU64) { let _: Option<_> = self.remove(&k); }
}
