use std::num::NonZeroU32;

pub(crate) trait Map<T> {
  fn new() -> Self;

  fn len(&self) -> usize;

  fn get(&self, _: NonZeroU32) -> Option<&T>;

  fn insert(&mut self, _: NonZeroU32, _: T) -> Option<T>;

  fn remove(&mut self, _: NonZeroU32) -> Option<T>;
}

impl<T> Map<T> for tangerine::map::HashMap<NonZeroU32, T> {
  #[inline(always)]
  fn new() -> Self { tangerine::map::HashMap::new() }

  #[inline(always)]
  fn len(&self) -> usize { self.len() }

  #[inline(always)]
  fn get(&self, k: NonZeroU32) -> Option<&T> { self.get(k) }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU32, v: T) -> Option<T> { self.insert(k, v) }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU32) -> Option<T> { self.remove(k) }
}

impl<T> Map<T> for ahash::AHashMap<NonZeroU32, T> {
  #[inline(always)]
  fn new() -> Self { ahash::AHashMap::new() }

  #[inline(always)]
  fn len(&self) -> usize {
    let t: &std::collections::HashMap<_, _, _> = &self;
    t.len()
  }

  #[inline(always)]
  fn get(&self, k: NonZeroU32) -> Option<&T> { self.get(&k) }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU32, v: T) -> Option<T> { self.insert(k, v) }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU32) -> Option<T> { self.remove(&k) }
}

impl<T> Map<T> for foldhash::HashMap<NonZeroU32, T> {
  #[inline(always)]
  fn new() -> Self { <foldhash::HashMap<_, _> as foldhash::HashMapExt>::new() }

  #[inline(always)]
  fn len(&self) -> usize { self.len() }

  #[inline(always)]
  fn get(&self, k: NonZeroU32) -> Option<&T> { self.get(&k) }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU32, v: T) -> Option<T> { self.insert(k, v) }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU32) -> Option<T> { self.remove(&k) }
}
