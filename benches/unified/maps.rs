use std::num::NonZeroU32;

pub(crate) trait Map<T> {
  fn new() -> Self;

  fn len(&self) -> usize;

  fn get(&self, _: NonZeroU32) -> Option<&T>;

  fn insert(&mut self, _: NonZeroU32, _: T) -> Option<T>;

  fn remove(&mut self, _: NonZeroU32) -> Option<T>;

  fn for_each_value<F: FnMut(&T)>(&self, f: F);
}

impl<K, V> Map<V> for tangerine::map::IntMap<K, V>
where
  K: tangerine::key::Key + From<NonZeroU32>
{
  #[inline(always)]
  fn new() -> Self {
    tangerine::map::IntMap::new()
  }

  #[inline(always)]
  fn len(&self) -> usize {
    tangerine::map::IntMap::len(self)
  }

  #[inline(always)]
  fn get(&self, k: NonZeroU32) -> Option<&V> {
    tangerine::map::IntMap::get(self, K::from(k))
  }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU32, v: V) -> Option<V> {
    tangerine::map::IntMap::insert(self, K::from(k), v)
  }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU32) -> Option<V> {
    tangerine::map::IntMap::remove(self, K::from(k))
  }

  #[inline(always)]
  fn for_each_value<F: FnMut(&V)>(&self, f: F) {
    tangerine::map::IntMap::values(self).for_each(f)
  }
}

impl<K, V, S> Map<V> for std::collections::HashMap<K, V, S>
where
  K: std::hash::Hash + Copy + Eq + From<NonZeroU32>,
  S: std::hash::BuildHasher + Default,
{
  #[inline(always)]
  fn new() -> Self {
    std::collections::HashMap::with_hasher(S::default())
  }

  #[inline(always)]
  fn len(&self) -> usize {
    std::collections::HashMap::len(self)
  }

  #[inline(always)]
  fn get(&self, k: NonZeroU32) -> Option<&V> {
    std::collections::HashMap::get(self, &K::from(k))
  }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU32, v: V) -> Option<V> {
    std::collections::HashMap::insert(self, K::from(k), v)
  }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU32) -> Option<V> {
    std::collections::HashMap::remove(self, &K::from(k))
  }

  #[inline(always)]
  fn for_each_value<F: FnMut(&V)>(&self, f: F) {
    std::collections::HashMap::values(self).for_each(f)
  }
}

impl<K, V> Map<V> for intmap::IntMap<K, V>
where
  K: intmap::IntKey + From<NonZeroU32>
{
  #[inline(always)]
  fn new() -> Self {
    intmap::IntMap::new()
  }

  #[inline(always)]
  fn len(&self) -> usize {
    intmap::IntMap::len(self)
  }

  #[inline(always)]
  fn get(&self, k: NonZeroU32) -> Option<&V> {
    intmap::IntMap::get(self, K::from(k))
  }

  #[inline(always)]
  fn insert(&mut self, k: NonZeroU32, v: V) -> Option<V> {
    intmap::IntMap::insert(self, K::from(k), v)
  }

  #[inline(always)]
  fn remove(&mut self, k: NonZeroU32) -> Option<V> {
    intmap::IntMap::remove(self, K::from(k))
  }

  #[inline(always)]
  fn for_each_value<F: FnMut(&V)>(&self, f: F) {
    intmap::IntMap::values(self).for_each(f)
  }
}
