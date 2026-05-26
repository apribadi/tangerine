pub(crate) trait Map<K, V> {
  fn new() -> Self;

  fn len(&self) -> usize;

  fn get(&self, _: K) -> Option<&V>;

  fn insert(&mut self, _: K, _: V) -> Option<V>;

  fn remove(&mut self, _: K) -> Option<V>;

  fn for_each_value<F: FnMut(&V)>(&self, f: F);
}

impl<T, U, V> Map<T, V> for tangerine::map::IntMap<U, V>
where
  U: tangerine::key::Key + From<T>
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
  fn get(&self, k: T) -> Option<&V> {
    tangerine::map::IntMap::get(self, U::from(k))
  }

  #[inline(always)]
  fn insert(&mut self, k: T, v: V) -> Option<V> {
    tangerine::map::IntMap::insert(self, U::from(k), v)
  }

  #[inline(always)]
  fn remove(&mut self, k: T) -> Option<V> {
    tangerine::map::IntMap::remove(self, U::from(k))
  }

  #[inline(always)]
  fn for_each_value<F: FnMut(&V)>(&self, f: F) {
    tangerine::map::IntMap::values(self).for_each(f)
  }
}

impl<T, U, V, S> Map<T, V> for std::collections::HashMap<U, V, S>
where
  U: std::hash::Hash + Copy + Eq + From<T>,
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
  fn get(&self, k: T) -> Option<&V> {
    std::collections::HashMap::get(self, &U::from(k))
  }

  #[inline(always)]
  fn insert(&mut self, k: T, v: V) -> Option<V> {
    std::collections::HashMap::insert(self, U::from(k), v)
  }

  #[inline(always)]
  fn remove(&mut self, k: T) -> Option<V> {
    std::collections::HashMap::remove(self, &U::from(k))
  }

  #[inline(always)]
  fn for_each_value<F: FnMut(&V)>(&self, f: F) {
    std::collections::HashMap::values(self).for_each(f)
  }
}

impl<K, V> Map<K, V> for intmap::IntMap<K, V>
where
  K: intmap::IntKey
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
  fn get(&self, k: K) -> Option<&V> {
    intmap::IntMap::get(self, K::from(k))
  }

  #[inline(always)]
  fn insert(&mut self, k: K, v: V) -> Option<V> {
    intmap::IntMap::insert(self, K::from(k), v)
  }

  #[inline(always)]
  fn remove(&mut self, k: K) -> Option<V> {
    intmap::IntMap::remove(self, K::from(k))
  }

  #[inline(always)]
  fn for_each_value<F: FnMut(&V)>(&self, f: F) {
    intmap::IntMap::values(self).for_each(f)
  }
}
