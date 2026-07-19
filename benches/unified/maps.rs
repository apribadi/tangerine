pub(crate) trait Map<K, V> {
  fn new() -> Self;

  fn len(&self) -> usize;

  fn get(&self, _: K) -> Option<&V>;

  fn insert(&mut self, _: K, _: V);

  fn remove(&mut self, _: K) -> Option<V>;

  fn for_each_value<F: FnMut(&V)>(&self, f: F);
}

impl<T, U, V> Map<T, V> for tangerine::map::IntMap<U, V>
where
  T: Into<U>,
  U: tangerine::key::Key,
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
    tangerine::map::IntMap::get(self, k.into())
  }

  #[inline(always)]
  fn insert(&mut self, k: T, v: V) {
    let _: Option<_> = tangerine::map::IntMap::insert(self, k.into(), v);
  }

  #[inline(always)]
  fn remove(&mut self, k: T) -> Option<V> {
    tangerine::map::IntMap::remove(self, k.into())
  }

  #[inline(always)]
  fn for_each_value<F: FnMut(&V)>(&self, f: F) {
    tangerine::map::IntMap::values(self).for_each(f)
  }
}

impl<T, U, V, S> Map<T, V> for std::collections::HashMap<U, V, S>
where
  T: Into<U>,
  U: std::hash::Hash + Copy + Eq,
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
    std::collections::HashMap::get(self, &k.into())
  }

  #[inline(always)]
  fn insert(&mut self, k: T, v: V) {
    let _: Option<_> = std::collections::HashMap::insert(self, k.into(), v);
  }

  #[inline(always)]
  fn remove(&mut self, k: T) -> Option<V> {
    std::collections::HashMap::remove(self, &k.into())
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
  fn insert(&mut self, k: K, v: V) {
    let _: Option<_> = intmap::IntMap::insert(self, K::from(k), v);
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

impl<K, V> Map<K, V> for sparse_hash_map::SparseMap<K, V>
where
  K: std::hash::Hash + Copy + Eq,
{
  #[inline(always)]
  fn new() -> Self {
    sparse_hash_map::SparseMap::new()
  }

  #[inline(always)]
  fn len(&self) -> usize {
    sparse_hash_map::SparseMap::len(self)
  }

  #[inline(always)]
  fn get(&self, k: K) -> Option<&V> {
    sparse_hash_map::SparseMap::get(self, &K::from(k))
  }

  #[inline(always)]
  fn insert(&mut self, k: K, v: V) {
    let _: (_, bool) = sparse_hash_map::SparseMap::insert_or_assign(self, K::from(k), v);
  }

  #[inline(always)]
  fn remove(&mut self, k: K) -> Option<V> {
    sparse_hash_map::SparseMap::remove(self, &K::from(k))
  }

  #[inline(always)]
  fn for_each_value<F: FnMut(&V)>(&self, f: F) {
    sparse_hash_map::SparseMap::values(self).for_each(f)
  }
}
