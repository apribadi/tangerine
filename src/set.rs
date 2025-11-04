//! This module provides a fast hash set containing types representable as
//! `NonZeroU32` or `NonZeroU64`.

use core::iter::ExactSizeIterator;
use core::iter::FusedIterator;
use rand_core::RngCore;

use crate::key::Key;
use crate::map::HashMap;
use crate::map;

/// A fast hash set containing types representable as `NonZeroU32` or
/// `NonZeroU64`.

pub struct HashSet<T: Key> {
  map: HashMap<T, ()>,
}

impl<T: Key> HashSet<T> {
  /// Creates an empty set, seeding the hash function from a thread-local
  /// random number generator.

  pub fn new() -> Self {
    return Self { map: HashMap::new() };
  }

  /// Creates an empty set, seeding the hash function from the given random
  /// number generator.

  pub fn new_seeded(rng: &mut impl RngCore) -> Self {
    return Self { map: HashMap::new_seeded(rng) };
  }

  /// Returns the number of values.

  #[inline(always)]
  pub fn len(&self) -> usize {
    return self.map.len();
  }

  /// Returns whether the set contains zero values.

  #[inline(always)]
  pub fn is_empty(&self) -> bool {
    return self.map.is_empty();
  }

  /// Returns whether the set contains the given value.

  #[inline(always)]
  pub fn contains(&self, value: T) -> bool {
    return self.map.contains_key(value);
  }

  /// Inserts the given value into the set. Returns `true` if the value was
  /// already present, and `false` if it was not.

  #[inline(always)]
  pub fn insert(&mut self, value: T) -> bool {
    return self.map.insert(value, ()).is_some();
  }

  /// Removes the given value from the set. Returns `true` if the value was
  /// present, and `false` if it was not.

  #[inline(always)]
  pub fn remove(&mut self, value: T) -> bool {
    return self.map.remove(value).is_some();
  }

  /// Removes every item from the set. Retains heap-allocated memory.

  pub fn clear(&mut self) {
    self.map.clear();
  }

  /// Removes every item from the set. Releases heap-allocated memory.

  pub fn reset(&mut self) {
    self.map.reset();
  }

  /// Returns an iterator yielding each value from the set. The iterator item
  /// type is `T`.

  pub fn iter(&self) -> Iter<'_, T> {
    return Iter { keys: self.map.keys() };
  }
}

/// Iterator returned by [`HashSet::iter`].

#[derive(Clone)]
pub struct Iter<'a, T: Key> {
  keys: map::Keys<'a, T, ()>,
}

impl<'a, T: Key> Iterator for Iter<'a, T> {
  type Item = T;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    return self.keys.next();
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    return self.keys.size_hint();
  }
}

impl<'a, T: Key> ExactSizeIterator for Iter<'a, T> {
  #[inline(always)]
  fn len(&self) -> usize {
    return self.keys.len();
  }
}

impl<'a, T: Key> FusedIterator for Iter<'a, T> {
}

impl<T: Key> Default for HashSet<T> {
  fn default() -> Self {
    return Self { map: HashMap::default() };
  }
}

pub mod internal {
  //! Unstable API exposing implementation details for benchmarks and tests.

  #![allow(missing_docs)]

  use super::*;

  pub fn num_slots<T: Key>(t: &HashSet<T>) -> usize {
    return map::internal::num_slots(&t.map);
  }

  pub fn allocation_size<T: Key>(t: &HashSet<T>) -> usize {
    return map::internal::allocation_size(&t.map);
  }

  pub fn load_factor<T: Key>(t: &HashSet<T>) -> f64 {
    return map::internal::load_factor(&t.map);
  }
}
