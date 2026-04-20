//! This module provides a fast hash set containing types representable as
//! `NonZeroU32` or `NonZeroU64`.

use core::fmt::Debug;
use core::iter::ExactSizeIterator;
use rand_core::RngCore;

use crate::key::Key;
use crate::map::IntMap;

/// A fast hash set containing types representable as `NonZeroU32` or
/// `NonZeroU64`.
pub struct IntSet<T: Key> {
  map: IntMap<T, ()>,
}

impl<T: Key> IntSet<T> {
  /// Creates an empty set, seeding the hash function from a thread-local
  /// random number generator.
  pub fn new() -> Self {
    Self { map: IntMap::new() }
  }

  /// Creates an empty set, seeding the hash function from the given random
  /// number generator.
  pub fn new_seeded(rng: &mut impl RngCore) -> Self {
    Self { map: IntMap::new_seeded(rng) }
  }

  /// Returns the number of values.
  #[inline(always)]
  pub fn len(&self) -> usize {
    self.map.len()
  }

  /// Returns whether the set contains zero values.
  #[inline(always)]
  pub fn is_empty(&self) -> bool {
    self.map.is_empty()
  }

  /// Returns whether the set contains the given value.
  #[inline(always)]
  pub fn contains(&self, value: T) -> bool {
    self.map.contains_key(value)
  }

  /// Inserts the given value into the set. Returns whether the set already
  /// contained the given value.
  #[inline(always)]
  pub fn insert(&mut self, value: T) -> bool {
    match self.map.insert(value, ()) {
      None => false,
      Some(()) => true,
    }
  }

  /// Removes the given value from the set. Returns whether the set previously
  /// contained the given value.
  #[inline(always)]
  pub fn remove(&mut self, value: T) -> bool {
    match self.map.remove(value) {
      None => false,
      Some(()) => true,
    }
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
  #[inline(always)]
  pub fn iter(&self) -> impl ExactSizeIterator<Item = T> + use<'_, T> {
    self.map.keys()
  }
}

impl<T: Key> Clone for IntSet<T> {
  fn clone(&self) -> Self {
    Self { map: self.map.clone() }
  }
}

impl <T: Key + Debug + Ord> Debug for IntSet<T> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let mut a = self.iter().collect::<Box<[T]>>();
    a.sort();
    f.debug_set().entries(a).finish()
  }
}

impl<T: Key> Default for IntSet<T> {
  fn default() -> Self {
    Self::new()
  }
}

impl<T: Key> Extend<T> for IntSet<T> {
  fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
    iter.into_iter().for_each(|x| { let _: bool = self.insert(x); });
  }

  #[cfg(feature = "nightly")]
  #[inline(always)]
  fn extend_one(&mut self, item: T) {
    let _: bool = self.insert(item);
  }
}

impl<const N: usize, T: Key> From<[T; N]> for IntSet<T> {
  fn from(value: [T; N]) -> Self {
    Self::from_iter(value)
  }
}

impl<T: Key> FromIterator<T> for IntSet<T> {
  fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
    let mut t = Self::new();
    t.extend(iter);
    t
  }
}
