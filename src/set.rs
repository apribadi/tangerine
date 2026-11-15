//! This module provides a high performance hash set containing types
//! representable as non-zero integers.

use alloc::alloc::Allocator;
use alloc::alloc::Global;
use alloc::boxed::Box;
use core::fmt::Debug;
use core::fmt::Formatter;
use core::fmt;
use core::iter::ExactSizeIterator;
use rand_core::Rng;
use crate::key::Key;
use crate::map::IntMap;

/// A high performance hash set containing types representable as non-zero
/// integers.
pub struct IntSet<T: Key, A: Allocator = Global> {
  map: IntMap<T, (), A>,
}

impl<T: Key> IntSet<T> {
  /// Creates an empty set, seeding the hash function from a thread-local
  /// random number generator.
  pub fn new() -> Self {
    Self { map: IntMap::new() }
  }

  /// Creates an empty set, seeding the hash function from the given random
  /// number generator.
  pub fn with_seed(rng: &mut impl Rng) -> Self {
    Self { map: IntMap::with_seed(rng) }
  }
}

impl<T: Key, A: Allocator> IntSet<T, A> {
  /// Creates an empty set. The hash function is seeded from a thread-local
  /// random number generator. The set uses the given allocator.
  pub fn new_in(alloc: A) -> Self {
    Self { map: IntMap::new_in(alloc) }
  }

  /// Creates an empty set. The hash function is seeded from the given random
  /// number generator. The set uses the given allocator.
  pub fn with_seed_in(rng: &mut impl Rng, alloc: A) -> Self {
    Self { map: IntMap::with_seed_in(rng, alloc) }
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
  pub fn iter(&self) -> impl ExactSizeIterator<Item = T> + use<'_, T, A> {
    self.map.keys()
  }
}

impl<T: Key, A: Allocator + Clone> Clone for IntSet<T, A> {
  fn clone(&self) -> Self {
    Self { map: self.map.clone() }
  }
}

impl<T: Key + Debug + Ord, A: Allocator> Debug for IntSet<T, A> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    let mut a = self.iter().collect::<Box<[T]>>();
    a.sort();
    f.debug_set().entries(a).finish()
  }
}

impl<T: Key, A: Allocator + Default> Default for IntSet<T, A> {
  fn default() -> Self {
    Self { map: IntMap::default() }
  }
}

impl<T: Key, A: Allocator> Extend<T> for IntSet<T, A> {
  fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
    iter.into_iter().for_each(|x| { let _: bool = self.insert(x); });
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
