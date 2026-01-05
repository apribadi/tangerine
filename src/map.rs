//! This module provides a fast hash map keyed by types representable as
//! `NonZeroU32` or `NonZeroU64`.

// TODO: IntoIterator
// TODO: drain
// TODO: try_insert
// TODO: shrink_to_fit
// TODO: get_or_insert_with

use core::cmp::max;
use core::fmt::Debug;
use core::iter::ExactSizeIterator;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::mem::needs_drop;
use core::mem::offset_of;
use core::ops::Index;
use core::ops::IndexMut;
use pop::global;
use pop::ptr;
use rand_core::RngCore;

use crate::key::Key;

/// A fast hash map keyed by types representable as `NonZeroU32` or
/// `NonZeroU64`.

pub struct HashMap<K: Key, V> {
  seed0: K::Seed,
  seed1: K::Seed,
  table: ptr<Slot<K, V>>, // NB: invariant
  width: usize,
  slack: usize,
  limit: ptr<Slot<K, V>>,
  _phantom_data: PhantomData<(K, V)>
}

// NB: We use `repr(C)` because the `hash` field MUST be at offset zero.

#[repr(C)]
struct Slot<K: Key, V> {
  hash: K::Hash,
  data: MaybeUninit<V>,
}

static EMPTY_TABLE: u64 = 0;

#[inline(always)]
fn capacity(w: usize) -> usize {
  return (w >> 1) - (w >> 3); // ~ 0.375
}

#[inline(always)]
fn log2(n: usize) -> usize {
  debug_assert!(n >= 1);
  return (usize::BITS - 1 - n.leading_zeros()) as usize;
}

// SIZE CLASS MATH
//
// 0           A     B     C           D           E
// |           |     |     |           |           |
//                X              Y
//
// Note that (3 / 2) * (4 / 3) == 2, so increasing a size class by two steps is
// always exactly a factor of two.
//
// We increase our size by just less than a factor of two, and then round down
// to the nearest size class.
//
// This ensures that we increase our size to the smallest size class such that
// we're increasing by at least one size class.

#[inline(always)]
fn increment_size_class(n: usize) -> usize {
  debug_assert!(2 <= n && n <= isize::MAX as usize);
  let n = 2 * n - 1;
  let a = 1 << usize::BITS - 1 - n.leading_zeros();
  let b = a >> 1;
  return a + (n & b);
}

#[inline(always)]
fn slot_hash<K: Key, V>(a: ptr<Slot<K, V>>) -> ptr<K::Hash> {
  return a.cast();
}

#[inline(always)]
fn slot_data<K: Key, V>(a: ptr<Slot<K, V>>) -> ptr<V> {
  // NOTE: We could improve code generation in a few places by
  // `std::hint::assert_unchecked`-ing that the result is non-nuull.
  return a.byte_add(offset_of!(Slot<K, V>, data));
}

impl<K: Key, V> HashMap<K, V> {
  const MAX_NUM_SLOTS: usize = isize::MAX as usize / size_of::<Slot<K, V>>();

  #[inline(always)]
  fn internal_new(m: K::Seed) -> Self {
    Self {
      seed0: m,
      seed1: K::invert_seed(m),
      table: ptr::from(&EMPTY_TABLE).cast(),
      width: 1,
      slack: 0,
      limit: ptr::NULL,
      _phantom_data: PhantomData,
    }
  }

  /// Creates an empty map, seeding the hash function from a thread-local
  /// random number generator.

  pub fn new() -> Self {
    return Self::internal_new(K::seed_nondet());
  }

  /// Creates an empty map, seeding the hash function from the given random
  /// number generator.

  pub fn new_seeded(rng: &mut impl RngCore) -> Self {
    return Self::internal_new(K::seed(rng));
  }

  /// Returns the number of items.

  #[inline(always)]
  pub fn len(&self) -> usize {
    let w = self.width;
    let s = self.slack;

    return capacity(w) - s;
  }

  /// Returns whether the map contains zero items.

  #[inline(always)]
  pub fn is_empty(&self) -> bool {
    return self.len() == 0;
  }

  /// Returns whether the map contains the given key.

  #[inline(always)]
  pub fn contains_key(&self, key: K) -> bool {
    let m = self.seed0;
    let t = self.table;
    let w = self.width;
    let h = K::hash(key, m);

    let mut a = t - K::slot(h, w);
    let mut x = unsafe { slot_hash(a).read() };

    while x > h {
      a = a + 1;
      x = unsafe { slot_hash(a).read() };
    }

    return x == h;
  }

  /// Returns a reference to the value associated with the given key, if
  /// present.

  #[inline(always)]
  pub fn get(&self, key: K) -> Option<&V> {
    let m = self.seed0;
    let t = self.table;
    let w = self.width;
    let h = K::hash(key, m);

    let mut a = t - K::slot(h, w);
    let mut x = unsafe { slot_hash(a).read() };

    while x > h {
      a = a + 1;
      x = unsafe { slot_hash(a).read() };
    }

    if x != h { return None; }

    return Some(unsafe { slot_data(a).as_ref() });
  }

  /// Returns a mutable reference to the value associated with the given key,
  /// if present.

  #[inline(always)]
  pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
    let m = self.seed0;
    let t = self.table;
    let w = self.width;
    let h = K::hash(key, m);

    let mut a = t - K::slot(h, w);
    let mut x = unsafe { slot_hash(a).read() };

    while x > h {
      a = a + 1;
      x = unsafe { slot_hash(a).read() };
    }

    if x != h { return None; }

    return Some(unsafe { slot_data(a).as_mut_ref() });
  }

  #[inline(never)]
  #[cold]
  fn internal_grow(&mut self, last_written_slot: ptr<Slot<K, V>>) {
    // Temporarily place table in a valid state, in case we panic.

    let h = unsafe { slot_hash(last_written_slot).replace(K::ZERO) };

    let old_t = self.table;
    let old_w = self.width;
    let old_s = self.slack.wrapping_add(1);
    let old_l = self.limit;

    self.slack = old_s;

    let old_p = old_t - (old_w - 1);
    let old_e = old_l - old_t;
    let old_d = old_w + old_e;
    let old_c = capacity(old_w);

    // Compute new size.

    let new_d = increment_size_class(old_d * size_of::<Slot<K, V>>()) / size_of::<Slot<K, V>>();
    let new_e = old_e + (log2(new_d) - log2(old_d)) + ((last_written_slot == old_l) as usize);
    let new_w = new_d - new_e;
    let new_c = capacity(new_w);

    // Panic if we would overflow the layout.

    assert!(new_d <= Self::MAX_NUM_SLOTS);

    // Alloc new table.

    let new_p = unsafe { global::alloc_slice::<Slot<K, V>>(new_d) };
    let new_t = new_p + (new_w - 1);
    let new_l = new_p + (new_d - 1);

    // At this point, we know that we can finish growing the table without
    // panicking.

    // Re-add the last written slot, and compute some values that include that
    // slot.

    unsafe { slot_hash(last_written_slot).write(h) };

    let old_n = old_c - old_s + 1;
    let new_s = old_s + (new_c - old_c) - 1;

    // Update struct fields.

    self.table = new_t;
    self.width = new_w;
    self.slack = new_s;
    self.limit = new_l;

    // Zero new table.

    let mut a = new_p;
    let mut k = new_d;

    while k != 0 {
      unsafe { slot_hash(a).write(K::ZERO) };

      a = a + 1;
      k = k - 1;
    }

    // Compress non-empty slots.

    let mut a = old_p;
    let mut b = old_p;
    let mut k = old_d;

    while k != 0 {
      let u = unsafe { a.read() };
      let x = u.hash;
      unsafe { b.write(u) };

      a = a + 1;
      b = b + (x != K::ZERO) as usize;
      k = k - 1;
    }

    // Copy slots to new allocated block.

    let mut a = old_p;
    let mut b = new_p;
    let mut k = old_n;

    while k != 0 {
      let u = unsafe { a.read() };
      let x = u.hash;
      b = max(b, new_t - K::slot(x, new_w));
      unsafe { b.write(u) };

      a = a + 1;
      b = b + 1;
      k = k - 1;
    }

    // The map is now in a valid state, even if deallocating panics.

    unsafe { global::dealloc_slice(old_p, old_d) };
  }

  #[inline(never)]
  #[cold]
  fn internal_init(&mut self, h: K::Hash, value: V) {
    // Initialize table, then insert.

    let w = 13;
    let e = 3;
    let d = w + e;

    assert!(d <= Self::MAX_NUM_SLOTS);

    let p = unsafe { global::alloc_slice::<Slot<K, V>>(d) };

    let mut a = p;
    let mut k = d;

    while k != 0 {
      unsafe { slot_hash(a).write(K::ZERO) };

      a = a + 1;
      k = k - 1;
    }

    let t = p + (w - 1);
    let l = p + (d - 1);
    let a = t - K::slot(h, w);

    unsafe { slot_hash(a).write(h) };
    unsafe { slot_data(a).write(value) };

    self.table = t;
    self.width = w;
    self.slack = capacity(w) - 1;
    self.limit = l;
  }

  /// Inserts the given key and value into the map. Returns the previous value
  /// associated with given key, if one was present.
  ///
  /// # Panics
  ///
  /// Panics if allocation fails. If that happens, it is possible for the map
  /// to leak an arbitrary set of items, but the map will remain in a valid
  /// state.

  #[inline(always)]
  pub fn get_and_insert(&mut self, key: K, value: V) -> Option<V> {
    let m = self.seed0;
    let t = self.table;
    let w = self.width;
    let h = K::hash(key, m);

    let mut a = t - K::slot(h, w);
    let mut x = unsafe { slot_hash(a).read() };

    while x > h {
      a = a + 1;
      x = unsafe { slot_hash(a).read() };
    }

    if x == h {
      return Some(unsafe { slot_data(a).replace(value) });
    }

    let s = self.slack;
    let l = self.limit;

    if l.is_null() {
      self.internal_init(h, value);
      return None;
    }

    self.slack = s.wrapping_sub(1);

    let mut y = value;

    unsafe { slot_hash(a).write(h) };

    while x != K::ZERO {
      y = unsafe { slot_data(a).replace(y) };
      a = a + 1;
      x = unsafe { slot_hash(a).replace(x) };
    }

    unsafe { slot_data(a).write(y) };

    if s == 0 || a == l {
      self.internal_grow(a);
    }

    return None;
  }

  /// Inserts the given key and value into the map.
  ///
  /// # Panics
  ///
  /// Panics if allocation fails. If that happens, it is possible for the map
  /// to leak an arbitrary set of items, but the map will remain in a valid
  /// state.

  #[inline(always)]
  pub fn insert(&mut self, key: K, value: V) {
    let _: Option<V> = self.get_and_insert(key, value);
  }

  /// Removes the given key from the map. Returns the previous value associated
  /// with the given key, if one was present.

  #[inline(always)]
  pub fn get_and_remove(&mut self, key: K) -> Option<V> {
    let m = self.seed0;
    let t = self.table;
    let w = self.width;
    let h = K::hash(key, m);

    let mut a = t - K::slot(h, w);
    let mut x = unsafe { slot_hash(a).read() };

    while x > h {
      a = a + 1;
      x = unsafe { slot_hash(a).read() };
    }

    if x != h { return None; }

    let s = self.slack;

    self.slack = s + 1;

    let value = unsafe { slot_data(a).read() };
    let mut a = a;
    let mut b = a + 1;
    let mut x = unsafe { slot_hash(b).read() };

    while t - K::slot(x, w) <= a && /* likely */ x != K::ZERO {
      unsafe { slot_hash(a).write(x) };
      unsafe { slot_data(a).write(slot_data(b).read()) };
      a = b;
      b = b + 1;
      x = unsafe { slot_hash(b).read() };
    }

    unsafe { slot_hash(a).write(K::ZERO) };

    return Some(value);
  }

  /// Removes the given key from the map.

  #[inline(always)]
  pub fn remove(&mut self, key: K) {
    let _: Option<V> = self.get_and_remove(key);
  }

  /// Removes every item from the map. Retains heap-allocated memory.
  ///
  /// # Panics
  ///
  /// Panics if [`drop`]ping a value panics. If that happens, the map will be in
  /// a valid but otherwise unspecified state.

  pub fn clear(&mut self) {
    let t = self.table;
    let w = self.width;
    let s = self.slack;
    let l = self.limit;

    let c = capacity(w);
    let n = c - s;

    if needs_drop::<V>() {
      if n != 0 {
        // WARNING!
        //
        // We must be careful to leave the map in a valid state even if a call to
        // `drop` panics.
        //
        // Here, we traverse the table in reverse order to ensure that we don't
        // remove an item that is currently displacing another item.
        //
        // Also, we update `self.slack` as we go instead of once at the end.

        let mut n = n;
        let mut s = s;
        let mut a = l;

        loop {
          if unsafe { slot_hash(a).read() } != K::ZERO {
            unsafe { slot_hash(a).write(K::ZERO) };

            s = s + 1;
            self.slack = s;

            unsafe { slot_data(a).drop_in_place() };

            n = n - 1;
            if n == 0 { break; }
          }

          a = a - 1;
        }
      }
    } else {
      if n != 0 {
        let mut a = t - (w - 1);
        let mut k = w + (t - l);

        while k != 0 {
          unsafe { slot_hash(a).write(K::ZERO) };
          a = a + 1;
          k = k - 1;
        }

        self.slack = c;
      }
    }
  }

  /// Removes every item from the map. Releases heap-allocated memory.
  ///
  /// # Panics
  ///
  /// Panics if [`drop`]ping a value or deallocating memory panics. If that
  /// happens, the map will be in a valid but otherwise unspecified state.

  pub fn reset(&mut self) {
    let t = self.table;
    let w = self.width;
    let s = self.slack;
    let l = self.limit;

    if l.is_null() { return; }

    let n = capacity(w) - s;
    let p = t - (w - 1);
    let d = w + (l - t);

    self.table = ptr::from(&EMPTY_TABLE).cast();
    self.width = 1;
    self.slack = 0;
    self.limit = ptr::NULL;

    if needs_drop::<V>() {
      if n != 0 {
        // WARNING!
        //
        // We must be careful to leave the map in a valid state even if a call to
        // `drop` panics.
        //
        // Here, we have already put `self` into the valid initial state, so if a
        // call to `drop` panics then we can just safely leak the table.

        let mut n = n;
        let mut a = p;

        loop {
          if unsafe { slot_hash(a).read() } != K::ZERO {
            unsafe { slot_data(a).drop_in_place() };

            n = n - 1;
            if n == 0 { break; }
          }

          a = a + 1;
        }
      }
    }

    unsafe { global::dealloc_slice(p, d) };
  }

  /// Returns an iterator yielding each key and a reference to its associated
  /// value. The iterator item type is `(K, &V)`.

  #[inline(always)]
  pub fn iter(&self) -> impl ExactSizeIterator<Item = (K, &V)> + use<'_, K, V> {
    let m = self.seed1;
    let t = self.table;
    let w = self.width;
    let s = self.slack;

    return Iter {
      size: capacity(w) - s,
      slot: t - (w - 1),
      func: move |x, a| unsafe { (K::invert_hash(x, m), slot_data(a).as_ref()) }
    };
  }

  /// Returns an iterator yielding each key and a mutable reference to its
  /// associated value. The iterator item type is `(K, &mut V)`.

  #[inline(always)]
  pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = (K, &mut V)> + use<'_, K, V>{
    let m = self.seed1;
    let t = self.table;
    let w = self.width;
    let s = self.slack;

    return Iter {
      size: capacity(w) - s,
      slot: t - (w - 1),
      func: move |x, a| unsafe { (K::invert_hash(x, m), slot_data(a).as_mut_ref()) }
    };
  }

  /// Returns an iterator yielding each key. The iterator item type is `K`.

  #[inline(always)]
  pub fn keys(&self) -> impl ExactSizeIterator<Item = K> + use<'_, K, V> {
    let m = self.seed1;
    let t = self.table;
    let w = self.width;
    let s = self.slack;

    return Iter {
      size: capacity(w) - s,
      slot: t - (w - 1),
      func: move |x, _| unsafe { K::invert_hash(x, m) }
    };
  }

  /// Returns an iterator yielding a reference to each value. The iterator item
  /// type is `&V`.

  #[inline(always)]
  pub fn values(&self) -> impl ExactSizeIterator<Item = &V> + use<'_, K, V> {
    let t = self.table;
    let w = self.width;
    let s = self.slack;

    return Iter {
      size: capacity(w) - s,
      slot: t - (w - 1),
      func: move |_, a| unsafe { slot_data(a).as_ref() }
    };
  }

  /// Returns an iterator yielding a mutable reference to each value. The
  /// iterator item type is `&mut V`.

  #[inline(always)]
  pub fn values_mut(&mut self) -> impl ExactSizeIterator<Item = &mut V> + use<'_, K, V> {
    let t = self.table;
    let w = self.width;
    let s = self.slack;

    return Iter {
      size: capacity(w) - s,
      slot: t - (w - 1),
      func: move |_, a| unsafe { slot_data(a).as_mut_ref() }
    };
  }

  fn internal_num_slots(&self) -> usize {
    let t = self.table;
    let w = self.width;
    let l = self.limit;

    if l.is_null() { return 0; }

    return w + (l - t);
  }

  fn internal_allocation_size(&self) -> usize {
    return self.internal_num_slots() * size_of::<Slot<K, V>>();
  }

  fn internal_load_factor(&self) -> f64 {
    // NB: NaN if no allocation
    return self.len() as f64 / self.internal_num_slots() as f64;
  }
}

impl<K: Key, V> Drop for HashMap<K, V> {
  fn drop(&mut self) {
    self.reset()
  }
}

impl<K: Key, V> Index<K> for HashMap<K, V> {
  type Output = V;

  #[inline(always)]
  fn index(&self, index: K) -> &Self::Output {
    return self.get(index).unwrap();
  }
}

// NB: The standard library hash map does *NOT* implement `IndexMut`, because
// people might try to do
//
//   map[k] = ...;
//
// when `k` is not present in the map. With other programming languages'
// standard behavior, this would insert the key.

impl<K: Key, V> IndexMut<K> for HashMap<K, V> {
  #[inline(always)]
  fn index_mut(&mut self, index: K) -> &mut Self::Output {
    return self.get_mut(index).unwrap();
  }
}

struct Iter<K: Key, V, T, F: FnMut(K::Hash, ptr<Slot<K, V>>) -> T> {
  size: usize,
  slot: ptr<Slot<K, V>>,
  func: F,
}

impl<K: Key, V, T, F: FnMut(K::Hash, ptr<Slot<K, V>>) -> T> Iterator for Iter<K, V, T, F> {
  type Item = T;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let n = self.size;

    if n == 0 { return None; }

    let mut a = self.slot;
    let mut x = unsafe { slot_hash(a).read() };

    while x == K::ZERO {
      a = a + 1;
      x = unsafe { slot_hash(a).read() };
    }

    self.size = n - 1;
    self.slot = a + 1;

    return Some((self.func)(x, a));
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    return (self.size, Some(self.size));
  }

  #[inline(always)]
  fn fold<B, G: FnMut(B, Self::Item) -> B>(self, init: B, g: G) -> B {
    // internal iteration

    let mut n = self.size;
    let mut a = self.slot;
    let mut f = self.func;
    let mut b = init;
    let mut g = g;

    if n != 0 {
      loop {
        let x = unsafe { slot_hash(a).read() };

        if x != K::ZERO {
          b = g(b, f(x, a));
          n = n - 1;
          if n == 0 { break; }
        }

        a = a + 1;
      }
    }

    return b;
  }
}

impl<K: Key, V, T, F: FnMut(K::Hash, ptr<Slot<K, V>>) -> T> ExactSizeIterator for Iter<K, V, T, F> {
  #[inline(always)]
  fn len(&self) -> usize {
    return self.size;
  }
}

impl<K: Key, V: Clone> Clone for HashMap<K, V> {
  fn clone(&self) -> Self {
    let mut t = Self::new();
    self.iter().for_each(|(x, y)| t.insert(x, y.clone()));
    return t;
  }
}

impl <K: Key + Debug, V: Debug> Debug for HashMap<K, V> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let mut a = self.iter().collect::<Box<[_]>>();
    a.sort_by_key(|&(x, _)| x);
    return f.debug_map().entries(a).finish();
  }
}

impl<K: Key, V> Default for HashMap<K, V> {
  fn default() -> Self {
    return Self::new();
  }
}

impl<K: Key, V> FromIterator<(K, V)> for HashMap<K, V> {
  fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
    let mut t = Self::new();
    iter.into_iter().for_each(|(x, y)| t.insert(x, y));
    return t;
  }
}

pub mod internal {
  //! Unstable API exposing implementation details for benchmarks and tests.

  #![allow(missing_docs)]

  use super::HashMap;
  use super::Key;

  pub fn num_slots<K: Key, V>(t: &HashMap<K, V>) -> usize {
    return t.internal_num_slots();
  }

  pub fn allocation_size<K: Key, V>(t: &HashMap<K, V>) -> usize {
    return t.internal_allocation_size();
  }

  pub fn load_factor<K: Key, V>(t: &HashMap<K, V>) -> f64 {
    return t.internal_load_factor();
  }
}
