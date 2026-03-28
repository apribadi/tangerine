//! This module provides a fast hash map keyed by types representable as
//! `NonZeroU32` or `NonZeroU64`.

// TODO: IntoIterator
// TODO: drain
// TODO: try_insert
// TODO: shrink_to_fit

extern crate alloc;

use alloc::alloc::Layout;
use alloc::alloc::alloc_zeroed;
use alloc::alloc::dealloc;
use alloc::alloc::handle_alloc_error;
use core::fmt::Debug;
use core::hint::select_unpredictable;
use core::mem::MaybeUninit;
use core::mem::needs_drop;
use core::mem::offset_of;
use core::ops::Index;
use core::ptr::null;
use core::ptr::write_bytes;
use rand_core::RngCore;

use crate::key::Key;

/// A fast hash map keyed by types representable as [`NonZeroU32`](core::num::NonZeroU32)
/// or [`NonZeroU64`](core::num::NonZeroU64).
pub struct HashMap<K: Key, V> {
  seed_inverted: K::Seed,
  seed: K::Seed,
  slack: usize,
  shift: usize,
  table: *const Slot<K, V>,
  limit: *const Slot<K, V>,
}

unsafe impl<K: Key + Send, V: Send> Send for HashMap<K, V> {
}

unsafe impl<K: Key + Sync, V: Sync> Sync for HashMap<K, V> {
}

struct Slot<K: Key, V> {
  hash: K::Hash,
  data: MaybeUninit<V>,
}

#[inline(always)]
fn slot_hash<K: Key, V>(a: *mut Slot<K, V>) -> *mut K::Hash {
  a.wrapping_byte_add(offset_of!(Slot<K, V>, hash)).cast()
}

#[inline(always)]
fn slot_data<K: Key, V>(a: *mut Slot<K, V>) -> *mut V {
  a.wrapping_byte_add(offset_of!(Slot<K, V>, data)).cast()
}

static EMPTY_TABLE: [u64; 12] = [0u64; 12];

#[inline(always)]
const fn empty_table<K: Key, V>() -> *const Slot<K, V> {
  // TODO:
  const { assert!(size_of::<Slot<K, V>>() <= 32) };
  &raw const EMPTY_TABLE as *const Slot<K, V>
}

#[inline(always)]
const fn ctz(n: usize) -> usize {
  n.trailing_zeros() as usize
}

#[inline(always)]
const fn allocation_max_num_slots<K: Key, V>() -> usize {
  isize::MAX as usize / size_of::<Slot<K, V>>()
}

#[inline(always)]
const fn allocation_size<K: Key, V>(num_slots: usize) -> usize {
  num_slots * size_of::<Slot<K, V>>()
}

#[inline(always)]
const unsafe fn allocation_layout<K: Key, V>(num_slots: usize) -> Layout {
  let s = allocation_size::<K, V>(num_slots);
  let a = align_of::<Slot<K, V>>();
  unsafe { Layout::from_size_align_unchecked(s, a) }
}

#[inline(always)]
const fn capacity<K: Key>(s: usize) -> usize {
  1 << K::BITS - s - 1
}

impl<K: Key, V> HashMap<K, V> {
  #[inline(always)]
  fn from_seed(m: K::Seed) -> Self {
    Self {
      seed_inverted: K::invert_seed(m),
      seed: m,
      slack: capacity::<K>(K::BITS - 1),
      shift: K::BITS - 1,
      table: empty_table::<K, V>(),
      limit: null(),
    }
  }

  /// Creates an empty map, seeding the hash function from a thread-local
  /// random number generator.
  pub fn new() -> Self {
    Self::from_seed(K::seed_nondet())
  }

  /// Creates an empty map, seeding the hash function from the given random
  /// number generator.
  pub fn new_seeded(rng: &mut impl RngCore) -> Self {
    Self::from_seed(K::seed(rng))
  }

  /// Returns the number of items.
  #[inline(always)]
  pub fn len(&self) -> usize {
    let r = self.slack;
    let s = self.shift;
    capacity::<K>(s) - r
  }

  /// Returns whether the map contains zero items.
  #[inline(always)]
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Returns whether the map contains the given key.
  #[inline(always)]
  pub fn contains_key(&self, key: K) -> bool {
    let m = self.seed;
    let s = self.shift;
    let t = self.table.cast_mut();
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    let b = t.wrapping_add(k);
    let y = unsafe { slot_hash(b).read() };
    let mut a = b;
    let mut x;
    loop {
      a = a.wrapping_add(1);
      x = unsafe { slot_hash(a).read() };
      if ! (x > h) { break }
    }
    let x = select_unpredictable(y > h, x, y);
    x == h
  }

  /// Returns a reference to the value associated with the given key, if
  /// present.
  #[inline(always)]
  pub fn get(&self, key: K) -> Option<&V> {
    let m = self.seed;
    let s = self.shift;
    let t = self.table.cast_mut();
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    let b = t.wrapping_add(k);
    let y = unsafe { slot_hash(b).read() };
    let mut a = b;
    let mut x;
    loop {
      a = a.wrapping_add(1);
      x = unsafe { slot_hash(a).read() };
      if ! (x > h) { break }
    }
    let a = select_unpredictable(y > h, a, b);
    let x = select_unpredictable(y > h, x, y);
    if x != h {
      None
    } else {
      Some(unsafe { &*slot_data(a) })
    }
  }

  /// Returns a mutable reference to the value associated with the given key,
  /// if present.
  #[inline(always)]
  pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
    let m = self.seed;
    let s = self.shift;
    let t = self.table.cast_mut();
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    let b = t.wrapping_add(k);
    let y = unsafe { slot_hash(b).read() };
    let mut a = b;
    let mut x;
    loop {
      a = a.wrapping_add(1);
      x = unsafe { slot_hash(a).read() };
      if ! (x > h) { break }
    }
    let a = select_unpredictable(y > h, a, b);
    let x = select_unpredictable(y > h, x, y);
    if x != h {
      None
    } else {
      Some(unsafe { &mut *slot_data(a) })
    }
  }

  #[inline(never)]
  #[cold]
  fn insert_init(&mut self, h: K::Hash, value: V) {
    const { assert!(40 <= allocation_max_num_slots::<K, V>()) };
    let w = 32;
    let d = 40;
    let s = K::BITS - ctz(w);
    let l = unsafe { allocation_layout::<K, V>(d) };
    let t = unsafe { alloc_zeroed(l) } as *mut Slot<K, V>;
    if t.is_null() { match handle_alloc_error(l) { } }
    let k = K::slot(h, s);
    unsafe { slot_hash(t.wrapping_add(k)).write(h) };
    unsafe { slot_data(t.wrapping_add(k)).write(value) };
    self.slack = capacity::<K>(s) - 1;
    self.shift = s;
    self.table = t;
    self.limit = t.wrapping_add(d);
  }

  #[inline(never)]
  #[cold]
  fn insert_grow(&mut self, last_write: *mut Slot<K, V>) {
    let old_r = self.slack.wrapping_add(1);
    let old_s = self.shift;
    let old_t = self.table.cast_mut();
    let old_u = self.limit.cast_mut();
    let old_d = unsafe { old_u.offset_from_unsigned(old_t) };
    let old_w = 1 << K::BITS - old_s;
    let old_e = old_d - old_w;
    // Temporarily place the table in a valid state in case we panic.
    self.slack = old_r;
    let h = unsafe { slot_hash(last_write).replace(K::ZERO) };
    let new_s = old_s - 1;
    let new_w = 1 << K::BITS - new_s;
    let new_e = if last_write.wrapping_add(1) == old_u { 2 * old_e } else { old_e };
    let new_d = new_w + new_e;
    // Panic if the layout would overflow.
    assert!(new_d <= allocation_max_num_slots::<K, V>());
    // Allocate.
    let new_l = unsafe { allocation_layout::<K, V>(new_d) };
    let new_t = unsafe { alloc_zeroed(new_l) } as *mut Slot<K, V>;
    if new_t.is_null() { match handle_alloc_error(new_l) { } }
    let new_u = new_t.wrapping_add(new_d);
    // At this point, we're guaranteed to successfully finish growing the
    // table. We re-add the last write.
    unsafe { slot_hash(last_write).write(h) };
    // Update struct fields.
    self.slack = old_r + (capacity::<K>(new_s) - capacity::<K>(old_s)) - 1;
    self.shift = new_s;
    self.table = new_t;
    self.limit = new_u;
    // Copy slots.
    let mut a = old_t;
    let mut j = 0;
    loop {
      let x = unsafe { slot_hash(a).read() };
      let v = unsafe { slot_data(a).cast::<MaybeUninit<V>>().read() };
      let k = K::slot(x, new_s);
      let k = select_unpredictable(j > k, j, k);
      unsafe { slot_hash(new_t.wrapping_add(k)).write(x) };
      unsafe { slot_data(new_t.wrapping_add(k)).cast::<MaybeUninit<V>>().write(v) };
      a = a.wrapping_add(1);
      j = select_unpredictable(x != K::ZERO, k + 1, j);
      if a == old_u { break }
    }
    // The map is now in a valid state, even if deallocating panics.
    unsafe { dealloc(old_t as *mut u8, allocation_layout::<K, V>(old_d)) }
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
  pub fn insert(&mut self, key: K, value: V) -> Option<V> {
    let m = self.seed;
    let r = self.slack;
    let s = self.shift;
    let t = self.table.cast_mut();
    let u = self.limit.cast_mut();
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    let b = t.wrapping_add(k);
    let y = unsafe { slot_hash(b).read() };
    let mut a = b;
    let mut x;
    loop {
      a = a.wrapping_add(1);
      x = unsafe { slot_hash(a).read() };
      if ! (x > h) { break }
    }
    let a = select_unpredictable(y > h, a, b);
    let x = select_unpredictable(y > h, x, y);
    if x == h {
      Some(unsafe { slot_data(a).replace(value) })
    } else {
      if u.is_null() {
        self.insert_init(h, value);
      } else {
        self.slack = r.wrapping_sub(1);
        let mut a = a;
        let mut x = x;
        let mut v = value;
        unsafe { slot_hash(a).write(h) };
        while x != K::ZERO {
          v = unsafe { slot_data(a).replace(v) };
          a = a.wrapping_add(1);
          x = unsafe { slot_hash(a).replace(x) };
        }
        unsafe { slot_data(a).write(v) };
        if r == 0 || a.wrapping_add(1) == u {
          self.insert_grow(a);
        }
      }
      None
    }
  }

  /// Removes the given key from the map. Returns the previous value associated
  /// with the given key, if one was present.
  #[inline(always)]
  pub fn remove(&mut self, key: K) -> Option<V> {
    let m = self.seed;
    let r = self.slack;
    let s = self.shift;
    let t = self.table.cast_mut();
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    let y = unsafe { slot_hash(t.wrapping_add(k)).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { slot_hash(t.wrapping_add(i)).read() };
      if ! (x > h) { break }
    }
    let i = select_unpredictable(y > h, i, k);
    let x = select_unpredictable(y > h, x, y);
    if x != h {
      None
    } else {
      self.slack = r + 1;
      let value = unsafe { slot_data(t.wrapping_add(i)).read() };
      let mut i = i;
      loop {
        i = i + 1;
        let x = unsafe { slot_hash(t.wrapping_add(i)).read() };
        if ! (K::slot(x, s) <= i - 1 && /* likely */ x != K::ZERO) { break }
        let v = unsafe { slot_data(t.wrapping_add(i)).read() };
        unsafe { slot_hash(t.wrapping_add(i - 1)).write(x) };
        unsafe { slot_data(t.wrapping_add(i - 1)).write(v) };
        // NOTE: We could do the loop exit test here instead.
      }
      unsafe { slot_hash(t.wrapping_add(i - 1)).write(K::ZERO) };
      Some(value)
    }
  }

  /// Removes every item from the map. Retains heap-allocated memory.
  ///
  /// # Panics
  ///
  /// Panics if [`drop`]ping a value panics. If that happens, the map will be in
  /// a valid but otherwise unspecified state.
  pub fn clear(&mut self) {
    let r = self.slack;
    let s = self.shift;
    let t = self.table.cast_mut();
    let u = self.limit.cast_mut();
    if u.is_null() { return }
    let c = capacity::<K>(s);
    let n = c - r;
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
        let mut r = r;
        let mut a = u;
        loop {
          a = a.wrapping_sub(1);
          if unsafe { slot_hash(a).read() } != K::ZERO {
            unsafe { slot_hash(a).write(K::ZERO) };
            r = r + 1;
            self.slack = r;
            unsafe { slot_data(a).drop_in_place() };
            n = n - 1;
            if n == 0 { break }
          }
        }
      }
    } else {
      if n != 0 {
        self.slack = c;
        let mut a = u;
        loop {
          a = a.wrapping_sub(8);
          unsafe { write_bytes(a, 0x00u8, 8) };
          if a == t { break }
        }
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
    let r = self.slack;
    let s = self.shift;
    let t = self.table.cast_mut();
    let u = self.limit.cast_mut();
    if u.is_null() { return }
    let n = capacity::<K>(s) - r;
    let d = unsafe { u.offset_from_unsigned(t) };
    self.slack = capacity::<K>(K::BITS - 1);
    self.shift = K::BITS - 1;
    self.table = empty_table::<K, V>();
    self.limit = null();
    if needs_drop::<V>() {
      if n != 0 {
        let mut n = n;
        let mut a = u;
        loop {
          a = a.wrapping_sub(1);
          if unsafe { slot_hash(a).read() } != K::ZERO {
            unsafe { slot_data(a).drop_in_place() };
            n = n - 1;
            if n == 0 { break }
          }
        }
      }
    }
    unsafe { dealloc(t as *mut u8, allocation_layout::<K, V>(d)) };
  }

  /// Returns an iterator yielding each key and a reference to its associated
  /// value. The iterator item type is `(K, &V)`.
  #[inline(always)]
  pub fn iter(&self) -> impl ExactSizeIterator<Item = (K, &V)> + use<'_, K, V> {
    let m = self.seed_inverted;
    Iter {
      len: capacity::<K>(self.shift) - self.slack,
      ptr: self.limit.cast_mut(),
      fun: move |x, a| unsafe { (K::invert_hash(x, m), &*slot_data(a)) }
    }
  }

  /// Returns an iterator yielding each key and a mutable reference to its
  /// associated value. The iterator item type is `(K, &mut V)`.
  #[inline(always)]
  pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = (K, &mut V)> + use<'_, K, V> {
    let m = self.seed_inverted;
    Iter {
      len: capacity::<K>(self.shift) - self.slack,
      ptr: self.limit.cast_mut(),
      fun: move |x, a| unsafe { (K::invert_hash(x, m), &mut *slot_data(a)) }
    }
  }

  /// Returns an iterator yielding each key. The iterator item type is `K`.
  #[inline(always)]
  pub fn keys(&self) -> impl ExactSizeIterator<Item = K> + use<'_, K, V> {
    let m = self.seed_inverted;
    Iter {
      len: capacity::<K>(self.shift) - self.slack,
      ptr: self.limit.cast_mut(),
      fun: move |x, _| unsafe { K::invert_hash(x, m) }
    }
  }

  /// Returns an iterator yielding a reference to each value. The iterator item
  /// type is `&V`.
  #[inline(always)]
  pub fn values(&self) -> impl ExactSizeIterator<Item = &V> + use<'_, K, V> {
    Iter {
      len: capacity::<K>(self.shift) - self.slack,
      ptr: self.limit.cast_mut(),
      fun: move |_, a| unsafe { &*slot_data(a) }
    }
  }

  /// Returns an iterator yielding a mutable reference to each value. The
  /// iterator item type is `&mut V`.
  #[inline(always)]
  pub fn values_mut(&mut self) -> impl ExactSizeIterator<Item = &mut V> + use<'_, K, V> {
    Iter {
      len: capacity::<K>(self.shift) - self.slack,
      ptr: self.limit.cast_mut(),
      fun: move |_, a| unsafe { &mut *slot_data(a) }
    }
  }

  fn internal_num_slots(&self) -> usize {
    let t = self.table;
    let u = self.limit;
    if u.is_null() { return 0 }
    unsafe { u.offset_from_unsigned(t) }
  }

  fn internal_allocation_size(&self) -> usize {
    allocation_size::<K, V>(self.internal_num_slots())
  }

  fn internal_load_factor(&self) -> f64 {
    self.len() as f64 / self.internal_num_slots() as f64
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
    self.get(index).unwrap()
  }
}

struct Iter<K: Key, V, T, F: FnMut(K::Hash, *mut Slot<K, V>) -> T> {
  len: usize,
  ptr: *mut Slot<K, V>,
  fun: F,
}

impl<K: Key, V, T, F: FnMut(K::Hash, *mut Slot<K, V>) -> T> Iterator for Iter<K, V, T, F> {
  type Item = T;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let n = self.len;
    if n == 0 { return None }
    let mut a = self.ptr;
    let mut x;
    loop {
      a = a.wrapping_sub(1);
      x = unsafe { slot_hash(a).read() };
      if x != K::ZERO { break }
    }
    self.len = n - 1;
    self.ptr = a;
    Some((self.fun)(x, a))
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }

  #[inline(always)]
  fn fold<U, G: FnMut(U, T) -> U>(self, init: U, g: G) -> U {
    let mut n = self.len;
    let mut a = self.ptr;
    let mut f = self.fun;
    let mut u = init;
    let mut g = g;
    if n != 0 {
      loop {
        a = a.wrapping_sub(1);
        let x = unsafe { slot_hash(a).read() };
        if x != K::ZERO {
          u = g(u, f(x, a));
          n = n - 1;
          if n == 0 { break }
        }
      }
    }
    u
  }
}

impl<K: Key, V, T, F: FnMut(K::Hash, *mut Slot<K, V>) -> T> ExactSizeIterator for Iter<K, V, T, F> {
  #[inline(always)]
  fn len(&self) -> usize {
    self.len
  }
}

impl<K: Key, V: Clone> Clone for HashMap<K, V> {
  fn clone(&self) -> Self {
    let mut t = Self::new();
    self.iter().for_each(|(x, y)| { let _ = t.insert(x, y.clone()); });
    t
  }
}

impl <K: Key + Debug, V: Debug> Debug for HashMap<K, V> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut a = self.iter().collect::<Box<[(K, &V)]>>();
    a.sort_by_key(|&(x, _)| x);
    f.debug_map().entries(a).finish()
  }
}

impl<K: Key, V> Default for HashMap<K, V> {
  fn default() -> Self {
    Self::new()
  }
}

impl<K: Key, V> Extend<(K, V)> for HashMap<K, V> {
  fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
    iter.into_iter().for_each(|(k, v)| { let _ = self.insert(k, v); });
  }
}

impl<K: Key, V> FromIterator<(K, V)> for HashMap<K, V> {
  fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
    let mut t = Self::new();
    iter.into_iter().for_each(|(x, y)| { let _ = t.insert(x, y); });
    t
  }
}

#[cfg(feature = "nightly")]
impl<'a, K: Key, V> IntoIterator for &'a HashMap<K, V> {
  type Item = (K, &'a V);
  type IntoIter = impl ExactSizeIterator<Item = Self::Item>;

  #[inline(always)]
  fn into_iter(self) -> Self::IntoIter {
    self.iter()
  }
}

#[cfg(feature = "nightly")]
impl<'a, K: Key, V> IntoIterator for &'a mut HashMap<K, V> {
  type Item = (K, &'a mut V);
  type IntoIter = impl ExactSizeIterator<Item = Self::Item>;

  #[inline(always)]
  fn into_iter(self) -> Self::IntoIter {
    self.iter_mut()
  }
}

pub mod internal {
  //! Unstable API exposing implementation details for benchmarks and tests.

  #![allow(missing_docs)]

  use super::HashMap;
  use super::Key;

  pub fn num_slots<K: Key, V>(t: &HashMap<K, V>) -> usize {
    t.internal_num_slots()
  }

  pub fn allocation_size<K: Key, V>(t: &HashMap<K, V>) -> usize {
    t.internal_allocation_size()
  }

  pub fn load_factor<K: Key, V>(t: &HashMap<K, V>) -> f64 {
    t.internal_load_factor()
  }
}

#[allow(missing_docs)]
pub fn get(t: &HashMap<std::num::NonZeroU64, u32>, key: std::num::NonZeroU64) -> Option<&u32> {
  t.get(key)
}

#[allow(missing_docs)]
pub fn get_value(t: &HashMap<std::num::NonZeroU64, u32>, key: std::num::NonZeroU64) -> Option<u32> {
  match t.get(key) { None => None, Some(&y) => Some(y) }
}

#[allow(missing_docs)]
pub fn contains_key(t: &HashMap<std::num::NonZeroU64, u32>, key: std::num::NonZeroU64) -> bool {
  t.contains_key(key)
}

#[allow(missing_docs)]
pub fn insert(t: &mut HashMap<std::num::NonZeroU64, u32>, key: std::num::NonZeroU64, value: u32) {
  let _ = t.insert(key, value);
}

#[allow(missing_docs)]
pub fn remove(t: &mut HashMap<std::num::NonZeroU64, u32>, key: std::num::NonZeroU64) {
  let _ = t.remove(key);
}

#[allow(missing_docs)]
pub fn clear(t: &mut HashMap<std::num::NonZeroU64, u32>) {
  t.clear();
}
