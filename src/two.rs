//! This module provides a fast hash map keyed by types representable as
//! `NonZeroU32` or `NonZeroU64`.

// TODO: IntoIterator
// TODO: drain
// TODO: try_insert
// TODO: shrink_to_fit

extern crate alloc;

use alloc::alloc::Layout;
use alloc::alloc::alloc;
use alloc::alloc::dealloc;
use alloc::alloc::handle_alloc_error;
use core::fmt::Debug;
use core::hint::select_unpredictable;
use core::mem::MaybeUninit;
use core::mem::needs_drop;
use core::ops::Index;
use core::ptr::addr_eq;
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
  hash: *const K::Hash,
  data: *const V,
}

unsafe impl<K: Key + Send, V: Send> Send for HashMap<K, V> {
}

unsafe impl<K: Key + Sync, V: Sync> Sync for HashMap<K, V> {
}

#[inline(always)]
fn prefetch_read_l1<T>(#[allow(unused_variables)] p: *const T) {
  #[cfg(feature = "nightly")]
  core::hint::prefetch_read(p, core::hint::Locality::L1)
}

#[inline(always)]
fn prefetch_write_l1<T>(#[allow(unused_variables)] p: *mut T) {
  #[cfg(feature = "nightly")]
  core::hint::prefetch_write(p, core::hint::Locality::L1)
}

#[inline(always)]
const fn ctz(n: usize) -> usize {
  n.trailing_zeros() as usize
}

#[inline(always)]
const fn max(x: usize, y: usize) -> usize {
  if x > y { x } else { y }
}

#[inline(always)]
const fn allocation_slot_size<K: Key, V>() -> usize {
  size_of::<K::Hash>() + size_of::<V>()
}

#[inline(always)]
const fn allocation_max_num_slots<K: Key, V>() -> usize {
  isize::MAX as usize / allocation_slot_size::<K, V>()
}

#[inline(always)]
const fn allocation_size<K: Key, V>(num_slots: usize) -> usize {
  num_slots * allocation_slot_size::<K, V>()
}

#[inline(always)]
const fn allocation_align<K: Key, V>() -> usize {
  max(align_of::<K::Hash>(), align_of::<V>())
}

#[inline(always)]
const fn allocation_chunk<K: Key, V>() -> usize {
  1 << max(3, ctz(align_of::<V>()).saturating_sub(ctz(size_of::<K::Hash>())))
}

#[inline(always)]
const unsafe fn allocation_layout<K: Key, V>(num_slots: usize) -> Layout {
  let s = allocation_size::<K, V>(num_slots);
  let a = allocation_align::<K, V>();
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
      hash: K::INIT,
      data: null(),
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
    let t = self.hash;
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    let y = unsafe { t.wrapping_add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { t.wrapping_add(i).read() };
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
    let t = self.hash;
    let u = self.data;
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    prefetch_read_l1(u.wrapping_add(k));
    let y = unsafe { t.wrapping_add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { t.wrapping_add(i).read() };
      if ! (x > h) { break }
    }
    let i = select_unpredictable(y > h, i, k);
    let x = select_unpredictable(y > h, x, y);
    if x != h {
      None
    } else {
      Some(unsafe { &*u.wrapping_add(i) })
    }
  }

  /// Returns a mutable reference to the value associated with the given key,
  /// if present.
  #[inline(always)]
  pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
    let m = self.seed;
    let s = self.shift;
    let t = self.hash;
    let u = self.data.cast_mut();
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    prefetch_write_l1(u.wrapping_add(k));
    let y = unsafe { t.wrapping_add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { t.wrapping_add(i).read() };
      if ! (x > h) { break }
    }
    let i = select_unpredictable(y > h, i, k);
    let x = select_unpredictable(y > h, x, y);
    if x != h {
      None
    } else {
      Some(unsafe { &mut *u.wrapping_add(i) })
    }
  }

  #[inline(never)]
  #[cold]
  fn insert_init(&mut self, h: K::Hash, value: V) {
    let w = 4 * allocation_chunk::<K, V>();
    let e = allocation_chunk::<K, V>();
    let d = w + e;
    let s = K::BITS - ctz(w);
    assert!(d <= allocation_max_num_slots::<K, V>());
    let l = unsafe { allocation_layout::<K, V>(d) };
    let t = unsafe { alloc(l) } as *mut K::Hash;
    if t.is_null() { match handle_alloc_error(l) { } }
    unsafe { write_bytes(t, 0x00u8, d) };
    let u = t.wrapping_add(d) as *mut V;
    let k = K::slot(h, s);
    unsafe { t.wrapping_add(k).write(h) };
    unsafe { u.wrapping_add(k).write(value) };
    self.slack = capacity::<K>(s) - 1;
    self.shift = s;
    self.hash = t;
    self.data = u;
  }

  #[inline(never)]
  #[cold]
  fn insert_grow(&mut self, last_write: usize) {
    let old_r = self.slack.wrapping_add(1);
    let old_s = self.shift;
    let old_t = self.hash.cast_mut();
    let old_u = self.data.cast_mut();
    let old_d = unsafe { (old_u as *mut K::Hash).offset_from_unsigned(old_t) };
    let old_w = 1 << K::BITS - old_s;
    let old_e = old_d - old_w;
    // Temporarily place the table in a valid state in case we panic.
    self.slack = old_r;
    let h = unsafe { old_t.wrapping_add(last_write).replace(K::ZERO) };
    let new_s = old_s - 1;
    let new_w = 1 << K::BITS - new_s;
    let new_e = if last_write + 1 == old_d { 2 * old_e } else { old_e };
    let new_d = new_w + new_e;
    // Panic if the layout would overflow.
    assert!(new_d <= allocation_max_num_slots::<K, V>());
    // Allocate.
    let new_l = unsafe { allocation_layout::<K, V>(new_d) };
    let new_t = unsafe { alloc(new_l) } as *mut K::Hash;
    if new_t.is_null() { match handle_alloc_error(new_l) { } }
    let new_u = new_t.wrapping_add(new_d) as *mut V;
    // At this point, we're guaranteed to successfully finish growing the
    // table. We re-add the last write.
    unsafe { old_t.wrapping_add(last_write).write(h) };
    // Update struct fields.
    self.slack = old_r + (capacity::<K>(new_s) - capacity::<K>(old_s)) - 1;
    self.shift = new_s;
    self.hash = new_t;
    self.data = new_u;
    // Initialize new table.
    let mut i = new_d;
    loop {
      i = i - 8;
      unsafe { write_bytes(new_t.wrapping_add(i), 0x00u8, 8) };
      if i == 0 { break }
    }
    // Copy slots.
    let mut i = 0;
    let mut j = 0;
    loop {
      let x = unsafe { old_t.wrapping_add(i).read() };
      let v = unsafe { old_u.wrapping_add(i).cast::<MaybeUninit<V>>().read() };
      let k = K::slot(x, new_s);
      let k = select_unpredictable(j > k, j, k);
      unsafe { new_t.wrapping_add(k).write(x) };
      unsafe { new_u.wrapping_add(k).cast::<MaybeUninit<V>>().write(v) };
      i = i + 1;
      j = select_unpredictable(x != K::ZERO, k + 1, j);
      if i == old_d { break }
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
    let t = self.hash.cast_mut();
    let u = self.data.cast_mut();
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    prefetch_write_l1(u.wrapping_add(k));
    let y = unsafe { t.wrapping_add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { t.wrapping_add(i).read() };
      if ! (x > h) { break }
    }
    let i = select_unpredictable(y > h, i, k);
    let x = select_unpredictable(y > h, x, y);
    if x == h {
      Some(unsafe { u.wrapping_add(i).replace(value) })
    } else {
      if u.is_null() {
        self.insert_init(h, value);
      } else {
        self.slack = r.wrapping_sub(1);
        let mut i = i;
        let mut x = x;
        let mut v = value;
        unsafe { t.wrapping_add(i).write(h) };
        while x != K::ZERO {
          v = unsafe { u.wrapping_add(i).replace(v) };
          i = i + 1;
          x = unsafe { t.wrapping_add(i).replace(x) };
        }
        unsafe { u.wrapping_add(i).write(v) };
        if r == 0 || addr_eq(t.wrapping_add(i + 1), u) {
          self.insert_grow(i);
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
    let t = self.hash.cast_mut();
    let u = self.data.cast_mut();
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    prefetch_write_l1(u.wrapping_add(k));
    let y = unsafe { t.wrapping_add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { t.wrapping_add(i).read() };
      if ! (x > h) { break }
    }
    let i = select_unpredictable(y > h, i, k);
    let x = select_unpredictable(y > h, x, y);
    if x != h {
      None
    } else {
      self.slack = r + 1;
      let value = unsafe { u.wrapping_add(i).read() };
      let mut i = i;
      loop {
        i = i + 1;
        let x = unsafe { t.wrapping_add(i).read() };
        if ! (K::slot(x, s) <= i - 1 && /* likely */ x != K::ZERO) { break }
        let v = unsafe { u.wrapping_add(i).read() };
        unsafe { t.wrapping_add(i - 1).write(x) };
        unsafe { u.wrapping_add(i - 1).write(v) };
        // NOTE: We could do the loop exit test here instead.
      }
      unsafe { t.wrapping_add(i - 1).write(K::ZERO) };
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
    let t = self.hash.cast_mut();
    let u = self.data.cast_mut();
    if u.is_null() { return }
    let c = capacity::<K>(s);
    let n = c - r;
    let d = unsafe { (u as *mut K::Hash).offset_from_unsigned(t) };
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
        let mut i = d;
        loop {
          i = i - 1;
          if unsafe { t.wrapping_add(i).read() } != K::ZERO {
            unsafe { t.wrapping_add(i).write(K::ZERO) };
            r = r + 1;
            self.slack = r;
            unsafe { u.wrapping_add(i).drop_in_place() };
            n = n - 1;
            if n == 0 { break }
          }
        }
      }
    } else {
      if n != 0 {
        self.slack = c;
        let mut i = d;
        loop {
          i = i - 8;
          unsafe { write_bytes(t.wrapping_add(i), 0x00u8, 8) };
          if i == 0 { break }
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
    let t = self.hash.cast_mut();
    let u = self.data.cast_mut();
    if u.is_null() { return }
    let n = capacity::<K>(s) - r;
    let d = unsafe { (u as *mut K::Hash).offset_from_unsigned(t) };
    self.slack = capacity::<K>(K::BITS - 1);
    self.shift = K::BITS - 1;
    self.hash = K::INIT;
    self.data = null();
    if needs_drop::<V>() {
      if n != 0 {
        let mut n = n;
        let mut i = d;
        loop {
          i = i - 1;
          if unsafe { t.wrapping_add(i).read() } != K::ZERO {
            unsafe { u.wrapping_add(i).drop_in_place() };
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
    let r = self.slack;
    let s = self.shift;
    let t = self.hash;
    let u = self.data;
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        idx: unsafe { (u as *const K::Hash).offset_from_unsigned(t) },
        ptr: t,
        fun: move |x, i| unsafe { (K::invert_hash(x, m), &*u.wrapping_add(i)) }
      };
    i
  }

  /// Returns an iterator yielding each key and a mutable reference to its
  /// associated value. The iterator item type is `(K, &mut V)`.
  #[inline(always)]
  pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = (K, &mut V)> + use<'_, K, V> {
    let m = self.seed_inverted;
    let r = self.slack;
    let s = self.shift;
    let t = self.hash;
    let u = self.data;
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        idx: unsafe { (u as *const K::Hash).offset_from_unsigned(t) },
        ptr: t,
        fun: move |x, i| unsafe { (K::invert_hash(x, m), &mut *u.wrapping_add(i).cast_mut()) }
      };
    i
  }

  /// Returns an iterator yielding each key. The iterator item type is `K`.
  #[inline(always)]
  pub fn keys(&self) -> impl ExactSizeIterator<Item = K> + use<'_, K, V> {
    let m = self.seed_inverted;
    let r = self.slack;
    let s = self.shift;
    let t = self.hash;
    let u = self.data;
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        idx: unsafe { (u as *const K::Hash).offset_from_unsigned(t) },
        ptr: t,
        fun: move |x, _| unsafe { K::invert_hash(x, m) }
      };
    i
  }

  /// Returns an iterator yielding a reference to each value. The iterator item
  /// type is `&V`.
  #[inline(always)]
  pub fn values(&self) -> impl ExactSizeIterator<Item = &V> + use<'_, K, V> {
    let r = self.slack;
    let s = self.shift;
    let t = self.hash;
    let u = self.data;
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        idx: unsafe { (u as *const K::Hash).offset_from_unsigned(t) },
        ptr: t,
        fun: move |_, i| unsafe { &*u.wrapping_add(i) }
      };
    i
  }

  /// Returns an iterator yielding a mutable reference to each value. The
  /// iterator item type is `&mut V`.
  #[inline(always)]
  pub fn values_mut(&mut self) -> impl ExactSizeIterator<Item = &mut V> + use<'_, K, V> {
    let r = self.slack;
    let s = self.shift;
    let t = self.hash;
    let u = self.data;
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        idx: unsafe { (u as *const K::Hash).offset_from_unsigned(t) },
        ptr: t,
        fun: move |_, i| unsafe { &mut *u.wrapping_add(i).cast_mut() }
      };
    i
  }

  fn internal_num_slots(&self) -> usize {
    let t = self.hash;
    let u = self.data;
    if u.is_null() { return 0 }
    unsafe { (u as *const K::Hash).offset_from_unsigned(t) }
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

struct Iter<K: Key, T, F: FnMut(K::Hash, usize) -> T> {
  len: usize,
  idx: usize,
  ptr: *const K::Hash,
  fun: F,
}

impl<K: Key, T, F: FnMut(K::Hash, usize) -> T> Iterator for Iter<K, T, F> {
  type Item = T;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let n = self.len;
    if n == 0 { return None }
    let t = self.ptr;
    let mut i = self.idx;
    let mut x;
    loop {
      i = i - 1;
      x = unsafe { t.wrapping_add(i).read() };
      if x != K::ZERO { break }
    }
    self.len = n - 1;
    self.idx = i;
    Some((self.fun)(x, i))
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }

  #[inline(always)]
  fn fold<U, G: FnMut(U, T) -> U>(self, init: U, g: G) -> U {
    let t = self.ptr;
    let mut n = self.len;
    let mut i = self.idx;
    let mut f = self.fun;
    let mut u = init;
    let mut g = g;
    if n != 0 {
      loop {
        i = i - 1;
        let x = unsafe { t.wrapping_add(i).read() };
        if x != K::ZERO {
          u = g(u, f(x, i));
          n = n - 1;
          if n == 0 { break }
        }
      }
    }
    u
  }
}

impl<K: Key, T, F: FnMut(K::Hash, usize) -> T> ExactSizeIterator for Iter<K, T, F> {
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
