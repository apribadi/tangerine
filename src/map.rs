//! This module provides a fast hash map keyed by types representable as
//! `NonZeroU32` or `NonZeroU64`.

// TODO:
// - get_disjoint_mut

extern crate alloc;

use alloc::alloc::Layout;
use alloc::alloc::alloc;
use alloc::alloc::dealloc;
use alloc::alloc::handle_alloc_error;
use core::fmt::Debug;
use core::fmt::Formatter;
use core::hint::assert_unchecked;
use core::hint::select_unpredictable;
use core::mem::MaybeUninit;
use core::mem::needs_drop;
use core::mem::replace;
use core::ops::Index;
use core::ptr::addr_eq;
use core::ptr::write_bytes;
use rand_core::RngCore;

use crate::key::Key;

/// A fast hash map keyed by types representable as [`NonZeroU32`](core::num::NonZeroU32)
/// or [`NonZeroU64`](core::num::NonZeroU64).
pub struct HashMap<K: Key, V> {
  slack: usize,
  shift: usize,
  table: *const K::Hash,
  value: *const V,
  seed: K::Seed,
  seed_inverted: K::Seed,
}

unsafe impl<K: Key + Send, V: Send> Send for HashMap<K, V> {
}

unsafe impl<K: Key + Sync, V: Sync> Sync for HashMap<K, V> {
}

#[inline(always)]
unsafe fn assume_nonnull<T>(p: *const T) {
  unsafe { assert_unchecked(p.addr() != 0) }
}

#[inline(always)]
fn prefetch_read<T>(_p: *const T) {
  #[cfg(feature = "nightly")]
  core::hint::prefetch_read(_p, core::hint::Locality::L1)
}

#[inline(always)]
fn prefetch_write<T>(_p: *mut T) {
  #[cfg(feature = "nightly")]
  core::hint::prefetch_write(_p, core::hint::Locality::L1)
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
  1 << max(2, ctz(align_of::<V>()).saturating_sub(ctz(size_of::<K::Hash>())))
}

#[inline(always)]
const unsafe fn allocation_layout<K: Key, V>(num_slots: usize) -> Layout {
  let s = allocation_size::<K, V>(num_slots);
  let a = allocation_align::<K, V>();
  unsafe { Layout::from_size_align_unchecked(s, a) }
}

#[inline(always)]
fn capacity<K: Key>(s: usize) -> usize {
  1 << K::BITS - s - 1
}

#[inline(always)]
const fn is_dummy<K: Key>(s: usize) -> bool {
  s == K::BITS - 1
}

#[inline(always)]
fn ptr_diff<T>(x: *const T, y: *const T) -> usize {
  x.addr().wrapping_sub(y.addr()) / size_of::<T>()
}

impl<K: Key, V> HashMap<K, V> {
  #[inline(always)]
  fn from_seed(m: K::Seed) -> Self {
    Self {
      slack: capacity::<K>(K::BITS - 1),
      shift: K::BITS - 1,
      table: K::INIT,
      value: K::INIT.wrapping_add(3).cast(),
      seed: m,
      seed_inverted: K::invert_seed(m),
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
    let s = self.shift;
    let t = self.table;
    let m = self.seed;
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    let a = unsafe { t.add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { t.add(i).read() };
      if ! (x > h) { break }
    }
    let x = select_unpredictable(a > h, x, a);
    x == h
  }

  /// Returns a reference to the value associated with the given key, if
  /// present.
  #[inline(always)]
  pub fn get(&self, key: K) -> Option<&V> {
    let s = self.shift;
    let t = self.table;
    let u = self.value;
    let m = self.seed;
    unsafe { assume_nonnull(u) };
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    prefetch_read(u.wrapping_add(k));
    let a = unsafe { t.add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { t.add(i).read() };
      if ! (x > h) { break }
    }
    let i = select_unpredictable(a > h, i, k);
    let x = select_unpredictable(a > h, x, a);
    if x != h {
      None
    } else {
      Some(unsafe { &*u.add(i) })
    }
  }

  /// Returns a mutable reference to the value associated with the given key,
  /// if present.
  #[inline(always)]
  pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
    let s = self.shift;
    let t = self.table;
    let u = self.value.cast_mut();
    let m = self.seed;
    unsafe { assume_nonnull(u) };
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    prefetch_write(u.wrapping_add(k));
    let a = unsafe { t.add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { t.add(i).read() };
      if ! (x > h) { break }
    }
    let i = select_unpredictable(a > h, i, k);
    let x = select_unpredictable(a > h, x, a);
    if x != h {
      None
    } else {
      Some(unsafe { &mut *u.add(i) })
    }
  }

  #[inline(never)]
  #[cold]
  fn insert_init(&mut self, h: K::Hash, value: V) -> *mut V {
    let w = 4 * allocation_chunk::<K, V>();
    let e = allocation_chunk::<K, V>();
    let d = w + e;
    let s = K::BITS - ctz(w);
    assert!(d <= allocation_max_num_slots::<K, V>());
    let l = unsafe { allocation_layout::<K, V>(d) };
    let t = unsafe { alloc(l) } as *mut K::Hash;
    if t.is_null() { match handle_alloc_error(l) { } }
    let u = unsafe { t.add(d) } as *mut V;
    unsafe { write_bytes(t, 0u8, d) };
    let k = K::slot(h, s);
    unsafe { t.add(k).write(h) };
    unsafe { u.add(k).write(value) };
    self.slack = capacity::<K>(s) - 1;
    self.shift = s;
    self.table = t;
    self.value = u;
    unsafe { u.add(k) }
  }

  #[inline(never)]
  #[cold]
  fn insert_grow(&mut self, h: K::Hash, last_write: usize) -> *mut V {
    let old_r = self.slack.wrapping_add(1);
    let old_s = self.shift;
    let old_t = self.table.cast_mut();
    let old_u = self.value.cast_mut();
    let old_d = ptr_diff(old_u.cast(), old_t);
    let old_w = 1 << K::BITS - old_s;
    let old_e = old_d - old_w;
    // Temporarily place the table in a valid state in case we panic.
    self.slack = old_r;
    let z = unsafe { old_t.add(last_write).replace(K::ZERO) };
    // Compute new sizes.
    let new_s = old_s - 1;
    let new_w = 1 << K::BITS - new_s;
    let new_e =
      if last_write + 1 == old_d {
        old_e * 2 // if we wrote in the final slot
      } else if old_e < ctz(new_w) {
        old_e + allocation_chunk::<K, V>() // we maintain e >= log2(w)
      } else {
        old_e
      };
    let new_d = new_w + new_e;
    // Panic if the layout would overflow.
    assert!(new_d <= allocation_max_num_slots::<K, V>());
    // Allocate.
    let new_l = unsafe { allocation_layout::<K, V>(new_d) };
    let new_t = unsafe { alloc(new_l) } as *mut K::Hash;
    if new_t.is_null() { match handle_alloc_error(new_l) { } }
    let new_u = unsafe { new_t.add(new_d) } as *mut V;
    // At this point, we're guaranteed to successfully finish growing the
    // table. We re-add the last write.
    unsafe { old_t.add(last_write).write(z) };
    // Update struct fields.
    self.slack = old_r + (capacity::<K>(new_s) - capacity::<K>(old_s)) - 1;
    self.shift = new_s;
    self.table = new_t;
    self.value = new_u;
    // Initialize new table.
    let mut i = new_d;
    loop {
      i = i - allocation_chunk::<K, V>();
      unsafe { write_bytes(new_t.add(i), 0u8, allocation_chunk::<K, V>()) };
      if i == 0 { break }
    }
    // Copy slots.
    let mut i = 0;
    let mut j = 0;
    loop {
      let x = unsafe { old_t.add(i).read() };
      let y = unsafe { old_u.add(i).cast::<MaybeUninit<V>>().read() };
      let k = K::slot(x, new_s);
      let k = select_unpredictable(j > k, j, k);
      unsafe { new_t.add(k).write(x) };
      unsafe { new_u.add(k).cast::<MaybeUninit<V>>().write(y) };
      i = i + 1;
      j = select_unpredictable(x != K::ZERO, k + 1, j);
      if i == old_d { break }
    }
    // The map is now in a valid state, even if deallocating panics.
    unsafe { dealloc(old_t as *mut u8, allocation_layout::<K, V>(old_d)) };
    // Find the newly-inserted value. Note, this was not necessarily at last_write.
    let mut i = K::slot(h, new_s);
    while unsafe { new_t.add(i).read() } != h {
      i = i + 1;
    }
    unsafe { new_u.add(i) }
  }

  /// Tries to insert the given key and value into the map. Returns a mutable
  /// reference to the inserted value.
  ///
  /// If the map already contains a value associated with the given key, then
  /// nothing is updated. Instead an error is returned that contains both a
  /// mutable reference to occupied entry and the value that was not inserted.
  ///
  /// # Panics
  ///
  /// Panics if allocation fails. If that happens, it is possible for the map
  /// to leak an arbitrary set of items, but the map will remain in a valid
  /// state.
  #[inline(always)]
  pub fn try_insert(&mut self, key: K, value: V) -> Result<&mut V, (&mut V, V)> {
    let r = self.slack;
    let s = self.shift;
    let t = self.table.cast_mut();
    let u = self.value.cast_mut();
    let m = self.seed;
    unsafe { assume_nonnull(u) };
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    prefetch_write(u.wrapping_add(k));
    let a = unsafe { t.add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { t.add(i).read() };
      if ! (x > h) { break }
    }
    let i = select_unpredictable(a > h, i, k);
    let x = select_unpredictable(a > h, x, a);
    if x == h {
      Err((unsafe { &mut *u.add(i) }, value))
    } else {
      let p =
        if is_dummy::<K>(s) {
          self.insert_init(h, value)
        } else {
          self.slack = r.wrapping_sub(1);
          let inserted_at = i;
          let mut i = i;
          let mut x = x;
          let mut v = value;
          unsafe { t.add(i).write(h) };
          while x != K::ZERO {
            v = unsafe { u.add(i).replace(v) };
            i = i + 1;
            x = unsafe { t.add(i).replace(x) };
          }
          unsafe { u.add(i).write(v) };
          if addr_eq(t.wrapping_add(i + 1), u) || r == 0 {
            self.insert_grow(h, i)
          } else {
            unsafe { u.add(inserted_at) }
          }
        };
      Ok(unsafe { &mut *p })
    }
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
    match self.try_insert(key, value) {
      Ok(_) => None,
      Err((p, v)) => Some(replace(p, v)),
    }
  }

  /// Removes the given key from the map. Returns the previous value associated
  /// with the given key, if one was present.
  #[inline(always)]
  pub fn remove(&mut self, key: K) -> Option<V> {
    let r = self.slack;
    let s = self.shift;
    let t = self.table.cast_mut();
    let u = self.value.cast_mut();
    let m = self.seed;
    let h = K::hash(key, m);
    let k = K::slot(h, s);
    prefetch_write(u.wrapping_add(k));
    let a = unsafe { t.add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { t.add(i).read() };
      if ! (x > h) { break }
    }
    let i = select_unpredictable(a > h, i, k);
    let x = select_unpredictable(a > h, x, a);
    if x != h {
      None
    } else {
      self.slack = r + 1;
      let value = unsafe { u.add(i).read() };
      let mut i = i;
      loop {
        i = i + 1;
        let x = unsafe { t.add(i).read() };
        if ! (K::slot(x, s) <= i - 1 && /* likely */ x != K::ZERO) { break }
        let y = unsafe { u.add(i).read() };
        unsafe { t.add(i - 1).write(x) };
        unsafe { u.add(i - 1).write(y) };
        // NOTE: We could do the loop exit test here instead.
      }
      unsafe { t.add(i - 1).write(K::ZERO) };
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
    let u = self.value.cast_mut();
    if is_dummy::<K>(s) { return }
    let c = capacity::<K>(s);
    let n = c - r;
    let d = ptr_diff(u.cast(), t);
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
          if unsafe { t.add(i).read() } != K::ZERO {
            unsafe { t.add(i).write(K::ZERO) };
            r = r + 1;
            self.slack = r;
            unsafe { u.add(i).drop_in_place() };
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
          i = i - allocation_chunk::<K, V>();
          unsafe { write_bytes(t.add(i), 0u8, allocation_chunk::<K, V>()) };
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
    let t = self.table.cast_mut();
    let u = self.value.cast_mut();
    if is_dummy::<K>(s) { return }
    let n = capacity::<K>(s) - r;
    let d = ptr_diff(u.cast(), t);
    self.slack = capacity::<K>(K::BITS - 1);
    self.shift = K::BITS - 1;
    self.table = K::INIT;
    self.value = K::INIT.wrapping_add(3).cast();
    if needs_drop::<V>() {
      if n != 0 {
        let mut n = n;
        let mut i = d;
        loop {
          i = i - 1;
          if unsafe { t.add(i).read() } != K::ZERO {
            unsafe { u.add(i).drop_in_place() };
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
    let r = self.slack;
    let s = self.shift;
    let t = self.table;
    let u = self.value;
    let m = self.seed_inverted;
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        idx: ptr_diff(u.cast(), t),
        ptr: t,
        fun: move |x, i| unsafe { (K::invert_hash(x, m), &*u.add(i)) }
      };
    i
  }

  /// Returns an iterator yielding each key and a mutable reference to its
  /// associated value. The iterator item type is `(K, &mut V)`.
  #[inline(always)]
  pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = (K, &mut V)> + use<'_, K, V> {
    let r = self.slack;
    let s = self.shift;
    let t = self.table;
    let u = self.value.cast_mut();
    let m = self.seed_inverted;
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        idx: ptr_diff(u.cast(), t),
        ptr: t,
        fun: move |x, i| unsafe { (K::invert_hash(x, m), &mut *u.add(i)) }
      };
    i
  }

  /// Returns an iterator yielding each key. The iterator item type is `K`.
  #[inline(always)]
  pub fn keys(&self) -> impl ExactSizeIterator<Item = K> + use<'_, K, V> {
    let r = self.slack;
    let s = self.shift;
    let t = self.table;
    let u = self.value;
    let m = self.seed_inverted;
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        idx: ptr_diff(u.cast(), t),
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
    let t = self.table;
    let u = self.value;
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        idx: ptr_diff(u.cast(), t),
        ptr: t,
        fun: move |_, i| unsafe { &*u.add(i) }
      };
    i
  }

  /// Returns an iterator yielding a mutable reference to each value. The
  /// iterator item type is `&mut V`.
  #[inline(always)]
  pub fn values_mut(&mut self) -> impl ExactSizeIterator<Item = &mut V> + use<'_, K, V> {
    let r = self.slack;
    let s = self.shift;
    let t = self.table;
    let u = self.value.cast_mut();
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        idx: ptr_diff(u.cast(), t),
        ptr: t,
        fun: move |_, i| unsafe { &mut *u.add(i) }
      };
    i
  }

  fn num_slots(&self) -> usize {
    let s = self.shift;
    let t = self.table;
    let u = self.value;
    if is_dummy::<K>(s) { return 0 }
    ptr_diff(u.cast(), t)
  }

  fn allocation_size(&self) -> usize {
    allocation_size::<K, V>(self.num_slots())
  }

  fn load_factor(&self) -> f64 {
    self.len() as f64 / self.num_slots() as f64
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
      x = unsafe { t.add(i).read() };
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
        let x = unsafe { t.add(i).read() };
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
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
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

impl<const N: usize, K: Key, V> From<[(K, V); N]> for HashMap<K, V> {
  fn from(value: [(K, V); N]) -> Self {
    Self::from_iter(value)
  }
}

impl<K: Key, V> FromIterator<(K, V)> for HashMap<K, V> {
  fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
    let mut t = Self::new();
    iter.into_iter().for_each(|(x, y)| { let _ = t.insert(x, y); });
    t
  }
}

pub mod internal {
  //! Unstable API exposing implementation details for benchmarks and tests.

  #![allow(missing_docs)]

  use super::HashMap;
  use super::Key;

  pub fn num_slots<K: Key, V>(t: &HashMap<K, V>) -> usize {
    t.num_slots()
  }

  pub fn allocation_size<K: Key, V>(t: &HashMap<K, V>) -> usize {
    t.allocation_size()
  }

  pub fn load_factor<K: Key, V>(t: &HashMap<K, V>) -> f64 {
    t.load_factor()
  }
}

#[allow(missing_docs)]
#[inline(never)]
pub fn get(t: &HashMap<core::num::NonZeroU32, usize>, key: core::num::NonZeroU32) -> Option<&usize> {
  t.get(key)
}

#[allow(missing_docs)]
#[inline(never)]
pub fn get_value(t: &HashMap<core::num::NonZeroU32, usize>, key: core::num::NonZeroU32) -> Option<usize> {
  match t.get(key) { None => None, Some(&y) => Some(y) }
}

#[allow(missing_docs)]
#[inline(never)]
pub fn contains_key(t: &HashMap<core::num::NonZeroU32, usize>, key: core::num::NonZeroU32) -> bool {
  t.contains_key(key)
}

#[allow(missing_docs)]
#[inline(never)]
pub fn insert(t: &mut HashMap<core::num::NonZeroU32, usize>, key: core::num::NonZeroU32, value: usize) {
  let _ = t.insert(key, value);
}

#[allow(missing_docs)]
#[inline(never)]
pub fn try_insert(t: &mut HashMap<core::num::NonZeroU32, usize>, key: core::num::NonZeroU32, value: usize) -> Result<&mut usize, (&mut usize, usize)> {
  t.try_insert(key, value)
}

#[allow(missing_docs)]
#[inline(never)]
pub fn remove(t: &mut HashMap<core::num::NonZeroU32, usize>, key: core::num::NonZeroU32) {
  let _ = t.remove(key);
}

#[allow(missing_docs)]
#[inline(never)]
pub fn clear(t: &mut HashMap<core::num::NonZeroU32, usize>) {
  t.clear();
}

#[allow(missing_docs)]
#[inline(never)]
pub fn reset(t: &mut HashMap<core::num::NonZeroU32, usize>) {
  t.reset();
}

#[allow(missing_docs)]
#[inline(never)]
pub fn len(t: &HashMap<core::num::NonZeroU32, usize>) -> usize {
  t.len()
}
