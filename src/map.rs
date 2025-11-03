//! This module provides a fast hash map keyed by types representable as
//! `NonZeroU32` or `NonZeroU64`.

// TODO: Clone
// TODO: Debug
// TODO: IntoIterator
// TODO: drain
// TODO: shrink_to_fit
// TODO: try_insert

extern crate alloc;

use alloc::alloc::handle_alloc_error;
use core::alloc::Layout;
use core::cmp::max;
use core::iter::ExactSizeIterator;
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::mem::needs_drop;
use core::mem::offset_of;
use core::ops::Index;
use core::ops::IndexMut;
use pop::ptr;
use rand_core::RngCore;

use crate::key::Key;

/// A fast hash map keyed by types representable as `NonZeroU32` or
/// `NonZeroU64`.

pub struct HashMap<K: Key, V> {
  seed0: K::Seed,
  seed1: K::Seed,
  table: ptr,
  width: usize,
  slack: isize,
  limit: ptr,
  _phantom_data: PhantomData<(K, V)>,
}

// NB: We use `repr(C)` because the `hash` field MUST be at offset zero.

#[repr(C)]
struct Slot<K: Key, V> {
  hash: K::Hash,
  data: MaybeUninit<V>,
}

static EMPTY_TABLE: u64 = 0;

unsafe fn alloc_zeroed(size: usize, align: usize) -> ptr {
  let l = unsafe { Layout::from_size_align_unchecked(size, align) };
  let p = unsafe { pop::alloc_zeroed(l) };

  if p.is_null() {
    match handle_alloc_error(l) {
    }
  }

  return p;
}

unsafe fn dealloc(ptr: ptr, size: usize, align: usize) {
  unsafe { pop::dealloc(ptr, Layout::from_size_align_unchecked(size, align)) };
}

#[inline(always)]
fn capacity(w: usize) -> isize {
  return ((w >> 1) - (w >> 3)) as isize // ~ 0.375
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
  let m = 2 * n - 1;
  let k = usize::BITS - 1 - m.leading_zeros();
  let a = 1 << k;
  let b = a >> 1;
  return a | b & m;
}

#[inline(always)]
fn log2(n: usize) -> usize {
  debug_assert!(n >= 1);
  return (usize::BITS - 1 - n.leading_zeros()) as usize;
}

struct LayoutInfo {
  SLOT_STRIDE: usize,
  DATA_OFFSET: usize,
  ALIGN: usize,
  MAX_NUM_SLOTS: usize,
}

#[inline(always)]
const fn layout_info<K: Key, V>() -> LayoutInfo {
  // NB: The fact that `align_of::<T>` divides `size_of::<T>()` helps imply
  // that the layout of an array of `MAX_NUM_SLOTS` slots is valid, because
  // rounding up to the alignment won't increase the size.

  let SLOT_STRIDE = size_of::<Slot<K, V>>();
  let DATA_OFFSET = offset_of!(Slot<K, V>, data);
  let ALIGN = align_of::<Slot<K, V>>();
  let MAX_NUM_SLOTS = isize::MAX as usize / size_of::<Slot<K, V>>();

  return LayoutInfo { SLOT_STRIDE, DATA_OFFSET, ALIGN, MAX_NUM_SLOTS };
}

impl<K: Key, V> HashMap<K, V> {
  #[inline(always)]
  fn internal_new(m: K::Seed) -> Self {
    Self {
      seed0: m,
      seed1: K::invert_seed(m),
      table: ptr::from(&EMPTY_TABLE),
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

    return (capacity(w) - s) as usize;
  }

  /// Returns whether the map contains zero items.

  #[inline(always)]
  pub fn is_empty(&self) -> bool {
    return self.len() == 0;
  }

  /// Returns whether the map contains the given key.

  #[inline(always)]
  pub fn contains_key(&self, key: K) -> bool {
    let I = layout_info::<K, V>();
    let m = self.seed0;
    let t = self.table;
    let w = self.width;
    let h = K::hash(key, m);

    let mut a = t - I.SLOT_STRIDE * K::slot(h, w);
    let mut x = unsafe { a.read::<K::Hash>() };

    while x > h {
      a = a + I.SLOT_STRIDE;
      x = unsafe { a.read::<K::Hash>() };
    }

    return x == h;
  }

  /// Returns a reference to the value associated with the given key, if
  /// present.

  #[inline(always)]
  pub fn get(&self, key: K) -> Option<&V> {
    let I = layout_info::<K, V>();
    let m = self.seed0;
    let t = self.table;
    let w = self.width;
    let h = K::hash(key, m);

    let mut a = t - I.SLOT_STRIDE * K::slot(h, w);
    let mut x = unsafe { a.read::<K::Hash>() };

    while x > h {
      a = a + I.SLOT_STRIDE;
      x = unsafe { a.read::<K::Hash>() };
    }

    if x != h { return None; }

    return Some(unsafe { (a + I.DATA_OFFSET).as_ref::<V>() });
  }

  /// Returns a mutable reference to the value associated with the given key,
  /// if present.

  #[inline(always)]
  pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
    let I = layout_info::<K, V>();
    let m = self.seed0;
    let t = self.table;
    let w = self.width;
    let h = K::hash(key, m);

    let mut a = t - I.SLOT_STRIDE * K::slot(h, w);
    let mut x = unsafe { a.read::<K::Hash>() };

    while x > h {
      a = a + I.SLOT_STRIDE;
      x = unsafe { a.read::<K::Hash>() };
    }

    if x != h { return None; }

    return Some(unsafe { (a + I.DATA_OFFSET).as_mut_ref::<V>() });
  }

  #[inline(never)]
  #[cold]
  fn internal_init(&mut self, key: K, value: V) {
    let I = layout_info::<K, V>();
    let m = self.seed0;
    let w = 12;
    let e = 4;
    let d = w + e;

    assert!(d <= I.MAX_NUM_SLOTS);

    let size = d * I.SLOT_STRIDE;
    let p = unsafe { alloc_zeroed(size, I.ALIGN) };

    let t = p + I.SLOT_STRIDE * (w - 1);
    let l = p + I.SLOT_STRIDE * (d - 1);
    let h = K::hash(key, m);
    let a = t - I.SLOT_STRIDE * K::slot(h, w);

    unsafe { a.write(h) };
    unsafe { (a + I.DATA_OFFSET).write(value) };

    // We only modify `self` after we know that allocation has succeeded so
    // that the hash map will still be valid after a panic.

    self.table = t;
    self.width = w;
    self.slack = capacity(w) - 1;
    self.limit = l;
  }

  #[inline(never)]
  #[cold]
  fn internal_grow(&mut self) {
    let I = layout_info::<K, V>();
    let old_t = self.table;
    let old_w = self.width;
    let old_s = self.slack;
    let old_l = self.limit;
    let old_e = (old_l - old_t) / I.SLOT_STRIDE;
    let old_d = old_w + old_e;
    let old_p = old_t - I.SLOT_STRIDE * (old_w - 1);
    let old_n = (capacity(old_w) - old_s) as usize;

    let old_l_hash = unsafe { old_l.read::<K::Hash>() };
    let is_overflow = old_l_hash != K::ZERO;

    // WARNING!
    //
    // We must be careful to leave the map in a valid state even if attempting
    // to allocate a new table results in a panic.
    //
    // It turns out that the `self.slack < 0` state actually *is* valid, but
    // the `is_overflow` state *is not* valid.
    //
    // In the latter case, we temporarily remove the item in the final slot and
    // restore it after we have succeeded at allocating a new table.
    //
    // This is an instance of the infamous PPYP design pattern.

    if is_overflow {
      unsafe { old_l.write(K::ZERO) };
      self.slack = old_s + 1;
    }

    let new_d = increment_size_class(old_d * I.SLOT_STRIDE) / I.SLOT_STRIDE;
    let new_e = old_e + (log2(new_d) - log2(old_d)) + (is_overflow as usize);
    let new_w = new_d - new_e;
    let new_s = old_s + (capacity(new_w) - capacity(old_w));

    // Panic if we would overflow the layout.

    assert!(new_d <= I.MAX_NUM_SLOTS);

    let old_size = old_d * I.SLOT_STRIDE;
    let new_size = new_d * I.SLOT_STRIDE;

    let new_p = unsafe { alloc_zeroed(new_size, I.ALIGN) };

    // At this point we know that allocating a new table has succeeded. We
    // make sure to re-write the last slot before copying from the old table to
    // the new table.

    unsafe { old_l.write(old_l_hash) };

    let new_t = new_p + I.SLOT_STRIDE * (new_w - 1);
    let new_l = new_p + I.SLOT_STRIDE * (new_d - 1);

    let mut a = old_p;
    let mut b = new_p;
    let mut n = old_n;

    loop {
      let x = unsafe { a.read::<K::Hash>() };

      if x != K::ZERO {
        b = max(b, new_t - I.SLOT_STRIDE * K::slot(x, new_w));

        unsafe { b.write(x) }
        unsafe { (b + I.DATA_OFFSET).write((a + I.DATA_OFFSET).read::<V>()) };

        n -= 1;
        if n == 0 { break; }

        b = b + I.SLOT_STRIDE;
      }

      a = a + I.SLOT_STRIDE;
    }

    self.table = new_t;
    self.width = new_w;
    self.slack = new_s;
    self.limit = new_l;

    // The map is now in a valid state, even if `dealloc` panics.

    unsafe { dealloc(old_p, old_size, I.ALIGN) };
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
    let I = layout_info::<K, V>();
    let l = self.limit;

    if l.is_null() {
      self.internal_init(key, value);

      return None;
    }

    let m = self.seed0;
    let t = self.table;
    let w = self.width;
    let h = K::hash(key, m);

    let mut a = t - I.SLOT_STRIDE * K::slot(h, w);
    let mut x = unsafe { a.read::<K::Hash>() };

    while x > h {
      a = a + I.SLOT_STRIDE;
      x = unsafe { a.read::<K::Hash>() };
    }

    if x == h {
      return Some(unsafe { (a + I.DATA_OFFSET).replace(value) });
    }

    let mut y = value;

    unsafe { a.write(h) };

    while x != K::ZERO {
      y = unsafe { (a + I.DATA_OFFSET).replace(y) };
      a = a + I.SLOT_STRIDE;
      x = unsafe { a.replace(x) };
    }

    unsafe { (a + I.DATA_OFFSET).write(y) };

    let s = self.slack - 1;
    self.slack = s;

    if s < 0 || a == l { self.internal_grow(); }

    return None;
  }

  /// Removes the given key from the map. Returns the previous value associated
  /// with the given key, if one was present.

  #[inline(always)]
  pub fn remove(&mut self, key: K) -> Option<V> {
    let I = layout_info::<K, V>();
    let m = self.seed0;
    let t = self.table;
    let w = self.width;
    let h = K::hash(key, m);

    let mut a = t - I.SLOT_STRIDE * K::slot(h, w);
    let mut x = unsafe { a.read::<K::Hash>() };

    while x > h {
      a = a + I.SLOT_STRIDE;
      x = unsafe { a.read::<K::Hash>() };
    }

    if x != h { return None; }

    self.slack += 1;

    let value = unsafe { (a + I.DATA_OFFSET).read::<V>() };
    let mut a = a;
    let mut b = a + I.SLOT_STRIDE;
    let mut x = unsafe { b.read::<K::Hash>() };

    while t - I.SLOT_STRIDE * K::slot(x, w) <= a && /* likely */ x != K::ZERO {
      unsafe { a.write(x) };
      unsafe { (a + I.DATA_OFFSET).write((b + I.DATA_OFFSET).read::<V>()) };
      a = b;
      b = b + I.SLOT_STRIDE;
      x = unsafe { b.read::<K::Hash>() };
    }

    unsafe { a.write(K::ZERO) };

    return Some(value);
  }

  /// Removes every item from the map. Retains heap-allocated memory.
  ///
  /// # Panics
  ///
  /// Panics if [`drop`]ping a value panics. If that happens, the map will be in
  /// a valid but otherwise unspecified state.

  pub fn clear(&mut self) {
    let I = layout_info::<K, V>();
    let l = self.limit;

    if l.is_null() { return; }

    let t = self.table;
    let w = self.width;
    let s = self.slack;
    let c = capacity(w);
    let n = (c - s) as usize;

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
          if unsafe { a.read::<K::Hash>() } != K::ZERO {
            unsafe { a.write(K::ZERO) };

            s += 1;
            self.slack = s;

            unsafe { (a + I.DATA_OFFSET).drop_in_place::<V>() };

            n -= 1;
            if n == 0 { break; }
          }

          a = a - I.SLOT_STRIDE;
        }
      }
    } else {
      if n != 0 {
        let mut a = t - I.SLOT_STRIDE * (w - 1);

        while a <= l {
          unsafe { a.write(K::ZERO) };
          a = a + I.SLOT_STRIDE;
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
    let I = layout_info::<K, V>();
    let l = self.limit;

    if l.is_null() { return; }

    let t = self.table;
    let w = self.width;
    let s = self.slack;
    let e = (l - t) / I.SLOT_STRIDE;
    let d = w + e;
    let c = capacity(w);
    let n = (c - s) as usize;

    self.table = ptr::from(&EMPTY_TABLE);
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
        let mut a = t - I.SLOT_STRIDE * (w - 1);

        loop {
          if unsafe { a.read::<K::Hash>() } != K::ZERO {
            unsafe { (a + I.DATA_OFFSET).drop_in_place::<V>() };

            n -= 1;
            if n == 0 { break; }
          }

          a = a + I.SLOT_STRIDE;
        }
      }
    }

    let size = d * I.SLOT_STRIDE;
    let p = t - I.SLOT_STRIDE * (w - 1);

    unsafe { dealloc(p, size, I.ALIGN) };
  }

  /// Returns an iterator yielding each key and a reference to its associated
  /// value. The iterator item type is `(K, &'_ V)`.

  pub fn iter(&self) -> Iter<'_, K, V> {
    let I = layout_info::<K, V>();
    let m = self.seed1;
    let t = self.table;
    let w = self.width;
    let s = self.slack;

    let n = (capacity(w) - s) as usize;
    let a = t - I.SLOT_STRIDE * (w - 1);

    return Iter { size: n, slot: a, seed: m, _phantom_data: PhantomData };
  }

  /// Returns an iterator yielding each key and a mutable reference to its
  /// associated value. The iterator item type is `(K, &'_ mut V)`.

  pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
    let I = layout_info::<K, V>();
    let m = self.seed1;
    let t = self.table;
    let w = self.width;
    let s = self.slack;

    let n = (capacity(w) - s) as usize;
    let a = t - I.SLOT_STRIDE * (w - 1);

    return IterMut { size: n, slot: a, seed: m, _phantom_data: PhantomData };
  }

  /// Returns an iterator yielding each key. The iterator item type is `K`.

  pub fn keys(&self) -> Keys<'_, K, V> {
    let I = layout_info::<K, V>();
    let m = self.seed1;
    let t = self.table;
    let w = self.width;
    let s = self.slack;

    let n = (capacity(w) - s) as usize;
    let a = t - I.SLOT_STRIDE * (w - 1);

    return Keys { size: n, slot: a, seed: m, _phantom_data: PhantomData };
  }

  /// Returns an iterator yielding a reference to each value. The iterator item
  /// type is `&'_ V`.

  pub fn values(&self) -> Values<'_, K, V> {
    let I = layout_info::<K, V>();
    let t = self.table;
    let w = self.width;
    let s = self.slack;

    let n = (capacity(w) - s) as usize;
    let a = t - I.SLOT_STRIDE * (w - 1);

    return Values { size: n, slot: a, _phantom_data: PhantomData };
  }

  /// Returns an iterator yielding a mutable reference to each value. The
  /// iterator item type is `&'_ mut V`.

  pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
    let I = layout_info::<K, V>();
    let t = self.table;
    let w = self.width;
    let s = self.slack;

    let n = (capacity(w) - s) as usize;
    let a = t - I.SLOT_STRIDE * (w - 1);

    return ValuesMut { size: n, slot: a, _phantom_data: PhantomData };
  }

  fn internal_num_slots(&self) -> usize {
    let I = layout_info::<K, V>();
    let l = self.limit;

    if l.is_null() { return 0; }

    let t = self.table;
    let w = self.width;

    return (l - t) / I.SLOT_STRIDE + w;
  }

  fn internal_allocation_size(&self) -> usize {
    let I = layout_info::<K, V>();

    return self.internal_num_slots() * I.SLOT_STRIDE;
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
  fn index(&self, key: K) -> &V {
    return self.get(key).unwrap();
  }
}

impl<K: Key, V> IndexMut<K> for HashMap<K, V> {
  #[inline(always)]
  fn index_mut(&mut self, key: K) -> &mut V {
    return self.get_mut(key).unwrap();
  }
}

/// Iterator returned by [`HashMap::iter`].

#[derive(Clone)]
pub struct Iter<'a, K: Key, V> {
  size: usize,
  slot: ptr,
  seed: K::Seed,
  _phantom_data: PhantomData<(&'a K, &'a V)>,
}

/// Iterator returned by [`HashMap::iter_mut`].

pub struct IterMut<'a, K: Key, V> {
  size: usize,
  slot: ptr,
  seed: K::Seed,
  _phantom_data: PhantomData<(&'a K, &'a mut V)>,
}

/// Iterator returned by [`HashMap::keys`].

#[derive(Clone)]
pub struct Keys<'a, K: Key, V> {
  size: usize,
  slot: ptr,
  seed: K::Seed,
  _phantom_data: PhantomData<(&'a K, &'a V)>,
}

/// Iterator returned by [`HashMap::values`].

#[derive(Clone)]
pub struct Values<'a, K: Key, V> {
  size: usize,
  slot: ptr,
  _phantom_data: PhantomData<(&'a K, &'a V)>,
}

/// Iterator returned by [`HashMap::values_mut`].

pub struct ValuesMut<'a, K: Key, V> {
  size: usize,
  slot: ptr,
  _phantom_data: PhantomData<(&'a K, &'a mut V)>,
}

impl<'a, K: Key, V> FusedIterator for Iter<'a, K, V> {
}

impl<'a, K: Key, V> FusedIterator for IterMut<'a, K, V> {
}

impl<'a, K: Key, V> FusedIterator for Keys<'a, K, V> {
}

impl<'a, K: Key, V> FusedIterator for Values<'a, K, V> {
}

impl<'a, K: Key, V> FusedIterator for ValuesMut<'a, K, V> {
}

impl<'a, K: Key, V> ExactSizeIterator for Iter<'a, K, V> {
  #[inline(always)]
  fn len(&self) -> usize {
    return self.size;
  }
}

impl<'a, K: Key, V> ExactSizeIterator for IterMut<'a, K, V> {
  #[inline(always)]
  fn len(&self) -> usize {
    return self.size;
  }
}

impl<'a, K: Key, V> ExactSizeIterator for Keys<'a, K, V> {
  #[inline(always)]
  fn len(&self) -> usize {
    return self.size;
  }
}

impl<'a, K: Key, V> ExactSizeIterator for Values<'a, K, V> {
  #[inline(always)]
  fn len(&self) -> usize {
    return self.size;
  }
}

impl<'a, K: Key, V> ExactSizeIterator for ValuesMut<'a, K, V> {
  #[inline(always)]
  fn len(&self) -> usize {
    return self.size;
  }
}

impl<'a, K: Key, V> Iterator for Iter<'a, K, V> {
  type Item = (K, &'a V);

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let I = layout_info::<K, V>();
    let n = self.size;

    if n == 0 { return None; }

    let mut a = self.slot;
    let mut x = unsafe { a.read::<K::Hash>() };

    while x == K::ZERO {
      a = a + I.SLOT_STRIDE;
      x = unsafe { a.read::<K::Hash>() };
    }

    let x = unsafe { K::invert_hash(x, self.seed) };
    let y = unsafe { (a + I.DATA_OFFSET).as_ref::<V>() };

    self.size = n - 1;
    self.slot = a + I.SLOT_STRIDE;

    return Some((x, y));
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    return (self.size, Some(self.size));
  }
}

impl<'a, K: Key, V> Iterator for IterMut<'a, K, V> {
  type Item = (K, &'a mut V);

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let I = layout_info::<K, V>();
    let n = self.size;

    if n == 0 { return None; }

    let mut a = self.slot;
    let mut x = unsafe { a.read::<K::Hash>() };

    while x == K::ZERO {
      a = a + I.SLOT_STRIDE;
      x = unsafe { a.read::<K::Hash>() };
    }

    let x = unsafe { K::invert_hash(x, self.seed) };
    let y = unsafe { (a + I.DATA_OFFSET).as_mut_ref::<V>() };

    self.size = n - 1;
    self.slot = a + I.SLOT_STRIDE;

    return Some((x, y));
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    return (self.size, Some(self.size));
  }
}

impl<'a, K: Key, V> Iterator for Keys<'a, K, V> {
  type Item = K;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let I = layout_info::<K, V>();
    let n = self.size;

    if n == 0 { return None; }

    let mut a = self.slot;
    let mut x = unsafe { a.read::<K::Hash>() };

    while x == K::ZERO {
      a = a + I.SLOT_STRIDE;
      x = unsafe { a.read::<K::Hash>() };
    }

    let x = unsafe { K::invert_hash(x, self.seed) };

    self.size = n - 1;
    self.slot = a + I.SLOT_STRIDE;

    return Some(x);
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    return (self.size, Some(self.size));
  }
}

impl<'a, K: Key, V> Iterator for Values<'a, K, V> {
  type Item = &'a V;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let I = layout_info::<K, V>();
    let n = self.size;

    if n == 0 { return None; }

    let mut a = self.slot;
    let mut x = unsafe { a.read::<K::Hash>() };

    while x == K::ZERO {
      a = a + I.SLOT_STRIDE;
      x = unsafe { a.read::<K::Hash>() };
    }

    let y = unsafe { (a + I.DATA_OFFSET).as_ref::<V>() };

    self.size = n - 1;
    self.slot = a + I.SLOT_STRIDE;

    return Some(y);
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    return (self.size, Some(self.size));
  }
}

impl<'a, K: Key, V> Iterator for ValuesMut<'a, K, V> {
  type Item = &'a mut V;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let I = layout_info::<K, V>();
    let n = self.size;

    if n == 0 { return None; }

    let mut a = self.slot;
    let mut x = unsafe { a.read::<K::Hash>() };

    while x == K::ZERO {
      a = a + I.SLOT_STRIDE;
      x = unsafe { a.read::<K::Hash>() };
    }

    let y = unsafe { (a + I.DATA_OFFSET).as_mut_ref::<V>() };

    self.size = n - 1;
    self.slot = a + I.SLOT_STRIDE;

    return Some(y);
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    return (self.size, Some(self.size));
  }
}

impl<K: Key, V> Default for HashMap<K, V> {
  fn default() -> Self {
    return Self::new();
  }
}

pub mod internal {
  //! Unstable API exposing implementation details for benchmarks and tests.

  #![allow(missing_docs)]

  use super::*;

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
