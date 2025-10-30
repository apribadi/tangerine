//! This module provides a fast hash map keyed by types representable as
//! `NonZeroU32` or `NonZeroU64`.

// TODO: IntoIterator
// TODO: drain
// TODO: shrink_to_fit
// TODO: try_insert

extern crate alloc;

use alloc::alloc::alloc_zeroed;
use alloc::alloc::dealloc;
use alloc::alloc::handle_alloc_error;
use core::alloc::Layout;
use core::cmp::max;
use core::iter::ExactSizeIterator;
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::mem::needs_drop;
use core::ops::Index;
use core::ops::IndexMut;
use core::panic::RefUnwindSafe;
use core::panic::UnwindSafe;
use core::ptr;
use rand_core::RngCore;

use crate::key::Key;

/// A fast hash map keyed by types representable as `NonZeroU32` or
/// `NonZeroU64`.

pub struct HashMap<K: Key, V> {
  seed0: K::Seed,
  seed1: K::Seed,
  table: *const Slot<K, V>, // covariant
  width: usize,
  slack: isize,
  limit: *const Slot<K, V>,
}

unsafe impl<K: Key, V: Send> Send for HashMap<K, V> {
}

unsafe impl<K: Key, V: Sync> Sync for HashMap<K, V> {
}

impl<K: Key, V: Unpin> Unpin for HashMap<K, V> {
}

impl<K: Key, V: UnwindSafe> UnwindSafe for HashMap<K, V> {
}

impl<K: Key, V: RefUnwindSafe> RefUnwindSafe for HashMap<K, V> {
}

// NB: We use `repr(C)` because the `hash` field MUST be at offset zero.

#[repr(C)]
struct Slot<K: Key, V> {
  hash: K::Hash,
  data: MaybeUninit<V>,
}

static EMPTY_TABLE: u64 = 0;

#[inline(always)]
fn ptr_wrapping_offset_from_unsigned<T>(x: *const T, y: *const T) -> usize {
  return x.addr().wrapping_sub(y.addr()) / size_of::<T>();
}

#[inline(always)]
fn capacity(w: usize) -> isize {
  return ((w >> 1) - (w >> 3)) as isize // ~ 0.375
}

#[inline(always)]
fn log2(x: usize) -> usize {
  return (usize::BITS - 1 - (x | 1).leading_zeros()) as usize;
}

impl<K: Key, V> HashMap<K, V> {
  #[inline(always)]
  fn internal_new(m: K::Seed) -> Self {
    Self {
      seed0: m,
      seed1: K::invert_seed(m),
      table: &raw const EMPTY_TABLE as *const Slot<K, V>,
      width: 1,
      slack: 0,
      limit: ptr::null(),
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
    let m = self.seed0;
    let t = self.table;
    let w = self.width;
    let h = K::hash(key, m);

    let mut a = t.wrapping_sub(K::slot(h, w));
    let mut x;

    loop {
      x = unsafe { ptr::read(&raw const (*a).hash) };
      if x <= h { break; }
      a = a.wrapping_add(1);
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

    let mut a = t.wrapping_sub(K::slot(h, w));
    let mut x;

    loop {
      x = unsafe { ptr::read(&raw const (*a).hash) };
      if x <= h { break; }
      a = a.wrapping_add(1);
    }

    if x != h { return None; }

    return Some(unsafe { (&*&raw const (*a).data).assume_init_ref() });
  }

  /// Returns a mutable reference to the value associated with the given key,
  /// if present.

  #[inline(always)]
  pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
    let m = self.seed0;
    let t = self.table as *mut Slot<K, V>;
    let w = self.width;
    let h = K::hash(key, m);

    let mut a = t.wrapping_sub(K::slot(h, w));
    let mut x;

    loop {
      x = unsafe { ptr::read(&raw const (*a).hash) };
      if x <= h { break; }
      a = a.wrapping_add(1);
    }

    if x != h { return None; }

    return Some(unsafe { (&mut *&raw mut (*a).data).assume_init_mut() });
  }

  // NB: The fact that `align_of::<T>` divides `size_of::<T>()` helps imply
  // that the layout of an array of `MAX_NUM_SLOTS` slots is valid, because
  // rounding up to the alignment won't increase the size.

  const MAX_NUM_SLOTS: usize = isize::MAX as usize / size_of::<Slot<K, V>>();

  #[inline(never)]
  #[cold]
  fn internal_init(&mut self, key: K, value: V) {
    let m = self.seed0;
    let w = 12;
    let e = 4;

    // TODO: round size up

    assert!(w + e <= Self::MAX_NUM_SLOTS);

    let align = align_of::<Slot<K, V>>();
    let size = (w + e) * size_of::<Slot<K, V>>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    let p = unsafe { alloc_zeroed(layout) } as *mut Slot<K, V>;

    if p.is_null() {
      match handle_alloc_error(layout) { /* ! */ }
    }

    let t = p.wrapping_add(w - 1);
    let l = p.wrapping_add(w + e - 1);
    let h = K::hash(key, m);
    let a = t.wrapping_sub(K::slot(h, w));

    unsafe { ptr::write(&raw mut (*a).hash, h) };
    unsafe { ptr::write(&raw mut (*a).data, MaybeUninit::new(value)) };

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
    let old_t = self.table as *mut Slot<K, V>;
    let old_w = self.width;
    let old_s = self.slack;
    let old_l = self.limit as *mut Slot<K, V>;
    let old_e = ptr_wrapping_offset_from_unsigned(old_l, old_t);
    let old_p = old_t.wrapping_sub(old_w - 1);
    let old_n = (capacity(old_w) - old_s) as usize;

    let old_l_hash = unsafe { ptr::read(&raw const (*old_l).hash) };
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
      unsafe { ptr::write(&raw mut (*old_l).hash, K::ZERO) };
      self.slack = old_s + 1;
    }

    let new_w = old_w + old_w / 4;
    let new_e = old_e + (log2(new_w) - log2(old_w)) + (is_overflow as usize);
    let new_s = old_s + (capacity(new_w) - capacity(old_w));

    // TODO: round size up

    // Panic if we would overflow the layout.

    assert!(new_w + new_e <= Self::MAX_NUM_SLOTS);

    let align = align_of::<Slot<K, V>>();
    let old_size = (old_w + old_e) * size_of::<Slot<K, V>>();
    let new_size = (new_w + new_e) * size_of::<Slot<K, V>>();
    let old_layout = unsafe { Layout::from_size_align_unchecked(old_size, align) };
    let new_layout = unsafe { Layout::from_size_align_unchecked(new_size, align) };

    let new_p = unsafe { alloc_zeroed(new_layout) } as *mut Slot<K, V>;

    if new_p.is_null() {
      match handle_alloc_error(new_layout) { /* ! */ }
    }

    // At this point, we know that allocating a new table has succeeded, so we
    // make sure to restore the last slot in case he had removed it earlier.

    unsafe { ptr::write(&raw mut (*old_l).hash, old_l_hash) };

    let new_t = new_p.wrapping_add(new_w - 1);
    let new_l = new_p.wrapping_add(new_w + new_e - 1);

    let mut a = old_p;
    let mut b = new_p;
    let mut n = old_n;

    loop {
      let x = unsafe { ptr::read(&raw const (*a).hash) };

      if x != K::ZERO {
        b = max(b, new_t.wrapping_sub(K::slot(x, new_w)));
        unsafe { ptr::write(&raw mut (*b).hash, x) }
        unsafe { ptr::write(&raw mut (*b).data, ptr::read(&raw const (*a).data)) };

        n -= 1;
        if n == 0 { break; }

        b = b.wrapping_add(1);
      }

      a = a.wrapping_add(1);
    }

    self.table = new_t;
    self.width = new_w;
    self.slack = new_s;
    self.limit = new_l;

    // The map is now in a valid state, even if `dealloc` panics.

    unsafe { dealloc(old_p as *mut u8, old_layout) };
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
    let l = self.limit as *mut Slot<K, V>;

    if l.is_null() {
      self.internal_init(key, value);

      return None;
    }

    let m = self.seed0;
    let t = self.table as *mut Slot<K, V>;
    let w = self.width;
    let h = K::hash(key, m);

    let mut a = t.wrapping_sub(K::slot(h, w));
    let mut x;

    loop {
      x = unsafe { ptr::read(&raw const (*a).hash) };
      if x <= h { break; }
      a = a.wrapping_add(1);
    }

    let value = MaybeUninit::new(value);

    if x == h {
      return Some(unsafe { ptr::replace(&raw mut (*a).data, value).assume_init() });
    }

    let mut y = value;

    unsafe { ptr::write(&raw mut (*a).hash, h) };

    while x != K::ZERO {
      y = unsafe { ptr::replace(&raw mut (*a).data, y) };
      a = a.wrapping_add(1);
      x = unsafe { ptr::replace(&raw mut (*a).hash, x) };
    }

    unsafe { ptr::write(&raw mut (*a).data, y) };

    let s = self.slack - 1;
    self.slack = s;

    if s < 0 || a == l { self.internal_grow(); }

    return None;
  }

  /// Removes the given key from the map. Returns the previous value associated
  /// with the given key, if one was present.

  #[inline(always)]
  pub fn remove(&mut self, key: K) -> Option<V> {
    let m = self.seed0;
    let t = self.table as *mut Slot<K, V>;
    let w = self.width;
    let h = K::hash(key, m);

    let mut a = t.wrapping_sub(K::slot(h, w));
    let mut x;

    loop {
      x = unsafe { ptr::read(&raw const (*a).hash) };
      if x <= h { break; }
      a = a.wrapping_add(1);
    }

    if x != h { return None; }

    self.slack += 1;

    let value = unsafe { ptr::read(&raw const (*a).data).assume_init() };

    let mut b = a.wrapping_add(1);

    loop {
      x = unsafe { ptr::read(&raw const (*b).hash) };

      if a < t.wrapping_sub(K::slot(x, w)) || /* unlikely */ x == K::ZERO { break; }

      unsafe { ptr::write(&raw mut (*a).hash, x) };
      unsafe { ptr::write(&raw mut (*a).data, ptr::read(&raw const (*b).data)) };
      a = b;
      b = b.wrapping_add(1);
    }

    unsafe { ptr::write(&raw mut (*a).hash, K::ZERO) };

    return Some(value)
  }

  /// Removes every item from the map. Retains heap-allocated memory.
  ///
  /// # Panics
  ///
  /// Panics if [`drop`]ping a value panics. If that happens, the map will be in
  /// a valid but otherwise unspecified state.

  pub fn clear(&mut self) {
    let l = self.limit as *mut Slot<K, V>;

    if l.is_null() { return; }

    let t = self.table as *mut Slot<K, V>;
    let w = self.width;
    let s = self.slack;
    let c = capacity(w);
    let n = (c - s) as usize;

    if n == 0 { return; }

    if needs_drop::<V>() {
      // WARNING!
      //
      // We must be careful to leave the map in a valid state even if a call to
      // `drop` panics.
      //
      // Here, we traverse the table in reverse order to ensure that we don't
      // remove an item that is currently displacing another item.
      //
      // Also, we update `self.slack` as we go instead of once at the end.

      let mut a = l;
      let mut n = n;
      let mut s = s;

      loop {
        if unsafe { ptr::read(&raw const (*a).hash) } != K::ZERO {
          unsafe { ptr::write(&raw mut (*a).hash, K::ZERO) };
          s += 1;
          self.slack = s;

          unsafe { ptr::drop_in_place(&raw mut (*a).data) };

          n -= 1;
          if n == 0 { break; }
        }

        a = a.wrapping_sub(1);
      }
    } else {
      let mut a = t.wrapping_sub(w - 1);

      loop {
        unsafe { ptr::write(&raw mut (*a).hash, K::ZERO) };
        if a == l { break; }
        a = a.wrapping_add(1);
      }

      self.slack = c;
    }
  }

  /// Removes every item from the map. Releases heap-allocated memory.
  ///
  /// # Panics
  ///
  /// Panics if [`drop`]ping a value or deallocating memory panics. If that
  /// happens, the map will be in a valid but otherwise unspecified state.

  pub fn reset(&mut self) {
    let l = self.limit as *mut Slot<K, V>;

    if l.is_null() { return; }

    let t = self.table as *mut Slot<K, V>;
    let w = self.width;
    let s = self.slack;
    let e = ptr_wrapping_offset_from_unsigned(l, t);
    let c = capacity(w);
    let n = (c - s) as usize;

    self.table = &raw const EMPTY_TABLE as *const Slot<K, V>;
    self.width = 1;
    self.slack = 0;
    self.limit = ptr::null();

    if needs_drop::<V>() && n != 0 {
      // WARNING!
      //
      // We must be careful to leave the map in a valid state even if a call to
      // `drop` panics.
      //
      // Here, we have already put `self` into the valid initial state, so if a
      // call to `drop` panics then we can just safely leak the table.

      let mut n = n;
      let mut a = t.wrapping_sub(w - 1);

      loop {
        if unsafe { ptr::read(&raw const (*a).hash) } != K::ZERO {
          unsafe { ptr::drop_in_place(&raw mut (*a).data) };

          n -= 1;
          if n == 0 { break; }
        }

        a = a.wrapping_add(1);
      }
    }

    let align = align_of::<Slot<K, V>>();
    let size = (w + e) * size_of::<Slot<K, V>>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };
    let p = t.wrapping_sub(w - 1);

    unsafe { dealloc(p as *mut u8, layout) };
  }

  /// Returns an iterator yielding each key and a reference to its associated
  /// value. The iterator item type is `(K, &'_ V)`.

  pub fn iter(&self) -> Iter<'_, K, V> {
    let m = self.seed1;
    let t = self.table;
    let w = self.width;
    let s = self.slack;

    let n = (capacity(w) - s) as usize;
    let a = t.wrapping_sub(w - 1);

    return Iter { size: n, slot: a, seed: m, _phantom_data: PhantomData };
  }

  /// Returns an iterator yielding each key and a mutable reference to its
  /// associated value. The iterator item type is `(K, &'_ mut V)`.

  pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
    let m = self.seed1;
    let t = self.table as *mut Slot<K, V>;
    let w = self.width;
    let s = self.slack;

    let n = (capacity(w) - s) as usize;
    let a = t.wrapping_sub(w - 1);

    return IterMut { size: n, slot: a, seed: m, _phantom_data: PhantomData };
  }

  /// Returns an iterator yielding each key. The iterator item type is `K`.

  pub fn keys(&self) -> Keys<'_, K, V> {
    let m = self.seed1;
    let t = self.table;
    let w = self.width;
    let s = self.slack;

    let n = (capacity(w) - s) as usize;
    let a = t.wrapping_sub(w - 1);

    return Keys { size: n, slot: a, seed: m, _phantom_data: PhantomData };
  }

  /// Returns an iterator yielding a reference to each value. The iterator item
  /// type is `&'_ V`.

  pub fn values(&self) -> Values<'_, K, V> {
    let t = self.table;
    let w = self.width;
    let s = self.slack;

    let n = (capacity(w) - s) as usize;
    let a = t.wrapping_sub(w - 1);

    return Values { size: n, slot: a, _phantom_data: PhantomData };
  }

  /// Returns an iterator yielding a mutable reference to each value. The
  /// iterator item type is `&'_ mut V`.

  pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
    let t = self.table as *mut Slot<K, V>;
    let w = self.width;
    let s = self.slack;

    let n = (capacity(w) - s) as usize;
    let a = t.wrapping_sub(w - 1);

    return ValuesMut { size: n, slot: a, _phantom_data: PhantomData };
  }

  fn internal_num_slots(&self) -> usize {
    let l = self.limit;

    if l.is_null() { return 0; }

    let t = self.table;
    let w = self.width;

    return ptr_wrapping_offset_from_unsigned(l, t) + w;
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
  slot: *const Slot<K, V>,
  seed: K::Seed,
  _phantom_data: PhantomData<&'a V>,
}

/// Iterator returned by [`HashMap::iter_mut`].

pub struct IterMut<'a, K: Key, V> {
  size: usize,
  slot: *mut Slot<K, V>,
  seed: K::Seed,
  _phantom_data: PhantomData<&'a mut V>,
}

/// Iterator returned by [`HashMap::keys`].

#[derive(Clone)]
pub struct Keys<'a, K: Key, V> {
  size: usize,
  slot: *const Slot<K, V>,
  seed: K::Seed,
  _phantom_data: PhantomData<&'a V>,
}

/// Iterator returned by [`HashMap::values`].

#[derive(Clone)]
pub struct Values<'a, K: Key, V> {
  size: usize,
  slot: *const Slot<K, V>,
  _phantom_data: PhantomData<&'a V>,
}

/// Iterator returned by [`HashMap::values_mut`].

pub struct ValuesMut<'a, K: Key, V> {
  size: usize,
  slot: *mut Slot<K, V>,
  _phantom_data: PhantomData<&'a mut V>,
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
    let n = self.size;

    if n == 0 { return None; }

    let mut a = self.slot;
    let mut x;

    loop {
      x = unsafe { ptr::read(&raw const (*a).hash) };
      if x != K::ZERO { break; }
      a = a.wrapping_add(1);
    }

    let x = unsafe { K::invert_hash(x, self.seed) };
    let y = unsafe { (&*&raw const (*a).data).assume_init_ref() };

    self.size = n - 1;
    self.slot = a.wrapping_add(1);

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
    let n = self.size;

    if n == 0 { return None; }

    let mut a = self.slot;
    let mut x;

    loop {
      x = unsafe { ptr::read(&raw const (*a).hash) };
      if x != K::ZERO { break; }
      a = a.wrapping_add(1);
    }

    let x = unsafe { K::invert_hash(x, self.seed) };
    let y = unsafe { (&mut *&raw mut (*a).data).assume_init_mut() };

    self.size = n - 1;
    self.slot = a.wrapping_add(1);

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
    let n = self.size;

    if n == 0 { return None; }

    let mut a = self.slot;
    let mut x;

    loop {
      x = unsafe { ptr::read(&raw const (*a).hash) };
      if x != K::ZERO { break; }
      a = a.wrapping_add(1);
    }

    let x = unsafe { K::invert_hash(x, self.seed) };

    self.size = n - 1;
    self.slot = a.wrapping_add(1);

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
    let n = self.size;

    if n == 0 { return None; }

    let mut a = self.slot;
    let mut x;

    loop {
      x = unsafe { ptr::read(&raw const (*a).hash) };
      if x != K::ZERO { break; }
      a = a.wrapping_add(1);
    }

    let y = unsafe { (&*&raw const (*a).data).assume_init_ref() };

    self.size = n - 1;
    self.slot = a.wrapping_add(1);

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
    let n = self.size;

    if n == 0 { return None; }

    let mut a = self.slot;
    let mut x;

    loop {
      x = unsafe { ptr::read(&raw const (*a).hash) };
      if x != K::ZERO { break; }
      a = a.wrapping_add(1);
    }

    let y = unsafe { (&mut *&raw mut (*a).data).assume_init_mut() };

    self.size = n - 1;
    self.slot = a.wrapping_add(1);

    return Some(y);
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    return (self.size, Some(self.size));
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
