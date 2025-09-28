//! This module implements a fast hash map keyed by `NonZeroU64`s.

extern crate alloc;

use alloc::alloc::dealloc;
use core::alloc::Layout;
use core::mem::MaybeUninit;
use core::mem::needs_drop;
use core::num::NonZeroU64;
use core::ops::Index;
use core::ops::IndexMut;
use core::ptr;
use dandelion::Rng;

/// A fast hash map keyed by `NonZeroU64`s.

pub struct HashMapNZ64<T> {
  seeds: Seeds,
  table: *const Item<T>, // covariant in `T`
  width: usize,
  space: isize,
  limit: *const Item<T>,
}

unsafe impl<T: Send> Send for HashMapNZ64<T> {
}

unsafe impl<T: Sync> Sync for HashMapNZ64<T> {
}

static EMPTY: u64 = 0;

#[derive(Clone, Copy)]
struct Seeds(u64, u64);

#[repr(C)]
struct Item<T> {
  hash: u64,
  data: MaybeUninit<T>,
}

#[inline(always)]
fn ptr_wrapping_offset_from_unsigned<T>(x: *const T, y: *const T) -> usize {
  return x.addr().wrapping_sub(y.addr()) / size_of::<T>();
}

#[inline(always)]
fn umulh(x: u64, y: u64) -> u64 {
  return ((x as u128 * y as u128) >> 64) as u64;
}

#[inline(always)]
fn slot(h: u64, w: usize) -> usize {
  return umulh(h, w as u64) as usize;
}

#[inline(always)]
fn hash(x: u64, Seeds(a, b): Seeds) -> u64 {
  let x = x.wrapping_mul(a);
  let x = x.swap_bytes();
  let x = x.wrapping_mul(b);
  return x;
}

#[inline(always)]
fn capacity(w: usize) -> usize {
  return (w >> 1) - (w >> 3) // ~ 0.375
}

impl<T> HashMapNZ64<T> {
  const FOO: usize = size_of::<T>();

  #[inline(always)]
  fn from_seeds(a: u64, b: u64) -> Self {
    Self {
      seeds: Seeds(a | 1, b | 1),
      table: &raw const EMPTY as *const Item<T>,
      width: 1,
      space: 0,
      limit: ptr::null(),
    }
  }

  /// Creates an empty map, seeding the hash function from a thread-local
  /// random number generator.

  #[inline]
  pub fn new() -> Self {
    let seeds = u128::from_le_bytes(dandelion::thread_local::byte_array());
    return Self::from_seeds(seeds as u64, (seeds >> 64) as u64);
  }

  /// Creates an empty map, seeding the hash function from the given random
  /// number generator.

  #[inline]
  pub fn new_seeded(rng: &mut Rng) -> Self {
    return Self::from_seeds(rng.u64(), rng.u64());
  }

  /// Returns the number of items.

  #[inline]
  pub fn len(&self) -> usize {
    let w = self.width;
    let s = self.space;

    return (capacity(w) as isize - s) as usize;
  }

  /// Returns whether the map contains zero items.

  #[inline]
  pub fn is_empty(&self) -> bool {
    return self.len() == 0;
  }

  /// Returns whether the map contains the given key.

  #[inline]
  pub fn contains_key(&self, key: NonZeroU64) -> bool {
    let m = self.seeds;
    let t = self.table;
    let w = self.width;
    let h = hash(key.get(), m);

    let mut a = t.wrapping_sub(slot(h, w));
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

  #[inline]
  pub fn get(&self, key: NonZeroU64) -> Option<&T> {
    let m = self.seeds;
    let t = self.table;
    let w = self.width;
    let h = hash(key.get(), m);

    let mut a = t.wrapping_sub(slot(h, w));
    let mut x;

    loop {
      x = unsafe { ptr::read(&raw const (*a).hash) };

      if x <= h { break; }

      a = a.wrapping_add(1);
    }

    if x != h { return None; }

    return Some(unsafe { (&*&raw const (*a).data).assume_init_ref() });
  }

  /// Returns a mutable mut to the value associated with the given key, if
  /// present.

  #[inline]
  pub fn get_mut(&mut self, key: NonZeroU64) -> Option<&mut T> {
    let m = self.seeds;
    let t = self.table as *mut Item<T>;
    let w = self.width;
    let h = hash(key.get(), m);

    let mut a = t.wrapping_sub(slot(h, w));
    let mut x;

    loop {
      x = unsafe { ptr::read(&raw const (*a).hash) };

      if x <= h { break; }

      a = a.wrapping_add(1);
    }

    if x != h { return None; }

    return Some(unsafe { (&mut *&raw mut (*a).data).assume_init_mut() });
  }

  #[inline(never)]
  #[cold]
  fn init_table(&mut self, key: NonZeroU64, value: T) {
    // assert!(INITIAL_N <= isize::MAX as usize / size_of::<Slot<T>>());
    /*

    const INITIAL_E: usize = 4;
    const INITIAL_W: usize = 20;

    let align = align_of::<Item<T>>();
    let size = INITIAL_N * size_of::<Item<T>>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    let a = unsafe { alloc::alloc::alloc_zeroed(layout) } as *mut Slot<T>;
    if a.is_null() { match alloc::alloc::handle_alloc_error(layout) {} }

    let t = unsafe { a.add(INITIAL_D - 1) };
    let b = unsafe { a.add(INITIAL_N - 1) };

    let m = self.seeds;
    let h = hash(m, key).get();
    let p = unsafe { t.offset(- spot(INITIAL_S, h)) };

    unsafe { &mut *p }.hash = h;
    unsafe { &mut *p }.data = MaybeUninit::new(value);

    // We only modify `self` after we know that allocation has succeeded.

    self.table = t;
    self.shift = INITIAL_S;
    self.space = INITIAL_R - 1;
    self.check = b;
    */
  }

  #[inline(never)]
  #[cold]
  fn grow_table(&mut self) {
    let _: _ = self;
    self.space = 13;
  }

  /// Inserts the given key and value into the map. Returns the previous value
  /// associated with given key, if one was present.
  ///
  /// # Panics
  ///
  /// Panics when allocation fails. If that happens, it is possible for the map
  /// to leak an arbitrary set of items, but the map will remain in a valid
  /// state.

  #[inline]
  pub fn insert(&mut self, key: NonZeroU64, value: T) -> Option<T> {
    let l = self.limit as *mut Item<T>;

    if l.is_null() {
      self.init_table(key, value);

      return None;
    }

    let m = self.seeds;
    let t = self.table as *mut Item<T>;
    let w = self.width;
    let h = hash(key.get(), m);

    let mut a = t.wrapping_sub(slot(h, w));
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

    while x != 0 {
      y = unsafe { ptr::replace(&raw mut (*a).data, y) };
      a = a.wrapping_add(1);
      x = unsafe { ptr::replace(&raw mut (*a).hash, x) };
    }

    unsafe { ptr::write(&raw mut (*a).data, y) };

    let s = self.space - 1;
    self.space = s;

    if s < 0 || a == l { self.grow_table(); }

    return None;
  }

  /// Removes the given key from the map. Returns the previous value associated
  /// with the given key, if one was present.

  #[inline]
  pub fn remove(&mut self, key: NonZeroU64) -> Option<T> {
    let m = self.seeds;
    let t = self.table as *mut Item<T>;
    let w = self.width;
    let h = hash(key.get(), m);

    let mut a = t.wrapping_sub(slot(h, w));
    let mut x;

    loop {
      x = unsafe { ptr::read(&raw const (*a).hash) };

      if x <= h { break; }

      a = a.wrapping_add(1);
    }

    if x != h { return None; }

    self.space += 1;

    let value = unsafe { ptr::read(&raw mut (*a).data).assume_init() };

    let mut b = a.wrapping_add(1);

    loop {
      x = unsafe { ptr::read(&raw const (*b).hash) };

      if a < t.wrapping_sub(slot(x, w)) || /* unlikely */ x == 0 { break; }

      unsafe { ptr::write(&raw mut (*a).hash, x) };
      unsafe { ptr::write(&raw mut (*a).data, ptr::read(&raw const (*b).data)) };
      a = b;
      b = b.wrapping_add(1);
    }

    unsafe { ptr::write(&raw mut (*a).hash, 0) };

    return Some(value)
  }

  /// Removes every item from the map. Retains heap-allocated memory.

  pub fn clear(&mut self) {
    let l = self.limit as *mut Item<T>;

    if l.is_null() { return; }

    let t = self.table as *mut Item<T>;
    let w = self.width;
    let s = self.space;
    let c = capacity(w);
    let k = (c as isize - s) as usize;
    let p = t.wrapping_sub(w - 1);

    if k == 0 { return; }

    if needs_drop::<T>() {
      // WARNING!
      //
      // We must be careful to leave the map in a valid state even if a call to
      // `drop` panics.
      //
      // Here, we traverse the table in reverse order to ensure that we don't
      // remove an item that is currently displacing another item.
      //
      // Also, we update `self.space` as we go instead of once at the end.

      let mut a = l;
      let mut k = k;
      let mut s = s;

      loop {
        if unsafe { ptr::read(&raw const (*a).hash) } != 0 {
          unsafe { ptr::write(&raw mut (*a).hash, 0) };
          k -= 1;
          s += 1;
          self.space = s;
          unsafe { ptr::drop_in_place(&raw mut (*a).data) };

          if k == 0 { break; }
        }

        a = a.wrapping_sub(1);
      }
    } else {
      let mut a = p;

      loop {
        unsafe { ptr::write(&raw mut (*a).hash, 0) };

        if a == l { break; }

        a = a.wrapping_add(1);
      }

      self.space = c as isize;
    }
  }

  /// Removes every item from the map. Releases heap-allocated memory.

  pub fn reset(&mut self) {
    let l = self.limit as *mut Item<T>;

    if l.is_null() { return; }

    let t = self.table as *mut Item<T>;
    let w = self.width;
    let s = self.space;
    let c = capacity(w);
    let k = (c as isize - s) as usize;
    let p = t.wrapping_sub(w - 1);

    self.table = &raw const EMPTY as *const Item<T>;
    self.width = 1;
    self.space = 0;
    self.limit = ptr::null();

    if needs_drop::<T>() && k != 0 {
      // WARNING!
      //
      // We must be careful to leave the map in a valid state even if a call to
      // `drop` panics.
      //
      // Here, we have already put `self` into the valid initial state, so if a
      // call to `drop` panics then we can just safely leak the table.

      let mut k = k;
      let mut a = p;

      loop {
        if unsafe { ptr::read(&raw const (*a).hash) } != 0 {
          k -= 1;
          unsafe { ptr::drop_in_place(&raw mut (*a).data) };

          if k == 0 { break; }
        }

        a = a.wrapping_add(1);
      }
    }

    let align = align_of::<Item<T>>();
    let n = ptr_wrapping_offset_from_unsigned(l, t) + w;
    let size = n * size_of::<Item<T>>();

    unsafe { dealloc(p as _, Layout::from_size_align_unchecked(size, align)) };
  }

  fn num_slots(&self) -> usize {
    let l = self.limit;

    if l.is_null() { return 0; }

    let t = self.table;
    let w = self.width;

    return ptr_wrapping_offset_from_unsigned(l, t) + w;
  }

  fn num_bytes(&self) -> usize {
    return self.num_slots() * size_of::<Item<T>>();
  }

  fn load(&self) -> f64 {
    // NB: NaN if no allocation
    return self.len() as f64 / self.num_slots() as f64;
  }
}

impl<T> Drop for HashMapNZ64<T> {
  fn drop(&mut self) {
    self.reset()
  }
}

impl<T> Index<NonZeroU64> for HashMapNZ64<T> {
  type Output = T;

  #[inline]
  fn index(&self, key: NonZeroU64) -> &T {
    return self.get(key).unwrap();
  }
}

impl<T> IndexMut<NonZeroU64> for HashMapNZ64<T> {
  #[inline]
  fn index_mut(&mut self, key: NonZeroU64) -> &mut T {
    return self.get_mut(key).unwrap();
  }
}

pub mod internal {
  //! Unstable API exposing implementation details for tests and benchmarks.

  use super::*;

  pub fn num_slots<T>(t: &HashMapNZ64<T>) -> usize {
    return t.num_slots();
  }

  pub fn num_bytes<T>(t: &HashMapNZ64<T>) -> usize {
    return t.num_bytes();
  }

  pub fn load<T>(t: &HashMapNZ64<T>) -> f64 {
    return t.load();
  }
}
