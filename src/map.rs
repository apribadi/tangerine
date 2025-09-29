//! This module implements a fast hash map keyed by `NonZeroU64`s.

extern crate alloc;

use alloc::alloc::dealloc;
use core::alloc::Layout;
use core::mem::MaybeUninit;
use core::mem::needs_drop;
use core::num::NonZeroU32;
use core::num::NonZeroU64;
use core::ops::Index;
use core::ops::IndexMut;
use core::panic::RefUnwindSafe;
use core::panic::UnwindSafe;
use core::ptr;
use rand_core::RngCore;

/// A sealed trait for hash map keys, implemented only by `NonZeroU32` and
/// `NonZeroU64`.

pub trait Key: private::Key {
}

impl Key for NonZeroU32 {
}

impl Key for NonZeroU64 {
}

/// A fast hash map keyed by `NonZeroU32`s or `NonZeroU64`s.

pub struct HashMap<K: Key, V> {
  seed: K::Seed,
  table: *const Slot<K, V>, // covariant
  width: usize,
  slack: isize,
  last: *const Slot<K, V>,
}

impl<K: Key, V: RefUnwindSafe> RefUnwindSafe for HashMap<K, V> {
}

unsafe impl<K: Key, V: Send> Send for HashMap<K, V> {
}

unsafe impl<K: Key, V: Sync> Sync for HashMap<K, V> {
}

impl<K: Key, V: Unpin> Unpin for HashMap<K, V> {
}

impl<K: Key, V: UnwindSafe> UnwindSafe for HashMap<K, V> {
}

#[repr(C)]
struct Slot<K: Key, V> {
  hash: K::Hash,
  data: MaybeUninit<V>,
}

#[inline(always)]
fn ptr_wrapping_offset_from_unsigned<T>(x: *const T, y: *const T) -> usize {
  return x.addr().wrapping_sub(y.addr()) / size_of::<T>();
}

#[inline(always)]
fn capacity(w: usize) -> usize {
  return (w >> 1) - (w >> 3) // ~ 0.375
}

#[inline(always)]
fn umulh(x: u64, y: u64) -> u64 {
  return ((x as u128 * y as u128) >> 64) as u64;
}

static EMPTY32: u32 = 0;

unsafe impl private::Key for NonZeroU32 {
  type Seed = (u32, u32);

  type Hash = u32;

  const ZERO: Self::Hash = 0;

  const EMPTY_TABLE: *const Self::Hash = &raw const EMPTY32;

  #[inline(always)]
  fn seed_nondet() -> Self::Seed {
    let n = dandelion::thread_local::u64();
    let a = n as u32;
    let b = (n >> 32) as u32;
    return (a | 1, b | 1);
  }

  #[inline(always)]
  fn seed(g: &mut impl RngCore) -> Self::Seed {
    let n = g.next_u64();
    let a = n as u32;
    let b = (n >> 32) as u32;
    return (a | 1, b | 1);
  }

  #[inline(always)]
  fn hash(k: Self, (a, b): Self::Seed) -> Self::Hash {
    let h = k.get();
    let h = h.wrapping_mul(a);
    let h = h.swap_bytes();
    let h = h.wrapping_mul(b);
    return h;
  }

  #[inline(always)]
  fn slot(h: Self::Hash, w: usize) -> usize {
    return umulh((h as u64) << 32, w as u64) as usize;
  }
}

static EMPTY64: u64 = 0;

unsafe impl private::Key for NonZeroU64 {
  type Seed = (u64, u64);

  type Hash = u64;

  const ZERO: Self::Hash = 0;

  const EMPTY_TABLE: *const Self::Hash = &raw const EMPTY64;

  #[inline(always)]
  fn seed_nondet() -> Self::Seed {
    let n = u128::from_le_bytes(dandelion::thread_local::byte_array());
    let a = n as u64;
    let b = (n >> 64) as u64;
    return (a | 1, b | 1);
  }

  #[inline(always)]
  fn seed(g: &mut impl RngCore) -> Self::Seed {
    let a = g.next_u64();
    let b = g.next_u64();
    return (a | 1, b | 1);
  }

  #[inline(always)]
  fn hash(k: Self, (a, b): Self::Seed) -> Self::Hash {
    let h = k.get();
    let h = h.wrapping_mul(a);
    let h = h.swap_bytes();
    let h = h.wrapping_mul(b);
    return h;
  }

  #[inline(always)]
  fn slot(h: Self::Hash, w: usize) -> usize {
    return umulh(h, w as u64) as usize;
  }
}

impl<K: Key, V> HashMap<K, V> {
  #[inline(always)]
  fn internal_new(m: K::Seed) -> Self {
    Self {
      seed: m,
      table: K::EMPTY_TABLE as *const Slot<K, V>,
      width: 1,
      slack: 0,
      last: ptr::null(),
    }
  }

  /// Creates an empty map, seeding the hash function from a thread-local
  /// random number generator.

  #[inline]
  pub fn new() -> Self {
    return Self::internal_new(K::seed_nondet());
  }

  /// Creates an empty map, seeding the hash function from the given random
  /// number generator.

  #[inline]
  pub fn new_seeded(g: &mut impl RngCore) -> Self {
    return Self::internal_new(K::seed(g));
  }

  /// Returns the number of items.

  #[inline]
  pub fn len(&self) -> usize {
    let w = self.width;
    let s = self.slack;

    return (capacity(w) as isize - s) as usize;
  }

  /// Returns whether the map contains zero items.

  #[inline]
  pub fn is_empty(&self) -> bool {
    return self.len() == 0;
  }

  /// Returns whether the map contains the given key.

  #[inline]
  pub fn contains_key(&self, key: K) -> bool {
    let m = self.seed;
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

  #[inline]
  pub fn get(&self, key: K) -> Option<&V> {
    let m = self.seed;
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

  /// Returns a mutable mut to the value associated with the given key, if
  /// present.

  #[inline]
  pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
    let m = self.seed;
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

  #[inline(never)]
  #[cold]
  fn internal_init(&mut self, key: K, value: V) {
    // assert!(INITIAL_N <= isize::MAX as usize / size_of::<Slot<T>>());
    /*

    const INITIAL_E: usize = 4;
    const INITIAL_W: usize = 20;

    let align = align_of::<Slot<K, V>>();
    let size = INITIAL_N * size_of::<Slot<K, V>>();
    let layout = unsafe { Layout::from_size_align_unchecked(size, align) };

    let a = unsafe { alloc::alloc::alloc_zeroed(layout) } as *mut Slot<T>;
    if a.is_null() { match alloc::alloc::handle_alloc_error(layout) {} }

    let t = unsafe { a.add(INITIAL_D - 1) };
    let b = unsafe { a.add(INITIAL_N - 1) };

    let m = self.seed;
    let h = hash(m, key).get();
    let p = unsafe { t.offset(- spot(INITIAL_S, h)) };

    unsafe { &mut *p }.hash = h;
    unsafe { &mut *p }.data = MaybeUninit::new(value);

    // We only modify `self` after we know that allocation has succeeded.

    self.table = t;
    self.shift = INITIAL_S;
    self.slack = INITIAL_R - 1;
    self.check = b;
    */
  }

  #[inline(never)]
  #[cold]
  fn internal_grow(&mut self) {
    let _: _ = self;
    self.slack = 13;
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
  pub fn insert(&mut self, key: K, value: V) -> Option<V> {
    let l = self.last as *mut Slot<K, V>;

    if l.is_null() {
      self.internal_init(key, value);

      return None;
    }

    let m = self.seed;
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

  #[inline]
  pub fn remove(&mut self, key: K) -> Option<V> {
    let m = self.seed;
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

    let value = unsafe { ptr::read(&raw mut (*a).data).assume_init() };

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

  pub fn clear(&mut self) {
    let l = self.last as *mut Slot<K, V>;

    if l.is_null() { return; }

    let t = self.table as *mut Slot<K, V>;
    let w = self.width;
    let s = self.slack;
    let c = capacity(w);
    let n = (c as isize - s) as usize;

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
          n -= 1;
          s += 1;
          self.slack = s;
          unsafe { ptr::drop_in_place(&raw mut (*a).data) };

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

      self.slack = c as isize;
    }
  }

  /// Removes every item from the map. Releases heap-allocated memory.

  pub fn reset(&mut self) {
    let l = self.last as *mut Slot<K, V>;

    if l.is_null() { return; }

    let t = self.table as *mut Slot<K, V>;
    let w = self.width;
    let s = self.slack;
    let c = capacity(w);
    let n = (c as isize - s) as usize;

    self.table = K::EMPTY_TABLE as *const Slot<K, V>;
    self.width = 1;
    self.slack = 0;
    self.last = ptr::null();

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
          n -= 1;
          unsafe { ptr::drop_in_place(&raw mut (*a).data) };

          if n == 0 { break; }
        }

        a = a.wrapping_add(1);
      }
    }

    let align = align_of::<Slot<K, V>>();
    let num_slots = ptr_wrapping_offset_from_unsigned(l, t) + w;
    let size = num_slots * size_of::<Slot<K, V>>();
    let base = t.wrapping_sub(w - 1) as *mut u8;

    unsafe { dealloc(base, Layout::from_size_align_unchecked(size, align)) };
  }

  pub(self) fn num_slots(&self) -> usize {
    let l = self.last;

    if l.is_null() { return 0; }

    let t = self.table;
    let w = self.width;

    return ptr_wrapping_offset_from_unsigned(l, t) + w;
  }

  pub(self) fn num_bytes(&self) -> usize {
    return self.num_slots() * size_of::<Slot<K, V>>();
  }

  pub(self) fn load_factor(&self) -> f64 {
    // NB: NaN if no allocation
    return self.len() as f64 / self.num_slots() as f64;
  }
}

impl<K: Key, V> Drop for HashMap<K, V> {
  fn drop(&mut self) {
    self.reset()
  }
}

impl<K: Key, V> Index<K> for HashMap<K, V> {
  type Output = V;

  #[inline]
  fn index(&self, key: K) -> &V {
    return self.get(key).unwrap();
  }
}

impl<K: Key, V> IndexMut<K> for HashMap<K, V> {
  #[inline]
  fn index_mut(&mut self, key: K) -> &mut V {
    return self.get_mut(key).unwrap();
  }
}

mod private {
  use super::*;

  pub(super) unsafe trait Key {
    type Seed: Copy;

    type Hash: Copy + Ord;

    const ZERO: Self::Hash;

    const EMPTY_TABLE: *const Self::Hash;

    fn seed_nondet() -> Self::Seed;

    fn seed(g: &mut impl RngCore) -> Self::Seed;

    fn hash(k: Self, m: Self::Seed) -> Self::Hash;

    fn slot(h: Self::Hash, w: usize) -> usize;
  }
}

pub mod internal {
  //! Unstable API exposing implementation details for benchmarks and tests.

  use super::*;

  pub fn num_slots<K: Key, V>(t: &HashMap<K, V>) -> usize {
    return t.num_slots();
  }

  pub fn num_bytes<K: Key, V>(t: &HashMap<K, V>) -> usize {
    return t.num_bytes();
  }

  pub fn load_factor<K: Key, V>(t: &HashMap<K, V>) -> f64 {
    return t.load_factor();
  }
}
