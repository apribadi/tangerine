//! This module provides a high performance hash map keyed by types
//! representable as non-zero integers.

// TODO:
//
// two empty slots at the end
//
// full map size is 2**k + 1
//
// search loop stride 2
//
// remove loop stride 2


// TODO:
//
// consider unrolling grow loop

use alloc::alloc::Layout;
use alloc::alloc::alloc;
use alloc::alloc::dealloc;
use alloc::alloc::handle_alloc_error;
use alloc::boxed::Box;
use core::fmt::Debug;
use core::fmt::Formatter;
use core::fmt;
use core::hint::assert_unchecked;
use core::hint::select_unpredictable;
use core::mem::MaybeUninit;
use core::mem::needs_drop;
use core::ops::Index;
use core::ptr::null;
use core::ptr::null_mut;
use rand_core::Rng;

use crate::hash::Hash;
use crate::key::Key;
use crate::word::Word;

/// A high performance hash map keyed by types representable as non-zero
/// integers.
#[repr(C)]
pub struct IntMap<K: Key, V> {
  table: *const Slot<K, V>,
  shift: usize,
  slack: usize,
  limit: *const Slot<K, V>,
  hash: K::Hash,
}

unsafe impl<K: Key + Send, V: Send> Send for IntMap<K, V> {
}

unsafe impl<K: Key + Sync, V: Sync> Sync for IntMap<K, V> {
}

/// A view of an entry in a map, produced by the [`IntMap::entry`] method. It
/// may either be vacant or occupied.
#[repr(usize)]
pub enum Entry<'a, K: Key, V> {
  /// An occupied entry.
  Occupied(OccupiedEntry<'a, K, V>),
  /// A vacant entry.
  Vacant(VacantEntry<'a, K, V>),
}

/// A view of an occupied entry in a map.
#[repr(C)]
pub struct OccupiedEntry<'a, K: Key, V> {
  map: &'a mut IntMap<K, V>,
  pos: *mut Slot<K, V>,
}

/// A view of a vacant entry in a map.
#[repr(C)]
pub struct VacantEntry<'a, K: Key, V> {
  map: &'a mut IntMap<K, V>,
  pos: *mut Slot<K, V>,
  occupant: K::Word,
  hash: K::Word,
}

#[repr(C, align(64))]
struct Stub([u8; 192]);

static STUB: Stub = Stub([0xff; _]);

#[repr(C)]
struct Slot<K: Key, V> {
  hash: K::Word,
  data: MaybeUninit<V>,
}

#[inline(always)]
unsafe fn slot_hash<K: Key, V>(p: *mut Slot<K, V>) -> *mut K::Word {
  unsafe { &raw mut (*p).hash }
}

#[inline(always)]
unsafe fn slot_data<K: Key, V>(p: *mut Slot<K, V>) -> *mut V {
  unsafe { &raw mut (*p).data }.cast()
}

#[inline(always)]
const fn allocation_max_num_slots<K: Key, V>() -> usize {
  isize::MAX as usize / size_of::<Slot<K, V>>()
}

#[inline(always)]
const fn allocation_size<K: Key, V>(num_slots: usize) -> usize {
  num_slots * size_of::<Slot<K, V>>()
}

const CHUNK: usize = 4;

#[inline(always)]
const unsafe fn allocation_layout<K: Key, V>(num_slots: usize) -> Layout {
  debug_assert!(num_slots % CHUNK == 0);
  let s = allocation_size::<K, V>(num_slots);
  let a = align_of::<Slot<K, V>>();
  unsafe { Layout::from_size_align_unchecked(s, a) }
}

#[inline(always)]
const fn initial_table<K:Key, V>() -> *const Slot<K, V> {
  if const { is_stub_ok::<K, V>() } {
    &raw const STUB as _
  } else {
    null()
  }
}

#[inline(always)]
const fn initial_shift<K: Key, V>() -> usize {
  K::Word::BITS - 1
}

#[inline(always)]
const fn initial_slack<K: Key, V>() -> usize {
  1
}

#[inline(always)]
const fn initial_limit<K:Key, V>() -> *const Slot<K, V> {
  initial_table::<K, V>()
}

#[inline(always)]
const fn is_stub_ok<K: Key, V>() -> bool {
  align_of::<[Slot<K, V>; 3]>() <= align_of::<Stub>()
    && size_of::<[Slot<K, V>; 3]>() <= size_of::<Stub>()
}

#[inline(always)]
const fn is_uninit_null<K:Key, V>(table: *mut Slot<K, V>, _: usize) -> bool {
  ! is_stub_ok::<K, V>() && table.is_null()
}

#[inline(always)]
const fn is_uninit_stub<K:Key, V>(_: *mut Slot<K, V>, shift: usize) -> bool {
  is_stub_ok::<K, V>() && shift == initial_shift::<K, V>()
}

#[inline(always)]
const fn is_uninit<K:Key, V>(table: *mut Slot<K, V>, shift: usize) -> bool {
  is_uninit_null(table, shift) || is_uninit_stub(table, shift)
}

#[inline(always)]
fn hash<K: Key, H: Hash<K::Word>>(key: K, m: &H) -> K::Word {
  m.hash(K::into_word(key))
}

#[inline(always)]
unsafe fn invert_hash<K: Key, H: Hash<K::Word>>(x: K::Word, m: &H) -> K {
  unsafe { K::from_word(m.invert_hash(x)) }
}

#[inline(always)]
fn capacity<K: Key, V>(shift: usize) -> usize {
  K::Word::capacity(shift)
}

#[inline(always)]
fn slot<W: Word>(hash: W, shift: usize) -> usize {
  W::slot(hash, shift)
}

#[inline(always)]
fn num_slots<K: Key, V>(t: *mut Slot<K, V>, z: *mut Slot<K, V>) -> usize {
  let n = unsafe { z.offset_from_unsigned(t) };
  let n = n + (CHUNK - 1) & ! (CHUNK - 1);
  n
}

#[inline(always)]
unsafe fn search<K: Key, V>(t: *mut Slot<K, V>, s: usize, h: K::Word) -> (*mut Slot<K, V>, K::Word) {
  unsafe { assert_unchecked(s <= K::Word::BITS - 1) };
  let k = slot(h, s);
  let mut a = unsafe { t.add(k) };
  let mut b = unsafe { a.add(1) };
  let mut v = unsafe { slot_hash(b).read() };
  while ! (v >= h) {
    a = unsafe { a.add(2) };
    b = unsafe { b.add(2) };
    v = unsafe { slot_hash(b).read() };
  }
  let u = unsafe { slot_hash(a).read() };
  let p = select_unpredictable(u >= h, a, b);
  let x = select_unpredictable(u >= h, u, v);
  (p, x)
}

/*
#[inline(always)]
unsafe fn search<K: Key, V>(t: *mut Slot<K, V>, s: usize, h: K::Word) -> (*mut Slot<K, V>, K::Word) {
  unsafe { assert_unchecked(s <= K::Word::BITS - 1) };
  let k = slot(h, s);
  let a = unsafe { t.add(k) };
  let b = unsafe { a.add(1) };
  let v = unsafe { slot_hash(b).read() };
  if v >= h {
    let u = unsafe { slot_hash(a).read() };
    let p = select_unpredictable(u >= h, a, b);
    let x = select_unpredictable(u >= h, u, v);
    (p, x)
  } else {
    let mut a = a;
    let mut b;
    let mut v;
    loop {
      a = unsafe { a.add(2) };
      b = unsafe { a.add(1) };
      v = unsafe { slot_hash(b).read() };
      if v >= h { break }
    }
    let u = unsafe { slot_hash(a).read() };
    let p = select_unpredictable(u >= h, a, b);
    let x = select_unpredictable(u >= h, u, v);
    (p, x)
  }
}
*/

/*
#[inline(always)]
unsafe fn search<K: Key, V>(t: *mut Slot<K, V>, s: usize, h: K::Word) -> (*mut Slot<K, V>, K::Word) {
  unsafe { assert_unchecked(s <= K::Word::BITS - 1) };
  let k = slot(h, s);
  let b = unsafe { t.add(k + 1) };
  let v = unsafe { slot_hash(b).read() };
  if v >= h {
    let a = unsafe { t.add(k) };
    let u = unsafe { slot_hash(a).read() };
    let p = select_unpredictable(u >= h, a, b);
    let x = select_unpredictable(u >= h, u, v);
    (p, x)
  } else {
    let mut p = b;
    let mut x;
    loop {
      p = unsafe { p.add(1) };
      x = unsafe { slot_hash(p).read() };
      if x >= h { break }
    }
    (p, x)
  }
}
*/

#[inline(always)]
unsafe fn remove_at<K: Key, V>(t: *mut Slot<K, V>, s: usize, p: *mut Slot<K, V>) -> V {
  let value = unsafe { slot_data(p).read() };
  let mut i = unsafe { p.offset_from_unsigned(t) } + 1;
  let mut a;
  let mut b = p;
  let mut c = unsafe { p.add(1) };
  let mut d = unsafe { p.add(2) };
  let mut x = unsafe { slot_hash(c).read() };
  let mut y = unsafe { slot_hash(d).read() };
  unsafe { slot_hash(b).write(x) };
  unsafe { slot_data(b).copy_from_nonoverlapping(slot_data(c), 1) };
  let mut u = slot(x, s);
  let mut v = slot(y, s);
  let mut p = select_unpredictable(u < i, c, b);
  while u < i && v <= i && y != K::Word::MAX {
    i = i + 2;
    a = c;
    b = d;
    c = unsafe { c.add(2) };
    d = unsafe { d.add(2) };
    unsafe { slot_hash(a).write(y) };
    unsafe { slot_data(a).copy_from_nonoverlapping(slot_data(b), 1) };
    x = unsafe { slot_hash(c).read() };
    y = unsafe { slot_hash(d).read() };
    unsafe { slot_hash(b).write(x) };
    unsafe { slot_data(b).copy_from_nonoverlapping(slot_data(c), 1) };
    u = slot(x, s);
    v = slot(y, s);
    p = select_unpredictable(u < i, c, b);
  }
  unsafe { slot_hash(p).write(K::Word::MAX) };
  value
}

#[inline(always)]
unsafe fn remove_at0<K: Key, V>(t: *mut Slot<K, V>, s: usize, p: *mut Slot<K, V>) -> V {
  let value = unsafe { slot_data(p).read() };
  let mut p = p;
  let mut q;
  let mut i = unsafe { p.offset_from_unsigned(t) };
  loop {
    q = p;
    p = unsafe { p.add(1) };
    i = i + 1;
    let x = unsafe { slot_hash(p).read() };
    if ! (slot(x, s) < i && /* likely */ x != K::Word::MAX) { break }
    unsafe { slot_hash(q).write(x) };
    unsafe { slot_data(q).write(slot_data(p).read()) };
    // NOTE: We could do the loop exit test here instead, with the modification
    // that we read data as MaybeUninit<V>.
  }
  unsafe { slot_hash(q).write(K::Word::MAX) };
  value
}

#[inline(always)]
unsafe fn insert_at<K: Key, V>(p: *mut Slot<K, V>, x: K::Word, h: K::Word, value: V) -> *mut Slot<K, V> {
  unsafe { slot_hash(p).write(h) };
  let mut p = p;
  let mut x = x;
  let mut y = value;
  while x != K::Word::MAX {
    y = unsafe { slot_data(p).replace(y) };
    p = unsafe { p.add(1) };
    x = unsafe { slot_hash(p).replace(x) };
  }
  unsafe { slot_data(p).write(y) };
  p
}

#[inline(always)]
unsafe fn insert_at0<K: Key, V>(p: *mut Slot<K, V>, x: K::Word, h: K::Word, value: V) -> *mut Slot<K, V> {
  unsafe { slot_hash(p).write(h) };
  let mut p = p;
  let mut x = x;
  let mut y = value;
  while x != K::Word::MAX {
    y = unsafe { slot_data(p).replace(y) };
    p = unsafe { p.add(1) };
    x = unsafe { slot_hash(p).replace(x) };
  }
  unsafe { slot_data(p).write(y) };
  p
}

#[inline(always)]
unsafe fn init_span<K: Key, V>(p: *mut Slot<K, V>, z: *mut Slot<K, V>) {
  // Initializes `k * CHUNK` slots for `k >= 1`.
  let mut p = p;
  loop {
    for i in 0 .. CHUNK {
      unsafe { slot_hash(p.add(i)).write(K::Word::MAX) };
    }
    p = p.wrapping_add(CHUNK); // inhibit loop "optimizations"
    if p >= z { break } // sometimes `z` is placed a bit before the end of the span
  }
}


impl<K: Key, V> IntMap<K, V> {
  /// Creates an empty map, seeding the hash function from a thread-local
  /// random number generator.
  pub fn new() -> Self {
    dandelion::thread_local::with(|g| Self::with_seed(g))
  }

  /// Creates an empty map, seeding the hash function from the given random
  /// number generator.
  pub fn with_seed(g: &mut impl Rng) -> Self {
    Self {
      table: initial_table::<K, V>(),
      shift: initial_shift::<K, V>(),
      slack: initial_slack::<K, V>(),
      limit: initial_limit::<K, V>(),
      hash: K::Hash::seed(g),
    }
  }

  /// Returns the number of items.
  #[inline(always)]
  pub fn len(&self) -> usize {
    let s = self.shift;
    let r = self.slack;
    capacity::<K, V>(s) - r
  }

  /// Returns whether the map contains zero items.
  #[inline(always)]
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Prefetchs a key.
  #[inline(always)]
  pub fn prefetch(&self, key: K) {
    let t = self.table.cast_mut();
    let s = self.shift;
    let h = hash(key, &self.hash);
    if is_uninit_null(t, s) { return }
    let k = slot(h, s);
    let a = unsafe { t.add(k) };
    let b = unsafe { a.add(1) };
    let _: K::Word = unsafe { slot_hash(a).read_volatile() };
    let _: K::Word = unsafe { slot_hash(b).read_volatile() };
  }

  /// Returns whether the map contains the given key.
  #[inline(always)]
  pub fn contains_key(&self, key: K) -> bool {
    let t = self.table.cast_mut();
    let s = self.shift;
    let h = hash(key, &self.hash);
    if is_uninit_null(t, s) { return false }
    unsafe { search(t, s, h) }.1 == h
  }

  /// Returns a reference to the value associated with the given key, if
  /// present.
  #[inline(always)]
  pub fn get(&self, key: K) -> Option<&V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    if is_uninit_null(t, s) { return None }
    let h = hash(key, &self.hash);
    let p = unsafe { search(t, s, h) };
    if p.1 != h {
      None
    } else {
      Some(unsafe { &*slot_data(p.0) })
    }
  }

  /// Returns a mutable reference to the value associated with the given key,
  /// if present.
  #[inline(always)]
  pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let h = hash(key, &self.hash);
    if is_uninit_null(t, s) { return None }
    let p = unsafe { search(t, s, h) };
    if p.1 != h {
      None
    } else {
      Some(unsafe { &mut *slot_data(p.0) })
    }
  }

  /// For each key in the given array, returns a mutable reference to the
  /// associated value, if present.
  ///
  /// # Panics
  ///
  /// Panics if any key is the same as any other key.
  pub fn get_disjoint_mut<const N: usize>(&mut self, keys: [K; N]) -> [Option<&mut V>; N] {
    let t = self.table.cast_mut();
    let s = self.shift;
    let hs = keys.map(|key| hash(key, &self.hash));
    let mut is_disjoint = true;
    for i in 0 .. N {
      for j in 0 .. i {
        is_disjoint &= hs[i] != hs[j];
      }
    }
    assert!(is_disjoint);
    if is_uninit_null(t, s) { return [const { None }; _] }
    hs.map(|h| {
      let p = unsafe { search(t, s, h) };
      if p.1 != h {
        None
      } else {
        Some(unsafe { &mut *slot_data(p.0) })
      }
    })
  }

  #[inline(never)]
  #[cold]
  fn insert_init(&mut self, h: K::Word, value: V) -> *mut V {
    let new_d = 4 * CHUNK;
    let new_e = CHUNK;
    let new_w = new_d + new_e;
    let new_s = K::Word::BITS - new_d.trailing_zeros() as usize;
    let new_r = capacity::<K, V>(new_s) - 1;
    assert!(new_w <= allocation_max_num_slots::<K, V>());
    let new_l = unsafe { allocation_layout::<K, V>(new_w) };
    let new_t = unsafe { alloc(new_l) } as *mut Slot<K, V>;
    if new_t.is_null() { match handle_alloc_error(new_l) { } }
    let new_z = unsafe { new_t.add(new_w - 2) };
    unsafe { init_span(new_t, new_z) };
    let k = slot(h, new_s);
    let a = unsafe { new_t.add(k) };
    unsafe { slot_hash(a).write(h) };
    unsafe { slot_data(a).write(value) };
    self.table = new_t;
    self.shift = new_s;
    self.slack = new_r;
    self.limit = new_z;
    unsafe { slot_data(a) }
  }

  #[inline(never)]
  #[cold]
  fn insert_grow(&mut self, p: *mut Slot<K, V>, h: K::Word) -> *mut V {
    // Stash the item in the last written-to slot so that the table is in a
    // valid state, even if we panic.
    let stashed_slot = p;
    let stashed_hash = unsafe { slot_hash(stashed_slot).replace(K::Word::MAX) };
    // Retrieve values for the old table.
    let old_t = self.table.cast_mut();
    let old_s = self.shift;
    let old_r = self.slack;
    let old_z = self.limit.cast_mut();
    debug_assert!(1 <= old_s && old_s <= K::Word::BITS - 1);
    // Compute old sizes.
    let old_w = num_slots(old_t, old_z);
    let old_d = 1 << K::Word::BITS - old_s;
    let old_e = old_w - old_d;
    // Compute new sizes.
    let new_s = old_s - 1;
    let new_r = old_r + (capacity::<K, V>(new_s) - capacity::<K, V>(old_s)) - 1;
    let new_d = 1 << K::Word::BITS - new_s;
    let new_e =
      if new_s == 0 {
        CHUNK // special case for a full size table
      } else if p == old_z {
        old_e * 2 // if we wrote in the final slot
      } else if old_e < K::Word::BITS - new_s {
        old_e + CHUNK // we maintain e >= log2(w)
      } else {
        old_e
      };
    let new_w = new_d + new_e;
    // Panic if the layout would overflow.
    assert!(new_w <= allocation_max_num_slots::<K, V>());
    // Allocate.
    let new_l = unsafe { allocation_layout::<K, V>(new_w) };
    let new_t = unsafe { alloc(new_l) } as *mut Slot<K, V>;
    if new_t.is_null() { match handle_alloc_error(new_l) { } }
    let new_z = unsafe { new_t.add(new_w - 2) };
    // Update struct fields.
    self.table = new_t;
    self.shift = new_s;
    self.slack = new_r;
    self.limit = new_z;
    // Initialize new table.
    unsafe { init_span(new_t, new_z) };
    // Re-add the last write so that we copy it to the new table.
    unsafe { slot_hash(stashed_slot).write(stashed_hash) };
    // Copy slots.
    let mut p = old_t;
    let mut i = 0;
    loop {
      let x = unsafe { slot_hash(p).read() };
      let y = unsafe { slot_data(p).cast::<MaybeUninit<V>>().read() };
      let k = slot(x, new_s);
      let k = select_unpredictable(i > k, i, k);
      let a = unsafe { new_t.add(k) };
      unsafe { slot_hash(a).write(x) };
      unsafe { slot_data(a).cast::<MaybeUninit<V>>().write(y) };
      p = unsafe { p.add(1) };
      i = select_unpredictable(x != K::Word::MAX, k + 1, i);
      if p > old_z { break }
    }
    // The map is now in a valid state, even if deallocating panics.
    unsafe { dealloc(old_t as *mut u8, allocation_layout::<K, V>(old_w)) };
    // Find the newly-inserted value. Note, this was not necessarily at
    // stashed_slot.
    let k = slot(h, new_s);
    let mut p = unsafe { new_t.add(k) };
    while unsafe { slot_hash(p).read() } != h {
      p = unsafe { p.add(1) };
    }
    unsafe { slot_data(p) }
  }

  /// Inserts the given key and value into the map. Returns the previous value
  /// associated with given key, if one was present.
  ///
  /// # Panics
  ///
  /// Panics if the table would be too large or allocation fails. If that
  /// happens, it is possible for the map to leak an arbitrary set of items,
  /// but the map will remain in a valid state.
  #[inline(always)]
  pub fn insert(&mut self, key: K, value: V) -> Option<V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let h = hash(key, &self.hash);
    if is_uninit_null(t, s) {
      let _: *mut V = self.insert_init(h, value);
      None
    } else {
      let p = unsafe { search(t, s, h) };
      if p.1 == h {
        Some(unsafe { slot_data(p.0).replace(value) })
      } else {
        if is_uninit_stub(t, s) {
          let _: *mut V = self.insert_init(h, value);
        } else {
          let p = unsafe { insert_at(p.0, p.1, h, value) };
          let r = self.slack;
          let z = self.limit.cast_mut();
          if p == z || r == 0 {
            let _: *mut V = self.insert_grow(p, h);
          } else {
            self.slack = r - 1;
          }
        }
        None
      }
    }
  }

  /// Inserts the given key and value into the map. Returns the previous value
  /// associated with given key, if one was present.
  ///
  /// # Panics
  ///
  /// Panics if the table would be too large or allocation fails. If that
  /// happens, it is possible for the map to leak an arbitrary set of items,
  /// but the map will remain in a valid state.
  #[inline(always)]
  pub fn insert0(&mut self, key: K, value: V) -> Option<V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let h = hash(key, &self.hash);
    if is_uninit_null(t, s) {
      let _: *mut V = self.insert_init(h, value);
      None
    } else {
      let p = unsafe { search(t, s, h) };
      if p.1 == h {
        Some(unsafe { slot_data(p.0).replace(value) })
      } else {
        if is_uninit_stub(t, s) {
          let _: *mut V = self.insert_init(h, value);
        } else {
          let p = unsafe { insert_at0(p.0, p.1, h, value) };
          let r = self.slack;
          let z = self.limit.cast_mut();
          if p == z || r == 0 {
            let _: *mut V = self.insert_grow(p, h);
          } else {
            self.slack = r - 1;
          }
        }
        None
      }
    }
  }

  /// Removes the given key from the map. Returns the previous value associated
  /// with the given key, if one was present.
  #[inline(always)]
  pub fn remove(&mut self, key: K) -> Option<V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let h = hash(key, &self.hash);
    if is_uninit_null(t, s) { return None }
    let p = unsafe { search(t, s, h) };
    if p.1 != h {
      None
    } else {
      self.slack += 1;
      Some(unsafe { remove_at(t, s, p.0) })
    }
  }

  /// Removes the given key from the map. Returns the previous value associated
  /// with the given key, if one was present.
  #[inline(always)]
  pub fn remove0(&mut self, key: K) -> Option<V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let h = hash(key, &self.hash);
    if is_uninit_null(t, s) { return None }
    let p = unsafe { search(t, s, h) };
    if p.1 != h {
      None
    } else {
      self.slack += 1;
      Some(unsafe { remove_at0(t, s, p.0) })
    }
  }

  /// Returns a view of the entry in the map corresponding to the given key for
  /// subsequent inspection and modification.
  #[inline(always)]
  pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let h = hash(key, &self.hash);
    if is_uninit_null(t, s) {
      Entry::Vacant(VacantEntry { map: self, pos: null_mut(), occupant: K::Word::MAX, hash: h })
    } else {
      let p = unsafe { search(t, s, h) };
      if p.1 == h {
        Entry::Occupied(OccupiedEntry { map: self, pos: p.0 })
      } else {
        Entry::Vacant(VacantEntry { map: self, pos: p.0, occupant: p.1, hash: h })
      }
    }
  }

  /// Ensures that there is a value associated with the given key by inserting
  /// the provided default value if the key was previously absent. Returns a
  /// mutable reference to the value in the entry.
  #[inline(always)]
  pub fn get_or_insert(&mut self, key: K, default: V) -> &mut V {
    match self.entry(key) {
      Entry::Occupied(entry) => entry.into_mut(),
      Entry::Vacant(entry) => entry.insert(default),
    }
  }

  /// Ensures that there is a value associated with the given key by inserting
  /// the result of calling the provided default function if the key was
  /// previously absent. Returns a mutable reference to the value in the entry.
  #[inline(always)]
  pub fn get_or_insert_with(&mut self, key: K, default: impl FnOnce() -> V) -> &mut V {
    match self.entry(key) {
      Entry::Occupied(entry) => entry.into_mut(),
      Entry::Vacant(entry) => entry.insert(default()),
    }
  }

  /// Ensures that there is a value associated with the given key by inserting
  /// the result of calling [`V::default`](Default::default) if the key was
  /// previously absent.  Returns a mutable reference to the value in the
  /// entry.
  #[inline(always)]
  pub fn get_or_default(&mut self, key: K) -> &mut V where V: Default {
    match self.entry(key) {
      Entry::Occupied(entry) => entry.into_mut(),
      Entry::Vacant(entry) => entry.insert(V::default()),
    }
  }

  /// Removes every item from the map. Retains heap-allocated memory.
  ///
  /// # Panics
  ///
  /// Panics if [`drop`]ping a value panics. If that happens, the map will be in
  /// a valid but otherwise unspecified state.
  pub fn clear(&mut self) {
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    let z = self.limit.cast_mut();
    let c = capacity::<K, V>(s);
    let n = c - r;
    if needs_drop::<V>() {
      if n != 0 {
        // WARNING!
        //
        // We must be careful to leave the map in a valid state even if a call
        // to `drop` panics.
        //
        // Here, we traverse the table in reverse order to ensure that we don't
        // remove an item that is currently displacing another item.
        //
        // Also, we update `self.slack` as we go instead of once at the end.
        let mut n = n;
        let mut r = r;
        let mut p = z;
        loop {
          p = unsafe { p.sub(1) };
          if unsafe { slot_hash(p).read() } == K::Word::MAX { continue }
          unsafe { slot_hash(p).write(K::Word::MAX) };
          r = r + 1;
          self.slack = r;
          unsafe { slot_data(p).drop_in_place() };
          n = n - 1;
          if n == 0 { break }
        }
      }
    } else {
      if n != 0 {
        self.slack = c;
        unsafe { init_span(t, z) };
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
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    let z = self.limit.cast_mut();
    if is_uninit(t, s) { return }
    let n = capacity::<K, V>(s) - r;
    let w = num_slots(t, z);
    self.table = initial_table::<K, V>();
    self.shift = initial_shift::<K, V>();
    self.slack = initial_slack::<K, V>();
    self.limit = initial_limit::<K, V>();
    if needs_drop::<V>() {
      if n != 0 {
        let mut n = n;
        let mut p = t;
        loop {
          let x = unsafe { slot_hash(p).read() };
          let q = p;
          p = unsafe { p.add(1) };
          if x == K::Word::MAX { continue }
          unsafe { slot_data(q).drop_in_place() };
          n = n - 1;
          if n == 0 { break }
        }
      }
    }
    unsafe { dealloc(t as *mut u8, allocation_layout::<K, V>(w)) };
  }

  /// Returns an iterator yielding each key and a reference to its associated
  /// value. The iterator item type is `(K, &V)`.
  #[inline(always)]
  pub fn iter(&self) -> impl ExactSizeIterator<Item = (K, &V)> + use<'_, K, V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    let m = self.hash;
    Iter {
      len: capacity::<K, V>(s) - r,
      pos: t,
      f: move |a, x| unsafe { (invert_hash(x, &m), &*slot_data(a)) }
    }
  }

  /// Returns an iterator yielding each key and a mutable reference to its
  /// associated value. The iterator item type is `(K, &mut V)`.
  #[inline(always)]
  pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = (K, &mut V)> + use<'_, K, V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    let m = self.hash;
    Iter {
      len: capacity::<K, V>(s) - r,
      pos: t,
      f: move |a, x| unsafe { (invert_hash(x, &m), &mut *slot_data(a)) }
    }
  }

  /// Returns an iterator yielding each key. The iterator item type is `K`.
  #[inline(always)]
  pub fn keys(&self) -> impl ExactSizeIterator<Item = K> + use<'_, K, V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    let m = self.hash;
    Iter {
      len: capacity::<K, V>(s) - r,
      pos: t,
      f: move |_, x| unsafe { invert_hash(x, &m) }
    }
  }

  /// Returns an iterator yielding a reference to each value. The iterator item
  /// type is `&V`.
  #[inline(always)]
  pub fn values(&self) -> impl ExactSizeIterator<Item = &V> + use<'_, K, V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    Iter {
      len: capacity::<K, V>(s) - r,
      pos: t,
      f: move |a, _| unsafe { &*slot_data(a) }
    }
  }

  /// Returns an iterator yielding a mutable reference to each value. The
  /// iterator item type is `&mut V`.
  #[inline(always)]
  pub fn values_mut(&mut self) -> impl ExactSizeIterator<Item = &mut V> + use<'_, K, V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    Iter {
      len: capacity::<K, V>(s) - r,
      pos: t,
      f: move |a, _| unsafe { &mut *slot_data(a) }
    }
  }

  fn num_slots(&self) -> usize {
    let t = self.table.cast_mut();
    let z = self.limit.cast_mut();
    num_slots(t, z)
  }

  fn allocation_size(&self) -> usize {
    allocation_size::<K, V>(self.num_slots())
  }

  fn load_factor(&self) -> f64 {
    self.len() as f64 / self.num_slots() as f64
  }

  fn probe_count_histogram(&self) -> [usize; 20] {
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    let mut n = capacity::<K, V>(s) - r;
    let mut a = [0usize; 20];
    let mut p = t;
    let mut i = 0;
    loop {
      let x = unsafe { slot_hash(p).read() };
      p = unsafe { p.add(1) };
      i = i + 1;
      if x == K::Word::MAX { continue }
      a[usize::min(19, i - 1 - slot(x, s))] += 1;
      n = n - 1;
      if n == 0 { break }
    }
    a
  }

  fn shift_count_histogram(&self) -> [usize; 20] {
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    let mut n = capacity::<K, V>(s) - r;
    let mut a = [0usize; 20];
    let mut p = t;
    let mut i = 0;
    loop {
      let x = unsafe { slot_hash(p).read() };
      p = unsafe { p.add(1) };
      i = i + 1;
      if x == K::Word::MAX { continue }
      let mut k = 0;
      let mut y = unsafe { slot_hash(p.add(k)).read() };
      while slot(y, s) < i + k && y != K::Word::MAX {
        k = k + 1;
        y = unsafe { slot_hash(p.add(k)).read() };
      }
      a[usize::min(19, k)] += 1;
      n = n - 1;
      if n == 0 { break }
    }
    a
  }
}

impl<K: Key, V> Drop for IntMap<K, V> {
  fn drop(&mut self) {
    self.reset()
  }
}

impl<K: Key, V> Index<K> for IntMap<K, V> {
  type Output = V;

  #[inline(always)]
  fn index(&self, key: K) -> &Self::Output {
    self.get(key).unwrap()
  }
}

impl<'a, K: Key, V> OccupiedEntry<'a, K, V> {
  /// Gets a reference to the value in the entry.
  #[inline(always)]
  pub fn get(&self) -> &V {
    unsafe { &*slot_data(self.pos) }
  }

  /// Gets a mutable reference to the value in the entry.
  #[inline(always)]
  pub fn get_mut(&mut self) -> &mut V {
    unsafe { &mut *slot_data(self.pos) }
  }

  /// Converts itself into a mutable reference to the value in the entry, with
  /// a lifetime from the original borrow for the call to [`IntMap::entry`].
  #[inline(always)]
  pub fn into_mut(self) -> &'a mut V {
    unsafe { &mut *slot_data(self.pos) }
  }

  /// Inserts the given value into the entry, and returns the previous value.
  #[inline(always)]
  pub fn insert(&mut self, value: V) -> V {
    unsafe { slot_data(self.pos).replace(value) }
  }

  /// Removes the value occupying the entry, and returns that value.
  #[inline(always)]
  pub fn remove(self) -> V {
    let t = self.map.table.cast_mut();
    let s = self.map.shift;
    let p = self.pos;
    self.map.slack += 1;
    unsafe { remove_at(t, s, p) }
  }
}

impl<'a, K: Key, V> VacantEntry<'a, K, V> {
  /// Inserts the given value into the entry, and returns a mutable reference
  /// to it.
  #[inline(always)]
  pub fn insert(self, value: V) -> &'a mut V {
    let t = self.map.table.cast_mut();
    let s = self.map.shift;
    let p = self.pos;
    let x = self.occupant;
    let h = self.hash;
    let inserted_at =
      if is_uninit(t, s) {
        self.map.insert_init(h, value)
      } else {
        let q = p;
        let p = unsafe { insert_at(p, x, h, value) };
        let r = self.map.slack;
        let z = self.map.limit.cast_mut();
        if p == z || r == 0 {
          self.map.insert_grow(p, h)
        } else {
          self.map.slack = r - 1;
          unsafe { slot_data(q) }
        }
      };
    unsafe { &mut *inserted_at }
  }
}

struct Iter<K: Key, V, T, F: FnMut(*mut Slot<K, V>, K::Word) -> T> {
  len: usize,
  pos: *mut Slot<K, V>,
  f: F,
}

impl<K: Key, V, T, F: FnMut(*mut Slot<K, V>, K::Word) -> T> Iterator for Iter<K, V, T, F> {
  type Item = T;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let n = self.len;
    if n == 0 { return None }
    let mut p = self.pos;
    let mut q;
    let mut x;
    loop {
      x = unsafe { slot_hash(p).read()};
      q = p;
      p = unsafe { p.add(1) };
      if x != K::Word::MAX { break }
    }
    self.len = n - 1;
    self.pos = p;
    Some((self.f)(q, x))
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }

  #[inline(always)]
  fn fold<A, G: FnMut(A, T) -> A>(self, init: A, g: G) -> A {
    let mut n = self.len;
    let mut p = self.pos;
    let mut f = self.f;
    let mut a = init;
    let mut g = g;
    if n != 0 {
      loop {
        let x = unsafe { slot_hash(p).read() };
        let q = p;
        p = unsafe { p.add(1) };
        if x == K::Word::MAX { continue }
        a = g(a, f(q, x));
        n = n - 1;
        if n == 0 { break }
      }
    }
    a
  }
}

impl<K: Key, V, T, F: FnMut(*mut Slot<K, V>, K::Word) -> T> ExactSizeIterator for Iter<K, V, T, F> {
  #[inline(always)]
  fn len(&self) -> usize {
    self.len
  }
}

impl<K: Key, V: Clone> Clone for IntMap<K, V> {
  fn clone(&self) -> Self {
    let mut t = Self::new();
    self.iter().for_each(|(x, y)| { let _: Option<V> = t.insert(x, y.clone()); });
    t
  }
}

impl <K: Key + Debug + Ord, V: Debug> Debug for IntMap<K, V> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    let mut a = self.iter().collect::<Box<[(K, &V)]>>();
    a.sort_by(|&(ref x, _), &(ref y, _)| x.cmp(y));
    f.debug_map().entries(a).finish()
  }
}

impl<K: Key, V> Default for IntMap<K, V> {
  fn default() -> Self {
    Self::new()
  }
}

impl<K: Key, V> Extend<(K, V)> for IntMap<K, V> {
  fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
    iter.into_iter().for_each(|(x, y)| { let _: Option<V> = self.insert(x, y); });
  }
}

impl<const N: usize, K: Key, V> From<[(K, V); N]> for IntMap<K, V> {
  fn from(value: [(K, V); N]) -> Self {
    Self::from_iter(value)
  }
}

impl<K: Key, V> FromIterator<(K, V)> for IntMap<K, V> {
  fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
    let mut t = Self::new();
    t.extend(iter);
    t
  }
}

pub mod internal {
  //! Unstable API exposing implementation details for benchmarks and tests.

  #![allow(missing_docs)]

  use crate::map::IntMap;
  use crate::key::Key;

  pub fn num_slots<K: Key, V>(t: &IntMap<K, V>) -> usize {
    t.num_slots()
  }

  pub fn allocation_size<K: Key, V>(t: &IntMap<K, V>) -> usize {
    t.allocation_size()
  }

  pub fn load_factor<K: Key, V>(t: &IntMap<K, V>) -> f64 {
    t.load_factor()
  }

  pub fn probe_count_histogram<K: Key, V>(t: &IntMap<K, V>) -> [usize; 20] {
    t.probe_count_histogram()
  }

  pub fn shift_count_histogram<K: Key, V>(t: &IntMap<K, V>) -> [usize; 20] {
    t.shift_count_histogram()
  }
}
