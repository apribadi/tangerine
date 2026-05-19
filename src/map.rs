//! This module provides a fast hash map keyed by types representable as
//! `NonZeroU32` or `NonZeroU64`.

use alloc::alloc::Layout;
use alloc::alloc::alloc;
use alloc::alloc::dealloc;
use alloc::alloc::handle_alloc_error;
use alloc::boxed::Box;
use core::fmt::Debug;
use core::fmt::Formatter;
use core::hint::assert_unchecked;
use core::hint::cold_path;
use core::hint::select_unpredictable;
use core::mem::MaybeUninit;
use core::mem::needs_drop;
use core::mem::offset_of;
use core::ops::Index;
use core::ptr::null;
use core::ptr::null_mut;
use rand_core::Rng;

use crate::hash::Hash;
use crate::key::Key;
use crate::word::Word;

/// A fast hash map keyed by types representable as [`NonZeroU32`](core::num::NonZeroU32)
/// or [`NonZeroU64`](core::num::NonZeroU64).
#[repr(C)]
pub struct IntMap<K: Key, V> {
  table: *const Slot<K, V>,
  shift: usize,
  slack: usize,
  limit: *const Slot<K, V>,
  seed: <K::Word as Hash>::Seed,
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
  cur: K::Word,
  key: K::Word,
}

unsafe impl<K: Key + Send, V: Send> Send for IntMap<K, V> {
}

unsafe impl<K: Key + Sync, V: Sync> Sync for IntMap<K, V> {
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
  unsafe { p.byte_add(offset_of!(Slot<K, V>, hash)).cast() }
}

#[inline(always)]
unsafe fn slot_data<K: Key, V>(p: *mut Slot<K, V>) -> *mut V {
  unsafe { p.byte_add(offset_of!(Slot<K, V>, data)).cast() }
}

#[inline(always)]
const fn allocation_max_num_slots<K: Key, V>() -> usize {
  isize::MAX as usize / size_of::<Slot<K, V>>()
}

#[inline(always)]
const fn allocation_size<K: Key, V>(num_slots: usize) -> usize {
  num_slots * size_of::<Slot<K, V>>()
}

const ALLOCATION_CHUNK: usize = 4;

#[inline(always)]
const unsafe fn allocation_layout<K: Key, V>(num_slots: usize) -> Layout {
  let s = allocation_size::<K, V>(num_slots);
  let a = align_of::<Slot<K, V>>();
  unsafe { Layout::from_size_align_unchecked(s, a) }
}

fn initial_table<K:Key, V>() -> *const Slot<K, V> {
  if is_stub_ok::<K, V>() {
    &raw const STUB as _
  } else {
    null()
  }
}

fn initial_shift<K: Key, V>() -> usize {
  K::Word::BITS - 1
}

fn initial_slack<K: Key, V>() -> usize {
  capacity::<K, V>(initial_shift::<K, V>())
}

fn initial_limit<K:Key, V>() -> *const Slot<K, V> {
  initial_table::<K, V>()
}

#[inline(always)]
const fn is_stub_ok<K: Key, V>() -> bool {
  align_of::<[Slot<K, V>; 3]>() <= align_of::<Stub>()
    && size_of::<[Slot<K, V>; 3]>() <= size_of::<Stub>()
}

#[inline(always)]
fn is_uninit_null<K:Key, V>(table: *mut Slot<K, V>, _: usize) -> bool {
  ! is_stub_ok::<K, V>() && table.is_null()
}

#[inline(always)]
fn is_uninit_stub<K:Key, V>(_: *mut Slot<K, V>, shift: usize) -> bool {
  is_stub_ok::<K, V>() && shift == initial_shift::<K, V>()
}

#[inline(always)]
fn is_uninit<K:Key, V>(table: *mut Slot<K, V>, shift: usize) -> bool {
  is_uninit_null(table, shift) || is_uninit_stub(table, shift)
}

#[inline(always)]
fn hash<K: Key>(key: K, m: <K::Word as Hash>::Seed0) -> K::Word {
  K::Word::hash(K::into_word(key), m)
}

#[inline(always)]
unsafe fn invert_hash<K: Key>(x: K::Word, m: <K::Word as Hash>::Seed1) -> K {
  unsafe { K::from_word(K::Word::invert_hash(x, m)) }
}

#[inline(always)]
fn slot<W: Word>(h: W, s: usize) -> usize {
  W::slot(h, s)
}

#[inline(always)]
fn capacity<K: Key, V>(s: usize) -> usize {
  K::Word::capacity(s)
}

#[inline(always)]
unsafe fn search<K: Key, V>(t: *mut Slot<K, V>, s: usize, h: K::Word) -> (*mut Slot<K, V>, K::Word) {
  unsafe { assert_unchecked(s <= K::Word::BITS - 1) };
  let k = slot(h, s);
  let b = unsafe { t.add(k + 1) };
  let v = unsafe { slot_hash(b).read() };
  if ! (v < h) {
    let a = unsafe { t.add(k) };
    let u = unsafe { slot_hash(a).read() };
    let p = select_unpredictable(u < h, b, a);
    let x = select_unpredictable(u < h, v, u);
    (p, x)
  } else {
    cold_path();
    let mut p = b;
    let mut x;
    loop {
      p = unsafe { p.add(1) };
      x = unsafe { slot_hash(p).read() };
      if ! (x < h) { break }
    }
    (p, x)
  }
}

#[inline(always)]
unsafe fn remove_at<K: Key, V>(t: *mut Slot<K, V>, s: usize, p: *mut Slot<K, V>) -> V {
  let value = unsafe { slot_data(p).read() };
  let mut p = p;
  let mut i = unsafe { p.offset_from_unsigned(t) };
  loop {
    p = unsafe { p.add(1) };
    i = i + 1;
    let x = unsafe { slot_hash(p).read() };
    if ! (slot(x, s) < i && /* likely */ x != K::Word::MAX) { break }
    unsafe { slot_hash(p.sub(1)).write(x) };
    unsafe { slot_data(p.sub(1)).write(slot_data(p).read()) };
    // NOTE: We could do the loop exit test here instead, with the modification
    // that we read data as MaybeUninit<V>.
  }
  unsafe { slot_hash(p.sub(1)).write(K::Word::MAX) };
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
  unsafe { p.add(1) }
}

impl<K: Key, V> IntMap<K, V> {
  #[inline(always)]
  fn from_seed(m: <K::Word as Hash>::Seed) -> Self {
    Self {
      table: initial_table::<K, V>(),
      shift: initial_shift::<K, V>(),
      slack: initial_slack::<K, V>(),
      limit: initial_limit::<K, V>(),
      seed: m,
    }
  }

  /// Creates an empty map, seeding the hash function from a thread-local
  /// random number generator.
  pub fn new() -> Self {
    Self::from_seed(K::Word::seed_nondet())
  }

  /// Creates an empty map, seeding the hash function from the given random
  /// number generator.
  pub fn with_seed(rng: &mut impl Rng) -> Self {
    Self::from_seed(K::Word::seed(rng))
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
    let m = K::Word::seed0(&self.seed);
    let h = hash(key, m);
    if is_uninit_null(t, s) { return }
    let k = slot(h, s);
    let _ = unsafe { slot_hash(t.add(k)).read_volatile() };
    let _ = unsafe { slot_hash(t.add(k + 1)).read_volatile() };
  }

  /// Returns whether the map contains the given key.
  #[inline(always)]
  pub fn contains_key(&self, key: K) -> bool {
    let t = self.table.cast_mut();
    let s = self.shift;
    let m = K::Word::seed0(&self.seed);
    let h = hash(key, m);
    if is_uninit_null(t, s) { return false }
    unsafe { search(t, s, h) }.1 == h
  }

  /// Returns a reference to the value associated with the given key, if
  /// present.
  #[inline(always)]
  pub fn get(&self, key: K) -> Option<&V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let m = K::Word::seed0(&self.seed);
    if is_uninit_null(t, s) { return None }
    let h = hash(key, m);
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
    let m = K::Word::seed0(&self.seed);
    let h = hash(key, m);
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
    let m = K::Word::seed0(&self.seed);
    let hs = keys.map(|key| hash(key, m));
    let mut is_disjoint = true;
    for i in 0 .. N {
      for j in 0 .. i {
        is_disjoint &= hs[i] != hs[j];
      }
    }
    assert!(is_disjoint);
    let mut out = [const { None }; N];
    if is_uninit_null(t, s) { return out }
    for i in 0 .. N {
      let h = hs[i];
      let p = unsafe { search(t, s, h) };
      out[i] =
        if p.1 != h {
          None
        } else {
          Some(unsafe { &mut *slot_data(p.0) })
        };
    }
    out
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
    let t = self.table.cast_mut();
    let s = self.shift;
    let m = K::Word::seed0(&self.seed);
    let h = hash(key, m);
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
          let r = self.slack;
          let z = self.limit.cast_mut();
          let p = unsafe { insert_at(p.0, p.1, h, value) };
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

  #[inline(never)]
  #[cold]
  fn insert_init(&mut self, h: K::Word, value: V) -> *mut V {
    let w = 4 * ALLOCATION_CHUNK;
    let e = ALLOCATION_CHUNK;
    let d = w + e;
    let s = K::Word::BITS - w.trailing_zeros() as usize;
    assert!(d <= allocation_max_num_slots::<K, V>());
    let l = unsafe { allocation_layout::<K, V>(d) };
    let t = unsafe { alloc(l) } as *mut Slot<K, V>;
    if t.is_null() { match handle_alloc_error(l) { } }
    for i in 0 .. d { unsafe { slot_hash(t.add(i)).write(K::Word::MAX) }; }
    let k = slot(h, s);
    let a = unsafe { t.add(k) };
    unsafe { slot_hash(a).write(h) };
    unsafe { slot_data(a).write(value) };
    self.table = t;
    self.shift = s;
    self.slack = capacity::<K, V>(s) - 1;
    self.limit = unsafe { t.add(d) };
    unsafe { slot_data(a) }
  }

  #[inline(never)]
  #[cold]
  fn insert_grow(&mut self, pos: *mut Slot<K, V>, h: K::Word) -> *mut V {
    let last_write = unsafe { pos.sub(1) };
    // Remove the last slot so that the table is in a valid state, even if we
    // panic.
    let last_write_hash = unsafe { slot_hash(last_write).replace(K::Word::MAX) };
    // Retrieve and compute values for the old table.
    let old_t = self.table.cast_mut();
    let old_s = self.shift;
    let old_r = self.slack;
    let old_z = self.limit.cast_mut();
    let old_d = unsafe { old_z.offset_from_unsigned(old_t) };
    let old_w = 1 << K::Word::BITS - old_s;
    let old_e = old_d - old_w;
    // If s == 0, then the map can hold every possible key and should never grow.
    debug_assert!(0 != old_s);
    debug_assert!(old_s <= K::Word::BITS - 1);
    // Compute new sizes.
    let new_s = old_s - 1;
    let new_w = 1 << K::Word::BITS - new_s;
    let new_e =
      if new_s == 0 {
        0 // special case, we can store every possible key
      } else if last_write == unsafe { old_z.sub(1) } {
        old_e * 2 // if we wrote in the final slot
      } else if old_e < K::Word::BITS - new_s {
        old_e + ALLOCATION_CHUNK // we maintain e >= log2(w)
      } else {
        old_e
      };
    let new_d = new_w + new_e;
    // Panic if the layout would overflow.
    assert!(new_d <= allocation_max_num_slots::<K, V>());
    // Allocate.
    let new_l = unsafe { allocation_layout::<K, V>(new_d) };
    let new_t = unsafe { alloc(new_l) } as *mut Slot<K, V>;
    if new_t.is_null() { match handle_alloc_error(new_l) { } }
    let new_z = unsafe { new_t.add(new_d) };
    // Update struct fields.
    self.table = new_t;
    self.shift = new_s;
    self.slack = old_r + (capacity::<K, V>(new_s) - capacity::<K, V>(old_s)) - 1;
    self.limit = new_z;
    // Initialize new table.
    let mut p = new_t;
    let mut i = new_d;
    unsafe { assert_unchecked(i % ALLOCATION_CHUNK == 0) };
    unsafe { assert_unchecked(i != 0) };
    loop {
      unsafe { slot_hash(p).write(K::Word::MAX) };
      p = unsafe { p.add(1) };
      i = i - 1;
      if i == 0 { break }
    }
    // Re-add the last write so that we copy it to the new table.
    unsafe { slot_hash(last_write).write(last_write_hash) };
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
      if p == old_z { break }
    }
    // The map is now in a valid state, even if deallocating panics.
    unsafe { dealloc(old_t as *mut u8, allocation_layout::<K, V>(old_d)) };
    // Find the newly-inserted value. Note, this was not necessarily at last_write.
    let k = slot(h, new_s);
    let mut p = unsafe { new_t.add(k) };
    while unsafe { slot_hash(p).read() } != h {
      p = unsafe { p.add(1) };
    }
    unsafe { slot_data(p) }
  }

  /// Removes the given key from the map. Returns the previous value associated
  /// with the given key, if one was present.
  #[inline(always)]
  pub fn remove(&mut self, key: K) -> Option<V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let m = K::Word::seed0(&self.seed);
    let h = hash(key, m);
    if is_uninit_null(t, s) { return None }
    let p = unsafe { search(t, s, h) };
    if p.1 != h {
      None
    } else {
      self.slack = self.slack + 1;
      Some(unsafe { remove_at(t, s, p.0) })
    }
  }

  /// Returns a view of the entry in the map corresponding to the given key for
  /// subsequent inspection and modification.
  #[inline(always)]
  pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let m = K::Word::seed0(&self.seed);
    let h = hash(key, m);
    if is_uninit_null(t, s) {
      Entry::Vacant(VacantEntry { map: self, pos: null_mut(), cur: K::Word::MAX, key: h })
    } else {
      let p = unsafe { search(t, s, h) };
      if p.1 == h {
        Entry::Occupied(OccupiedEntry { map: self, pos: p.0 })
      } else {
        Entry::Vacant(VacantEntry { map: self, pos: p.0, cur: p.1, key: h })
      }
    }
  }

  /// Ensures that there is a value associated with the given key by inserting
  /// the provided default value if the key was previously absent. Returns a
  /// mutable reference to the value in the entry.
  pub fn get_or_insert(&mut self, key: K, default: V) -> &mut V {
    match self.entry(key) {
      Entry::Occupied(entry) => entry.into_mut(),
      Entry::Vacant(entry) => entry.insert(default),
    }
  }

  /// Ensures that there is a value associated with the given key by inserting
  /// the result of calling the provided default function if the key was
  /// previously absent. Returns a mutable reference to the value in the entry.
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
        // We must be careful to leave the map in a valid state even if a call to
        // `drop` panics.
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
          if unsafe { slot_hash(p).read() } != K::Word::MAX {
            unsafe { slot_hash(p).write(K::Word::MAX) };
            r = r + 1;
            self.slack = r;
            unsafe { slot_data(p).drop_in_place() };
            n = n - 1;
            if n == 0 { break }
          }
        }
      }
    } else {
      if n != 0 {
        self.slack = c;
        let mut p = t;
        let mut i = unsafe { z.offset_from_unsigned(t) };
        unsafe { assert_unchecked(i % ALLOCATION_CHUNK == 0) };
        unsafe { assert_unchecked(i != 0) };
        loop {
          unsafe { slot_hash(p).write(K::Word::MAX) };
          p = unsafe { p.add(1) };
          i = i - 1;
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
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    let z = self.limit.cast_mut();
    if is_uninit(t, s) { return }
    let n = capacity::<K, V>(s) - r;
    let d = unsafe { z.offset_from_unsigned(t) };
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
          p = unsafe { p.add(1) };
          if x != K::Word::MAX {
            unsafe { slot_data(p.sub(1)).drop_in_place() };
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
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    let m = K::Word::seed1(&self.seed);
    Iter {
      len: capacity::<K, V>(s) - r,
      pos: t,
      f: move |a, x| unsafe { (invert_hash(x, m), &*slot_data(a)) }
    }
  }

  /// Returns an iterator yielding each key and a mutable reference to its
  /// associated value. The iterator item type is `(K, &mut V)`.
  #[inline(always)]
  pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = (K, &mut V)> + use<'_, K, V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    let m = K::Word::seed1(&self.seed);
    Iter {
      len: capacity::<K, V>(s) - r,
      pos: t,
      f: move |a, x| unsafe { (invert_hash(x, m), &mut *slot_data(a)) }
    }
  }

  /// Returns an iterator yielding each key. The iterator item type is `K`.
  #[inline(always)]
  pub fn keys(&self) -> impl ExactSizeIterator<Item = K> + use<'_, K, V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    let m = K::Word::seed1(&self.seed);
    Iter {
      len: capacity::<K, V>(s) - r,
      pos: t,
      f: move |_, x| unsafe { invert_hash(x, m) }
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
    let t = self.table;
    let z = self.limit;
    unsafe { z.offset_from_unsigned(t) }
  }

  fn allocation_size(&self) -> usize {
    allocation_size::<K, V>(self.num_slots())
  }

  fn load_factor(&self) -> f64 {
    self.len() as f64 / self.num_slots() as f64
  }

  fn displacement_histogram(&self) -> [usize; 10] {
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    let mut n = capacity::<K, V>(s) - r;
    let mut r = [0usize; 10];
    let mut p = t;
    let mut i = 0;
    loop {
      let x = unsafe { slot_hash(p).read() };
      let k = i;
      p = unsafe { p.add(1) };
      i = i + 1;
      if x != K::Word::MAX {
        r[usize::min(9, k - slot(x, s))] += 1;
        n = n - 1;
        if n == 0 { break }
      }
    }
    r
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
    self.map.slack = self.map.slack + 1;
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
    let x = self.cur;
    let h = self.key;
    let inserted_at =
      if is_uninit(t, s) {
        self.map.insert_init(h, value)
      } else {
        let r = self.map.slack;
        let z = self.map.limit.cast_mut();
        let a = p;
        let p = unsafe { insert_at(p, x, h, value) };
        if p == z || r == 0 {
          self.map.insert_grow(p, h)
        } else {
          self.map.slack = r - 1;
          unsafe { slot_data(a) }
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
    let mut x;
    loop {
      x = unsafe { slot_hash(p).read()};
      p = unsafe { p.add(1) };
      if x != K::Word::MAX { break }
    }
    self.len = n - 1;
    self.pos = p;
    Some((self.f)(unsafe { p.sub(1) }, x))
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
    let mut u = init;
    let mut g = g;
    if n != 0 {
      loop {
        let x = unsafe { slot_hash(p).read() };
        p = unsafe { p.add(1) };
        if x != K::Word::MAX {
          u = g(u, f(unsafe { p.sub(1) }, x));
          n = n - 1;
          if n == 0 { break }
        }
      }
    }
    u
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
  fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
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

  use super::IntMap;
  use super::Key;

  pub fn num_slots<K: Key, V>(t: &IntMap<K, V>) -> usize {
    t.num_slots()
  }

  pub fn allocation_size<K: Key, V>(t: &IntMap<K, V>) -> usize {
    t.allocation_size()
  }

  pub fn load_factor<K: Key, V>(t: &IntMap<K, V>) -> f64 {
    t.load_factor()
  }

  pub fn displacement_histogram<K: Key, V>(t: &IntMap<K, V>) -> [usize; 10] {
    t.displacement_histogram()
  }
}
