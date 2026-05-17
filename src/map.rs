//! This module provides a fast hash map keyed by types representable as
//! `NonZeroU32` or `NonZeroU64`.

extern crate alloc;

use alloc::alloc::Layout;
use alloc::alloc::alloc;
use alloc::alloc::dealloc;
use alloc::alloc::handle_alloc_error;
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
use int_cast::IntCast;
use rand_core::Rng;

use crate::key::Key;
use crate::internal_trait::Hash;
use crate::internal_trait::Word;
use crate::util::ptr_diff;

/// A fast hash map keyed by types representable as [`NonZeroU32`](core::num::NonZeroU32)
/// or [`NonZeroU64`](core::num::NonZeroU64).
#[repr(C)]
pub struct IntMap<K: Key, V> {
  table: *const Slot<K, V>,
  shift: usize,
  slack: usize,
  limit: *const Slot<K, V>,
  seed0: <K::Word as Hash>::Seed0,
  seed1: <K::Word as Hash>::Seed1,
}

/// A view of an entry in a map, produced by the [`IntMap::entry`] method. It
/// may either be vacant or occupied.
pub enum Entry<'a, K: Key, V> {
  /// An occupied entry.
  Occupied(OccupiedEntry<'a, K, V>),
  /// A vacant entry.
  Vacant(VacantEntry<'a, K, V>),
}

/// A view of an occupied entry in a map.
pub struct OccupiedEntry<'a, K: Key, V> {
  map: &'a mut IntMap<K, V>,
  pos: *mut Slot<K, V>,
}

/// A view of a vacant entry in a map.
pub struct VacantEntry<'a, K: Key, V> {
  map: &'a mut IntMap<K, V>,
  pos: *mut Slot<K, V>,
  other: K::Word,
  entry: K::Word,
}

unsafe impl<K: Key + Send, V: Send> Send for IntMap<K, V> {
}

unsafe impl<K: Key + Sync, V: Sync> Sync for IntMap<K, V> {
}

#[repr(align(64))]
struct FakeTable(#[allow(dead_code)] [u8; 192]);

static FAKE_TABLE: FakeTable = FakeTable([0xff; 192]);

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

const ALLOCATION_CHUNK: usize = 4;

#[inline(always)]
const unsafe fn allocation_layout<K: Key, V>(num_slots: usize) -> Layout {
  let s = allocation_size::<K, V>(num_slots);
  let a = align_of::<Slot<K, V>>();
  unsafe { Layout::from_size_align_unchecked(s, a) }
}

fn initial_slack<K: Key, V>() -> usize {
  capacity::<K, V>(initial_shift::<K, V>())
}

fn initial_shift<K: Key, V>() -> usize {
  K::Word::BITS - 1
}

fn initial_table<K:Key, V>() -> *const Slot<K, V> {
  if is_fake_table_ok::<K, V>() {
    &raw const FAKE_TABLE as _
  } else {
    null()
  }
}

fn initial_limit<K:Key, V>() -> *const Slot<K, V> {
  initial_table::<K, V>()
}

#[inline(always)]
const fn is_fake_table_ok<K: Key, V>() -> bool {
  align_of::<[Slot<K, V>; 3]>() <= align_of::<FakeTable>()
    && size_of::<[Slot<K, V>; 3]>() <= size_of::<FakeTable>()
}

#[inline(always)]
fn is_initial_null_table<K:Key, V>(table: *mut Slot<K, V>) -> bool {
  ! is_fake_table_ok::<K, V>() && table.is_null()
}

#[inline(always)]
fn is_initial_fake_table<K:Key, V>(_: *mut Slot<K, V>, shift: usize) -> bool {
  is_fake_table_ok::<K, V>() && shift == initial_shift::<K, V>()
}

#[inline(always)]
fn is_uninit<K:Key, V>(shift: usize) -> bool {
  shift == initial_shift::<K, V>()
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
  (h.cast::<W::UInt>() >> s).into() as usize
}

#[inline(always)]
fn capacity<K: Key, V>(s: usize) -> usize {
  /*
  let n: u64 = (! (K::Word::MAX >> 1)).into();
  let n = (n >> s).wrapping_cast::<K::Word>();
  let n: u64 = (n | K::Word::asr(n, K::BITS - 1)).into();
  n.wrapping_cast()
  */
  let n = (! (K::Word::MAX >> 1)).cast::<<K::Word as Word>::UInt>();
  let n = (n >> s).wrapping_cast::<K::Word>();
  let n = (n | K::Word::asr(n, K::BITS - 1)).cast::<<K::Word as Word>::UInt>();
  n.into() as usize
}

#[inline(always)]
unsafe fn search<K: Key, V>(t: *mut Slot<K, V>, s: usize, h: K::Word) -> (K::Word, *mut Slot<K, V>) {
  unsafe { assert_unchecked(s <= K::Word::BITS - 1) };
  let k = slot(h, s);
  let b = unsafe { t.add(k + 1) };
  let v = unsafe { slot_hash(b).read() };
  if ! (v < h) {
    let a = unsafe { t.add(k) };
    let u = unsafe { slot_hash(a).read() };
    let p = select_unpredictable(u < h, b, a);
    let x = select_unpredictable(u < h, v, u);
    (x, p)
  } else {
    cold_path();
    let mut p = b;
    let mut x;
    loop {
      p = unsafe { p.add(1) };
      x = unsafe { slot_hash(p).read() };
      if ! (x < h) { break }
    }
    (x, p)
  }
}

impl<K: Key, V> IntMap<K, V> {
  #[inline(always)]
  fn from_seed(m: (<K::Word as Hash>::Seed0, <K::Word as Hash>::Seed1)) -> Self {
    Self {
      table: initial_table::<K, V>(),
      shift: initial_shift::<K, V>(),
      slack: initial_slack::<K, V>(),
      limit: initial_limit::<K, V>(),
      seed0: m.0,
      seed1: m.1,
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
    let m = self.seed0;
    let h = hash(key, m);
    if is_initial_null_table(t) { return }
    let k = slot(h, s);
    let _ = unsafe { slot_hash(t.add(k)).read_volatile() };
    let _ = unsafe { slot_hash(t.add(k + 1)).read_volatile() };
  }

  /// Returns whether the map contains the given key.
  #[inline(always)]
  pub fn contains_key(&self, key: K) -> bool {
    let t = self.table.cast_mut();
    let s = self.shift;
    let m = self.seed0;
    let h = hash(key, m);
    if is_initial_null_table(t) { return false }
    unsafe { search(t, s, h) }.0 == h
  }

  /// Returns a reference to the value associated with the given key, if
  /// present.
  #[inline(always)]
  pub fn get(&self, key: K) -> Option<&V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let m = self.seed0;
    if is_initial_null_table(t) { return None }
    let h = hash(key, m);
    let a = unsafe { search(t, s, h) };
    if a.0 != h {
      None
    } else {
      Some(unsafe { &*slot_data(a.1) })
    }
  }

  /// Returns a mutable reference to the value associated with the given key,
  /// if present.
  #[inline(always)]
  pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let m = self.seed0;
    let h = hash(key, m);
    if is_initial_null_table(t) { return None }
    let a = unsafe { search(t, s, h) };
    if a.0 != h {
      None
    } else {
      Some(unsafe { &mut *slot_data(a.1) })
    }
  }

  /// For each key in the given array, returns a mutable reference to the
  /// associated value, if present.
  ///
  /// # Panics
  ///
  /// Panics if any key is the same as any other key.
  pub fn get_disjoint_mut<const N: usize>(&mut self, keys: [K; N]) -> [Option<&mut V>; N] {
    let words = keys.map(K::into_word);
    let mut is_disjoint = true;
    for i in 0 .. N {
      for j in 0 .. i {
        is_disjoint &= words[i] != words[j];
      }
    }
    assert!(is_disjoint);
    let mut out = [const { None }; N];
    let t = self.table.cast_mut();
    let s = self.shift;
    let m = self.seed0;
    if is_initial_null_table(t) { return out }
    for i in 0 .. N {
      let h = K::Word::hash(words[i], m);
      let a = unsafe { search(t, s, h) };
      out[i] =
        if a.0 != h {
          None
        } else {
          Some(unsafe { &mut *slot_data(a.1) })
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
    let m = self.seed0;
    let h = hash(key, m);
    if is_initial_null_table(t) {
      cold_path();
      let _: *mut V = self.insert_init(h, value);
      None
    } else {
      let a = unsafe { search(t, s, h) };
      if a.0 == h {
        Some(unsafe { slot_data(a.1).replace(value) })
      } else {
        if is_initial_fake_table(t, s) {
          cold_path();
          let _: *mut V = self.insert_init(h, value);
        } else {
          let r = self.slack;
          let z = self.limit.cast_mut();
          let mut p = a.1;
          let mut x = a.0;
          let mut y = value;
          unsafe { slot_hash(p).write(h) };
          while x != K::MAX {
            y = unsafe { slot_data(p).replace(y) };
            p = unsafe { p.add(1) };
            x = unsafe { slot_hash(p).replace(x) };
          }
          unsafe { slot_data(p).write(y) };
          if unsafe { z.offset_from_unsigned(p) } == 1 || r == 0 {
            cold_path();
            let _: *mut V = self.insert_grow(h, p);
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
    let s = K::BITS - ctz(w);
    assert!(d <= allocation_max_num_slots::<K, V>());
    let l = unsafe { allocation_layout::<K, V>(d) };
    let t = unsafe { alloc(l) } as *mut Slot<K, V>;
    if t.is_null() { match handle_alloc_error(l) { } }
    for i in 0 .. d { unsafe { slot_hash(t.add(i)).write(K::MAX) }; }
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
  fn insert_grow(&mut self, h: K::Word, last_write: *mut Slot<K, V>) -> *mut V {
    // Remove the last slot so that the table is in a valid state, even if we
    // panic.
    let last_write_hash = unsafe { slot_hash(last_write).replace(K::MAX) };
    // Retrieve and compute values for the old table.
    let old_t = self.table.cast_mut();
    let old_s = self.shift;
    let old_r = self.slack;
    let old_z = self.limit.cast_mut();
    let old_d = ptr_diff(old_z, old_t);
    let old_w = 1 << K::BITS - old_s;
    let old_e = old_d - old_w;
    // If s == 0, then the map can hold every possible key and should never grow.
    debug_assert!(0 != old_s);
    debug_assert!(old_s <= K::BITS - 1);
    // Compute new sizes.
    let new_s = old_s - 1;
    let new_w = 1 << K::BITS - new_s;
    let new_e =
      if new_s == 0 {
        0 // special case, we can store every possible key
      } else if last_write == unsafe { old_z.sub(1) } {
        old_e * 2 // if we wrote in the final slot
      } else if old_e < ctz(new_w) {
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
      unsafe { slot_hash(p).write(K::MAX) };
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
      i = select_unpredictable(x != K::MAX, k + 1, i);
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
    let m = self.seed0;
    let h = hash(key, m);
    if is_initial_null_table(t) { return None }
    let (x, p) = unsafe { search(t, s, h) };
    if x != h {
      None
    } else {
      let r = self.slack;
      self.slack = r + 1;
      let value = unsafe { slot_data(p).read() };
      let mut p = p;
      let mut a;
      let mut i = ptr_diff(p, t);
      loop {
        a = p;
        p = unsafe { p.add(1) };
        i = i + 1;
        let x = unsafe { slot_hash(p).read() };
        if ! (slot(x, s) < i && /* likely */ x != K::MAX) { break }
        unsafe { slot_hash(a).write(x) };
        unsafe { slot_data(a).write(slot_data(p).read()) };
        // NOTE: We could do the loop exit test here instead, with the
        // modification that we read data as MaybeUninit<V>.
      }
      unsafe { slot_hash(a).write(K::MAX) };
      Some(value)
    }
  }

  /// Returns a view of the entry in the map corresponding to the given key for
  /// subsequent inspection and modification.
  #[inline(always)]
  pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
    let t = self.table.cast_mut();
    let s = self.shift;
    let m = self.seed0;
    let h = hash(key, m);
    if is_initial_null_table(t) {
      Entry::Vacant(
        VacantEntry {
          map: self,
          pos: null_mut(),
          other: K::MAX,
          entry: h
        }
      )
    } else {
      let a = unsafe { search(t, s, h) };
      if a.0 == h {
        Entry::Occupied(
          OccupiedEntry {
            map: self,
            pos: a.1
          }
        )
      } else {
        Entry::Vacant(
          VacantEntry {
            map: self,
            pos: a.1,
            other: a.0,
            entry: h
          }
        )
      }
    }
  }

  #[inline(always)]
  unsafe fn insert_at(&mut self, pos: *mut Slot<K, V>, other: K::Word, entry: K::Word, value: V) -> &mut V {
    let s = self.shift;
    let inserted_at =
      if is_uninit::<K, V>(s) {
        cold_path();
        self.insert_init(entry, value)
      } else {
        let r = self.slack;
        let z = self.limit.cast_mut();
        let mut p = pos;
        let mut x = other;
        let mut y = value;
        unsafe { slot_hash(p).write(entry) };
        while x != K::MAX {
          y = unsafe { slot_data(p).replace(y) };
          p = unsafe { p.add(1) };
          x = unsafe { slot_hash(p).replace(x) };
        }
        unsafe { slot_data(p).write(y) };
        if p == unsafe { z.sub(1) } || r == 0 {
          cold_path();
          self.insert_grow(entry, p)
        } else {
          self.slack = r - 1;
          unsafe { slot_data(pos) }
        }
      };
    unsafe { &mut *inserted_at }
  }

  #[inline(always)]
  unsafe fn remove_at(&mut self, pos: *mut Slot<K, V>) -> V {
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    self.slack = r + 1;
    let value = unsafe { slot_data(pos).read() };
    let mut p = pos;
    let mut a;
    let mut i = ptr_diff(p, t);
    loop {
      a = p;
      p = unsafe { p.add(1) };
      i = i + 1;
      let x = unsafe { slot_hash(p).read() };
      if ! (slot(x, s) < i && /* likely */ x != K::MAX) { break }
      unsafe { slot_hash(a).write(x) };
      unsafe { slot_data(a).write(slot_data(p).read()) };
    }
    unsafe { slot_hash(a).write(K::MAX) };
    value
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
  pub fn get_or_insert_with<F: FnOnce() -> V>(&mut self, key: K, default: F) -> &mut V {
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
          if unsafe { slot_hash(p).read() } != K::MAX {
            unsafe { slot_hash(p).write(K::MAX) };
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
        let mut i = ptr_diff(z, t);
        unsafe { assert_unchecked(i % ALLOCATION_CHUNK == 0) };
        unsafe { assert_unchecked(i != 0) };
        loop {
          unsafe { slot_hash(p).write(K::MAX) };
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
    if is_uninit::<K, V>(s) { return }
    let n = capacity::<K, V>(s) - r;
    let d = ptr_diff(z, t);
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
          let a = p;
          p = unsafe { p.add(1) };
          if x != K::MAX {
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
    let t = self.table.cast_mut();
    let s = self.shift;
    let r = self.slack;
    let m = self.seed1;
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
    let m = self.seed1;
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
    let m = self.seed1;
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
    ptr_diff(z, t)
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
      if x != K::MAX {
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
    unsafe { self.map.remove_at(self.pos) }
  }
}

impl<'a, K: Key, V> VacantEntry<'a, K, V> {
  /// Inserts the given value into the entry, and returns a mutable reference
  /// to it.
  #[inline(always)]
  pub fn insert(self, value: V) -> &'a mut V {
    unsafe { self.map.insert_at(self.pos, self.other, self.entry, value) }
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
    let mut a;
    let mut x;
    loop {
      x = unsafe { slot_hash(p).read()};
      a = p;
      p = unsafe { p.add(1) };
      if x != K::MAX { break }
    }
    self.len = n - 1;
    self.pos = p;
    Some((self.f)(a, x))
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }

  #[inline(always)]
  fn fold<U, G: FnMut(U, T) -> U>(self, init: U, g: G) -> U {
    let mut n = self.len;
    let mut p = self.pos;
    let mut f = self.f;
    let mut u = init;
    let mut g = g;
    if n != 0 {
      loop {
        let x = unsafe { slot_hash(p).read() };
        let a = p;
        p = unsafe { p.add(1) };
        if x != K::MAX {
          u = g(u, f(a, x));
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
