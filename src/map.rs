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
use core::hint::select_unpredictable;
use core::mem::MaybeUninit;
use core::mem::needs_drop;
use core::ops::Index;
use core::ptr::addr_eq;
use core::ptr::write_bytes;
use rand_core::RngCore;

use crate::key::Key;
use crate::key::private::Word;

/// A fast hash map keyed by types representable as [`NonZeroU32`](core::num::NonZeroU32)
/// or [`NonZeroU64`](core::num::NonZeroU64).
pub struct IntMap<K: Key, V> {
  slack: usize,
  shift: usize,
  head: *const K::Word,
  data: *const V,
  seed: (K::Word, K::Word),
  seed_inverted: (K::Word, K::Word),
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
  pos: usize,
}

/// A view of a vacant entry in a map.
pub struct VacantEntry<'a, K: Key, V> {
  map: &'a mut IntMap<K, V>,
  pos: usize,
  cur: K::Word,
  hash: K::Word,
}

unsafe impl<K: Key + Send, V: Send> Send for IntMap<K, V> {
}

unsafe impl<K: Key + Sync, V: Sync> Sync for IntMap<K, V> {
}

#[inline(always)]
fn prefetch_read<T>(_p: *const T) {
  #[cfg(feature = "nightly")]
  if size_of::<T>() != 0 { core::hint::prefetch_read(_p, core::hint::Locality::L1) }
}

#[inline(always)]
fn prefetch_write<T>(_p: *mut T) {
  #[cfg(feature = "nightly")]
  if size_of::<T>() != 0 { core::hint::prefetch_write(_p, core::hint::Locality::L1) }
}

#[inline(always)]
fn ptr_diff<T>(x: *const T, y: *const T) -> usize {
  x.addr().wrapping_sub(y.addr()) / size_of::<T>()
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
  size_of::<K::Word>() + size_of::<V>()
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
  max(align_of::<K::Word>(), align_of::<V>())
}

#[inline(always)]
const fn allocation_chunk<K: Key, V>() -> usize {
  1 << max(2, ctz(align_of::<V>()).saturating_sub(ctz(size_of::<K::Word>())))
}

#[inline(always)]
const unsafe fn allocation_layout<K: Key, V>(num_slots: usize) -> Layout {
  let s = allocation_size::<K, V>(num_slots);
  let a = allocation_align::<K, V>();
  unsafe { Layout::from_size_align_unchecked(s, a) }
}

#[inline(always)]
const fn is_dummy<K: Key>(s: usize) -> bool {
  s == K::BITS - 1
}

#[inline(always)]
fn capacity<K: Key>(s: usize) -> usize {
  let n = ! (! K::Word::ZERO >> 1);
  let n = n >> s;
  let n = n | K::Word::asr(n, K::Word::BITS - 1);
  K::Word::into_usize(n)
}

#[inline(always)]
fn invert_seed<W: Word>(m: (W, W)) -> (W, W) {
  let a = m.0;
  let b = m.1;
  let c = W::invert(a.wrapping_mul(b));
  (c.wrapping_mul(a), c.wrapping_mul(b))
}

#[inline(always)]
fn hash<K: Key>(k: K, (a, b): (K::Word, K::Word)) -> K::Word {
  let h = K::into_word(k);
  let h = h.wrapping_mul(a);
  let h = h.swap_bytes();
  let h = h.wrapping_mul(b);
  h
}

#[inline(always)]
unsafe fn invert_hash<K: Key>(h: K::Word, (a, b): (K::Word, K::Word)) -> K {
  let h = h.wrapping_mul(a);
  let h = h.swap_bytes();
  let h = h.wrapping_mul(b);
  unsafe { K::from_word(h) }
}

#[inline(always)]
fn slot<W: Word>(h: W, s: usize) -> usize {
  W::into_usize(! h >> s)
}

impl<K: Key, V> IntMap<K, V> {
  #[inline(always)]
  fn from_seed(m: (K::Word, K::Word)) -> Self {
    Self {
      slack: capacity::<K>(K::BITS - 1),
      shift: K::BITS - 1,
      head: K::EMPTY_TABLE,
      data: K::EMPTY_TABLE.wrapping_add(3).cast(),
      seed: m,
      seed_inverted: invert_seed(m),
    }
  }

  /// Creates an empty map, seeding the hash function from a thread-local
  /// random number generator.
  pub fn new() -> Self {
    Self::from_seed(K::Word::seed_nondet())
  }

  /// Creates an empty map, seeding the hash function from the given random
  /// number generator.
  pub fn new_seeded(rng: &mut impl RngCore) -> Self {
    Self::from_seed(K::Word::seed(rng))
  }

  /// Returns the number of items.
  #[inline(always)]
  pub fn len(&self) -> usize {
    let r = self.slack;
    let s = self.shift;
    unsafe { assert_unchecked(s <= K::BITS - 1) };
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
    let t = self.head;
    let m = self.seed;
    unsafe { assert_unchecked(s <= K::BITS - 1) };
    let h = hash(key, m);
    let k = slot(h, s);
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
    let t = self.head;
    let u = self.data;
    let m = self.seed;
    unsafe { assert_unchecked(s <= K::BITS - 1) };
    unsafe { assert_unchecked(u.addr() != 0) };
    let h = hash(key, m);
    let k = slot(h, s);
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
    let t = self.head;
    let u = self.data.cast_mut();
    let m = self.seed;
    unsafe { assert_unchecked(s <= K::BITS - 1) };
    unsafe { assert_unchecked(u.addr() != 0) };
    let h = hash(key, m);
    let k = slot(h, s);
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
  fn insert_init(&mut self, h: K::Word, value: V) -> *mut V {
    let w = 4 * allocation_chunk::<K, V>();
    let e = allocation_chunk::<K, V>();
    let d = w + e;
    let s = K::BITS - ctz(w);
    assert!(d <= allocation_max_num_slots::<K, V>());
    let l = unsafe { allocation_layout::<K, V>(d) };
    let t = unsafe { alloc(l) } as *mut K::Word;
    if t.is_null() { match handle_alloc_error(l) { } }
    let u = unsafe { t.add(d) } as *mut V;
    unsafe { write_bytes(t, 0u8, d) };
    let k = slot(h, s);
    unsafe { t.add(k).write(h) };
    unsafe { u.add(k).write(value) };
    self.slack = capacity::<K>(s) - 1;
    self.shift = s;
    self.head = t;
    self.data = u;
    unsafe { u.add(k) }
  }

  #[inline(never)]
  #[cold]
  fn insert_grow(&mut self, h: K::Word, last_write: usize) -> *mut V {
    let old_r = self.slack;
    let old_s = self.shift;
    let old_t = self.head.cast_mut();
    let old_u = self.data.cast_mut();
    let old_d = ptr_diff(old_u.cast(), old_t);
    let old_w = 1 << K::BITS - old_s;
    let old_e = old_d - old_w;
    // Place the table in a valid state in case we panic.
    let z = unsafe { old_t.add(last_write).replace(K::ZERO) };
    // Compute new sizes.
    debug_assert!(old_s != 0);
    let new_s = old_s - 1;
    let new_w = 1 << K::BITS - new_s;
    let new_e =
      if new_s == 0 {
        0 // special case, we can store every possible key
      } else if last_write + 1 == old_d {
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
    let new_t = unsafe { alloc(new_l) } as *mut K::Word;
    if new_t.is_null() { match handle_alloc_error(new_l) { } }
    let new_u = unsafe { new_t.add(new_d) } as *mut V;
    // Update struct fields.
    self.slack = old_r + (capacity::<K>(new_s) - capacity::<K>(old_s)) - 1;
    self.shift = new_s;
    self.head = new_t;
    self.data = new_u;
    // Initialize new table.
    let mut i = new_d;
    loop {
      i = i - allocation_chunk::<K, V>();
      unsafe { write_bytes(new_t.add(i), 0u8, allocation_chunk::<K, V>()) };
      if i == 0 { break }
    }
    // Re-add the last write so that we copy it to the new table.
    unsafe { old_t.add(last_write).write(z) };
    // Copy slots.
    let mut i = 0;
    let mut j = 0;
    loop {
      let x = unsafe { old_t.add(i).read() };
      let y = unsafe { old_u.add(i).cast::<MaybeUninit<V>>().read() };
      let k = slot(x, new_s);
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
    let mut i = slot(h, new_s);
    while unsafe { new_t.add(i).read() } != h {
      i = i + 1;
    }
    unsafe { new_u.add(i) }
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
    let r = self.slack;
    let s = self.shift;
    let t = self.head.cast_mut();
    let u = self.data.cast_mut();
    let m = self.seed;
    unsafe { assert_unchecked(s <= K::BITS - 1) };
    unsafe { assert_unchecked(u.addr() != 0) };
    let h = hash(key, m);
    let k = slot(h, s);
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
      Some(unsafe { u.add(i).replace(value) })
    } else {
      if is_dummy::<K>(s) {
        let _: *mut V = self.insert_init(h, value);
      } else {
        let mut i = i;
        let mut x = x;
        let mut y = value;
        unsafe { t.add(i).write(h) };
        while x != K::ZERO {
          y = unsafe { u.add(i).replace(y) };
          i = i + 1;
          x = unsafe { t.add(i).replace(x) };
        }
        unsafe { u.add(i).write(y) };
        if addr_eq(unsafe { t.add(i + 1) }, u) || r == 0 {
          let _: *mut V = self.insert_grow(h, i);
        } else {
          self.slack = r - 1;
        }
      }
      None
    }
  }

  /// Removes the given key from the map. Returns the previous value associated
  /// with the given key, if one was present.
  #[inline(always)]
  pub fn remove(&mut self, key: K) -> Option<V> {
    let r = self.slack;
    let s = self.shift;
    let t = self.head.cast_mut();
    let u = self.data.cast_mut();
    let m = self.seed;
    unsafe { assert_unchecked(s <= K::BITS - 1) };
    unsafe { assert_unchecked(u.addr() != 0) };
    let h = hash(key, m);
    let k = slot(h, s);
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
        if ! (slot(x, s) <= i - 1 && /* likely */ x != K::ZERO) { break }
        let y = unsafe { u.add(i).read() };
        unsafe { t.add(i - 1).write(x) };
        unsafe { u.add(i - 1).write(y) };
        // NOTE: We could do the loop exit test here instead.
      }
      unsafe { t.add(i - 1).write(K::ZERO) };
      Some(value)
    }
  }

  /// Returns a view of the entry in the map corresponding to the given key for
  /// subsequent inspection and modification.
  #[inline(always)]
  pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
    let s = self.shift;
    let t = self.head;
    let u = self.data.cast_mut();
    let m = self.seed;
    unsafe { assert_unchecked(s <= K::BITS - 1) };
    unsafe { assert_unchecked(u.addr() != 0) };
    let h = hash(key, m);
    let k = slot(h, s);
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
      Entry::Occupied(OccupiedEntry { map: self, pos: i })
    } else {
      Entry::Vacant(VacantEntry { map: self, pos: i, cur: x, hash: h })
    }
  }

  #[inline(always)]
  unsafe fn insert_at(&mut self, pos: usize, cur: K::Word, h: K::Word, value: V) -> &mut V {
    let r = self.slack;
    let s = self.shift;
    let t = self.head.cast_mut();
    let u = self.data.cast_mut();
    unsafe { assert_unchecked(s <= K::BITS - 1) };
    unsafe { assert_unchecked(u.addr() != 0) };
    let p =
      if is_dummy::<K>(s) {
        self.insert_init(h, value)
      } else {
        let mut i = pos;
        let mut x = cur;
        let mut y = value;
        unsafe { t.add(i).write(h) };
        while x != K::ZERO {
          y = unsafe { u.add(i).replace(y) };
          i = i + 1;
          x = unsafe { t.add(i).replace(x) };
        }
        unsafe { u.add(i).write(y) };
        if addr_eq(unsafe { t.add(i + 1) }, u) || r == 0 {
          self.insert_grow(h, i)
        } else {
          self.slack = r - 1;
          unsafe { u.add(pos) }
        }
      };
    unsafe { &mut *p }
  }


  #[inline(always)]
  unsafe fn remove_at(&mut self, pos: usize) -> V {
    let r = self.slack;
    let s = self.shift;
    let t = self.head.cast_mut();
    let u = self.data.cast_mut();
    unsafe { assert_unchecked(s <= K::BITS - 1) };
    unsafe { assert_unchecked(u.addr() != 0) };
    self.slack = r + 1;
    let value = unsafe { u.add(pos).read() };
    let mut i = pos;
    loop {
      i = i + 1;
      let x = unsafe { t.add(i).read() };
      if ! (slot(x, s) <= i - 1 && /* likely */ x != K::ZERO) { break }
      let y = unsafe { u.add(i).read() };
      unsafe { t.add(i - 1).write(x) };
      unsafe { u.add(i - 1).write(y) };
    }
    unsafe { t.add(i - 1).write(K::ZERO) };
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
  pub fn get_or_insert_default(&mut self, key: K) -> &mut V where V: Default {
    match self.entry(key) {
      Entry::Occupied(entry) => entry.into_mut(),
      Entry::Vacant(entry) => entry.insert(V::default()),
    }
  }

  /// TODO:
  pub fn get_disjoint_mut<const N: usize>(&mut self, keys: [K; N]) -> [Option<&mut V>; N] {
    let _ = keys;
    unimplemented!()
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
    let t = self.head.cast_mut();
    let u = self.data.cast_mut();
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
    let t = self.head.cast_mut();
    let u = self.data.cast_mut();
    if is_dummy::<K>(s) { return }
    let n = capacity::<K>(s) - r;
    let d = ptr_diff(u.cast(), t);
    self.slack = capacity::<K>(K::BITS - 1);
    self.shift = K::BITS - 1;
    self.head = K::EMPTY_TABLE;
    self.data = K::EMPTY_TABLE.wrapping_add(3).cast();
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
    let t = self.head;
    let u = self.data;
    let m = self.seed_inverted;
    unsafe { assert_unchecked(s <= K::BITS - 1) };
    unsafe { assert_unchecked(u.addr() != 0) };
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        pos: ptr_diff(u.cast(), t),
        head: t,
        f: move |x, i| unsafe { (invert_hash(x, m), &*u.add(i)) }
      };
    i
  }

  /// Returns an iterator yielding each key and a mutable reference to its
  /// associated value. The iterator item type is `(K, &mut V)`.
  #[inline(always)]
  pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = (K, &mut V)> + use<'_, K, V> {
    let r = self.slack;
    let s = self.shift;
    let t = self.head;
    let u = self.data.cast_mut();
    let m = self.seed_inverted;
    unsafe { assert_unchecked(s <= K::BITS - 1) };
    unsafe { assert_unchecked(u.addr() != 0) };
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        pos: ptr_diff(u.cast(), t),
        head: t,
        f: move |x, i| unsafe { (invert_hash(x, m), &mut *u.add(i)) }
      };
    i
  }

  /// Returns an iterator yielding each key. The iterator item type is `K`.
  #[inline(always)]
  pub fn keys(&self) -> impl ExactSizeIterator<Item = K> + use<'_, K, V> {
    let r = self.slack;
    let s = self.shift;
    let t = self.head;
    let u = self.data;
    let m = self.seed_inverted;
    unsafe { assert_unchecked(s <= K::BITS - 1) };
    unsafe { assert_unchecked(u.addr() != 0) };
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        pos: ptr_diff(u.cast(), t),
        head: t,
        f: move |x, _| unsafe { invert_hash(x, m) }
      };
    i
  }

  /// Returns an iterator yielding a reference to each value. The iterator item
  /// type is `&V`.
  #[inline(always)]
  pub fn values(&self) -> impl ExactSizeIterator<Item = &V> + use<'_, K, V> {
    let r = self.slack;
    let s = self.shift;
    let t = self.head;
    let u = self.data;
    unsafe { assert_unchecked(s <= K::BITS - 1) };
    unsafe { assert_unchecked(u.addr() != 0) };
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        pos: ptr_diff(u.cast(), t),
        head: t,
        f: move |_, i| unsafe { &*u.add(i) }
      };
    i
  }

  /// Returns an iterator yielding a mutable reference to each value. The
  /// iterator item type is `&mut V`.
  #[inline(always)]
  pub fn values_mut(&mut self) -> impl ExactSizeIterator<Item = &mut V> + use<'_, K, V> {
    let r = self.slack;
    let s = self.shift;
    let t = self.head;
    let u = self.data.cast_mut();
    unsafe { assert_unchecked(s <= K::BITS - 1) };
    unsafe { assert_unchecked(u.addr() != 0) };
    let i: Iter<K, _, _> =
      Iter {
        len: capacity::<K>(s) - r,
        pos: ptr_diff(u.cast(), t),
        head: t,
        f: move |_, i| unsafe { &mut *u.add(i) }
      };
    i
  }

  fn num_slots(&self) -> usize {
    let s = self.shift;
    let t = self.head;
    let u = self.data;
    if is_dummy::<K>(s) { return 0 }
    ptr_diff(u.cast(), t)
  }

  fn allocation_size(&self) -> usize {
    allocation_size::<K, V>(self.num_slots())
  }

  fn load_factor(&self) -> f64 {
    self.len() as f64 / self.num_slots() as f64
  }

  fn displacement_histogram(&self) -> [usize; 10] {
    let s = self.shift;
    let t = self.head;
    let u = self.data;
    let mut r = [0usize; 10];
    let mut i = ptr_diff(u.cast(), t);
    loop {
      i = i - 1;
      let x = unsafe { t.add(i).read() };
      if x != K::ZERO {
        r[usize::min(9, i - slot(x, s))] += 1;
      }
      if i == 0 { break }
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
  /// Gets a mutable reference to the value in the entry.
  #[inline(always)]
  pub fn get_mut(&mut self) -> &mut V {
    unsafe { &mut *self.map.data.cast_mut().add(self.pos) }
  }

  /// Converts itself into a mutable reference to the value in the entry, with
  /// a lifetime from the original borrow for the call to [`IntMap::entry`].
  #[inline(always)]
  pub fn into_mut(self) -> &'a mut V {
    unsafe { &mut *self.map.data.cast_mut().add(self.pos) }
  }

  /// Inserts the given value into the entry, and returns the previous value.
  #[inline(always)]
  pub fn insert(&mut self, value: V) -> V {
    unsafe { self.map.data.cast_mut().add(self.pos).replace(value) }
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
    unsafe { self.map.insert_at(self.pos, self.cur, self.hash, value) }
  }
}

struct Iter<K: Key, T, F: FnMut(K::Word, usize) -> T> {
  len: usize,
  pos: usize,
  head: *const K::Word,
  f: F,
}

impl<K: Key, T, F: FnMut(K::Word, usize) -> T> Iterator for Iter<K, T, F> {
  type Item = T;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let n = self.len;
    if n == 0 { return None }
    let t = self.head;
    let mut i = self.pos;
    let mut x;
    loop {
      i = i - 1;
      x = unsafe { t.add(i).read() };
      if x != K::ZERO { break }
    }
    self.len = n - 1;
    self.pos = i;
    Some((self.f)(x, i))
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.len, Some(self.len))
  }

  #[inline(always)]
  fn fold<U, G: FnMut(U, T) -> U>(self, init: U, g: G) -> U {
    let t = self.head;
    let mut n = self.len;
    let mut i = self.pos;
    let mut f = self.f;
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

impl<K: Key, T, F: FnMut(K::Word, usize) -> T> ExactSizeIterator for Iter<K, T, F> {
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

  #[cfg(feature = "nightly")]
  #[inline(always)]
  fn extend_one(&mut self, item: (K, V)) {
    let _: Option<V> = self.insert(item.0, item.1);
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
