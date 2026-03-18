#![allow(missing_docs)]

extern crate alloc;

use alloc::alloc::Layout;
use alloc::alloc::alloc;
use alloc::alloc::dealloc;
use alloc::alloc::handle_alloc_error;
use core::fmt::Debug;
use core::mem::MaybeUninit;
use core::hint::select_unpredictable;
use core::mem::needs_drop;
use core::num::NonZeroU64;
use core::ops::Index;
use core::ptr::addr_eq;
use core::ptr::null;
use core::ptr::write_bytes;
use rand_core::RngCore;

pub struct HashMap<V> {
  m: u64,
  s: usize,
  a: *const u64,
  b: *const V,
  r: usize,
}

static EMPTY: [u64; 3] = [u64::MAX; 3];

#[inline(always)]
fn allocation_slot_size<V>() -> usize {
  size_of::<u64>() + size_of::<V>()
}

#[inline(always)]
fn allocation_max_num_slots<V>() -> usize {
  isize::MAX as usize / allocation_slot_size::<V>()
}

#[inline(always)]
fn allocation_size<V>(num_slots: usize) -> usize {
  num_slots * allocation_slot_size::<V>()
}

#[inline(always)]
fn allocation_align<V>() -> usize {
  usize::max(align_of::<u64>(), align_of::<V>())
}

#[inline(always)]
fn allocation_chunk<V>() -> usize {
  1 << u32::max(2, align_of::<V>().trailing_zeros().saturating_sub(size_of::<u64>().trailing_zeros()))
}

#[inline(always)]
unsafe fn allocation_layout<V>(num_slots: usize) -> Layout {
  unsafe { Layout::from_size_align_unchecked(allocation_size::<V>(num_slots), allocation_align::<V>()) }
}

#[inline(always)]
fn capacity(s: usize) -> usize {
  1 << 64 - s - 1
}

#[inline(always)]
fn hash(key: NonZeroU64, m: u64) -> u64 {
  key.get().wrapping_mul(m).wrapping_sub(1)
}

#[inline(always)]
fn slot(h: u64, s: usize) -> usize {
  (h >> s) as usize
}

impl<V> HashMap<V> {
  #[inline(always)]
  fn internal_new(m: u64) -> Self {
    Self {
      m: m | 1,
      s: 63,
      a: &EMPTY as *const u64,
      b: null(),
      r: 1,
    }
  }

  pub fn new() -> Self {
    Self::internal_new(dandelion::thread_local::u64())
  }

  pub fn new_seeded(rng: &mut impl RngCore) -> Self {
    Self::internal_new(rng.next_u64())
  }

  #[inline(always)]
  pub fn len(&self) -> usize {
    let s = self.s;
    let r = self.r;

    capacity(s) - r
  }

  #[inline(always)]
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  #[inline(always)]
  pub fn contains_key(&self, key: NonZeroU64) -> bool {
    let m = self.m;
    let s = self.s;
    let a = self.a;
    let h = hash(key, m);
    let k = slot(h, s);
    let u = unsafe { a.wrapping_add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { a.wrapping_add(i).read() };
      if ! (x < h) { break }
    }
    let x = select_unpredictable(u < h, x, u);
    x == h
  }

  #[inline(always)]
  pub fn get(&self, key: NonZeroU64) -> Option<&V> {
    let m = self.m;
    let s = self.s;
    let a = self.a;
    let b = self.b;
    let h = hash(key, m);
    let k = slot(h, s);
    let u = unsafe { a.wrapping_add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { a.wrapping_add(i).read() };
      if ! (x < h) { break }
    }
    let i = select_unpredictable(u < h, i, k);
    let x = select_unpredictable(u < h, x, u);
    if x != h {
      None
    } else {
      Some(unsafe { &*b.wrapping_add(i) })
    }
  }

  #[inline(always)]
  pub fn get_mut(&mut self, key: NonZeroU64) -> Option<&mut V> {
    let m = self.m;
    let s = self.s;
    let a = self.a;
    let b = self.b as *mut V;
    let h = hash(key, m);
    let k = slot(h, s);
    let u = unsafe { a.wrapping_add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { a.wrapping_add(i).read() };
      if ! (x < h) { break }
    }
    let i = select_unpredictable(u < h, i, k);
    let x = select_unpredictable(u < h, x, u);
    if x != h {
      None
    } else {
      Some(unsafe { &mut *b.wrapping_add(i) })
    }
  }

  #[inline(never)]
  #[cold]
  fn internal_init(&mut self, h: u64, value: V) {
    let w = 4 * allocation_chunk::<V>();
    let e = allocation_chunk::<V>();
    let d = w + e;
    let s = 64 - w.trailing_zeros() as usize;
    assert!(d <= allocation_max_num_slots::<V>());
    let l = unsafe { allocation_layout::<V>(d) };
    let a = unsafe { alloc(l) } as *mut u64;
    if a.is_null() { match handle_alloc_error(l) { } }
    let b = a.wrapping_add(d) as *mut V;
    let k = slot(h, s);
    for i in 0 .. d { unsafe { a.wrapping_add(i).write(u64::MAX) } }
    unsafe { a.wrapping_add(k).write(h) };
    unsafe { b.wrapping_add(k).write(value) };
    self.s = s;
    self.a = a;
    self.b = b;
    self.r = capacity(s) - 1;
  }

  #[inline(never)]
  #[cold]
  fn internal_grow(&mut self, last_write: usize) {
    let old_s = self.s;
    let old_a = self.a as *mut u64;
    let old_b = self.b as *mut V;
    let old_r = self.r.wrapping_add(1);
    let old_c = capacity(old_s);
    let old_d = unsafe { (old_b as *mut u64).offset_from_unsigned(old_a) };
    let old_w = 1 << 64 - old_s;
    let old_e = old_d - old_w;
    let old_l = unsafe { allocation_layout::<V>(old_d) };
    // Temporarily place the table in a valid state in case we panic.
    let h = unsafe { old_a.wrapping_add(last_write).replace(u64::MAX) };
    self.r = old_r;
    let new_s = if old_r == 0 { old_s - 1 } else { old_s };
    let new_c = capacity(new_s);
    let new_w = 1 << 64 - new_s;
    let new_e = if last_write == old_d - 1 { 2 * old_e } else { old_e };
    let new_d = new_w + new_e;
    // Panic if the layout would overflow.
    assert!(new_d <= allocation_max_num_slots::<V>());
    // Alloc.
    let new_l = unsafe { allocation_layout::<V>(new_d) };
    let new_a = unsafe { alloc(new_l) } as *mut u64;
    if new_a.is_null() { match handle_alloc_error(new_l) { } }
    // At this point, we're guaranteed to successfully finish growing the
    // table.
    let new_b = new_a.wrapping_add(new_d) as *mut V;
    // We re-add the last write and compute some values that include that slot.
    unsafe { old_a.wrapping_add(last_write).write(h) };
    let old_n = old_c - old_r + 1;
    let new_r = old_r + (new_c - old_c) - 1;
    // Update struct fields.
    self.s = new_s;
    self.a = new_a;
    self.b = new_b;
    self.r = new_r;
    // Initialize new table.
    let mut i = 0;
    loop {
      unsafe { write_bytes(new_a.wrapping_add(i), 0xff, 4) };
      i = i + 4;
      if i == new_d { break }
    }
    // Compress non-empty slots.
    let mut i = 0;
    let mut j = 0;
    loop {
      let x = unsafe { old_a.wrapping_add(i).read() };
      let y = unsafe { old_b.wrapping_add(i).cast::<MaybeUninit<V>>().read() };
      unsafe { old_a.wrapping_add(j).write(x) };
      unsafe { old_b.wrapping_add(j).cast::<MaybeUninit<V>>().write(y) };
      i = i + 1;
      j = j + (x != u64::MAX) as usize;
      if i == old_d { break }
    }
    // Copy slots to new allocated block.
    let mut i = 0;
    let mut j = 0;
    loop {
      let x = unsafe { old_a.wrapping_add(i).read() };
      let y = unsafe { old_b.wrapping_add(i).read() };
      j = usize::max(j, slot(x, new_s));
      unsafe { new_a.wrapping_add(j).write(x) };
      unsafe { new_b.wrapping_add(j).write(y) };
      i = i + 1;
      if i == old_n { break }
    }
    // The map is now in a valid state, even if deallocating panics.
    unsafe { dealloc(old_a as *mut u8, old_l) }
  }

  #[inline(always)]
  pub fn insert(&mut self, key: NonZeroU64, value: V) -> Option<V> {
    let m = self.m;
    let s = self.s;
    let a = self.a;
    let b = self.b as *mut V;
    let h = hash(key, m);
    let k = slot(h, s);
    let u = unsafe { a.wrapping_add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { a.wrapping_add(i).read() };
      if ! (x < h) { break }
    }
    let i = select_unpredictable(u < h, i, k);
    let x = select_unpredictable(u < h, x, u);
    if x == h {
      Some(unsafe { b.wrapping_add(i).replace(value) })
    } else {
      if b.is_null() {
        self.internal_init(h, value);
      } else {
        let a = a as *mut u64;
        let r = self.r;
        self.r = r.wrapping_sub(1);
        let mut i = i;
        let mut x = x;
        let mut y = value;
        unsafe { a.wrapping_add(i).write(h) };
        while x != u64::MAX {
          y = unsafe { b.wrapping_add(i).replace(y) };
          i = i + 1;
          x = unsafe { a.wrapping_add(i).replace(x) };
        }
        unsafe { b.wrapping_add(i).write(y) };
        if r == 0 || addr_eq(a.wrapping_add(i + 1), b) {
          self.internal_grow(i);
        }
      }
      None
    }
  }

  #[inline(always)]
  pub fn remove(&mut self, key: NonZeroU64) -> Option<V> {
    let m = self.m;
    let s = self.s;
    let a = self.a as *mut u64;
    let b = self.b as *mut V;
    let r = self.r;
    let h = hash(key, m);
    let k = slot(h, s);
    let u = unsafe { a.wrapping_add(k).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { a.wrapping_add(i).read() };
      if ! (x < h) { break }
    }
    let i = select_unpredictable(u < h, i, k);
    let x = select_unpredictable(u < h, x, u);
    if x != h {
      None
    } else {
      self.r = r + 1;
      let value = unsafe { b.wrapping_add(i).read() };
      let mut i = i;
      loop {
        let x = unsafe { a.wrapping_add(i + 1).read() };
        if ! (slot(x, s) <= i && /* likely */ x != u64::MAX) { break }
        let y = unsafe { b.wrapping_add(i + 1).read() };
        unsafe { a.wrapping_add(i).write(x) };
        unsafe { b.wrapping_add(i).write(y) };
        i = i + 1;
      }
      unsafe { a.wrapping_add(i).write(u64::MAX) };
      Some(value)
    }
  }

  pub fn clear(&mut self) {
    let s = self.s;
    let a = self.a as *mut u64;
    let b = self.b as *mut V;
    let r = self.r;
    if b.is_null() { return }
    let c = capacity(s);
    let n = c - r;
    let d = unsafe { (b as *mut u64).offset_from_unsigned(a) };
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
        // Also, we update `self.r` as we go instead of once at the end.
        let mut n = n;
        let mut r = r;
        let mut i = d - 1;
        loop {
          if unsafe { a.wrapping_add(i).read() } != u64::MAX {
            unsafe { a.wrapping_add(i).write(u64::MAX) };
            r = r + 1;
            self.r = r;
            unsafe { b.wrapping_add(i).drop_in_place() };
            n = n - 1;
            if n == 0 { break }
          }
          i = i - 1;
        }
      }
    } else {
      if n != 0 {
        self.r = c;
        let mut i = 0;
        loop {
          unsafe { write_bytes(a.wrapping_add(i), 0xff, 4) };
          i = i + 4;
          if i == d { break }
        }
      }
    }
  }

  pub fn reset(&mut self) {
    let s = self.s;
    let a = self.a;
    let b = self.b as *mut V;
    let r = self.r;
    if b.is_null() { return }
    let n = capacity(s) - r;
    let d = unsafe { (b as *mut u64).offset_from_unsigned(a) };
    self.s = 63;
    self.a = &EMPTY as *const u64;
    self.b = null();
    self.r = 1;
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
        let mut i = d - 1;
        loop {
          if unsafe { a.wrapping_add(i).read() } != u64::MAX {
            unsafe { b.wrapping_add(i).drop_in_place() };
            n = n - 1;
            if n == 0 { break }
          }
          i = i - 1;
        }
      }
    }
    unsafe { dealloc(a as *mut u8, allocation_layout::<V>(d)) };
  }

  #[inline(always)]
  pub fn values(&self) -> impl ExactSizeIterator<Item = &V> + use<'_, V> {
    Iter {
      n: capacity(self.s) - self.r,
      i: 0,
      a: self.a,
      b: self.b as *mut V,
      f: move |_, b| unsafe { &*b }
    }
  }

  #[inline(always)]
  pub fn values_mut(&mut self) -> impl ExactSizeIterator<Item = &mut V> + use<'_, V> {
    Iter {
      n: capacity(self.s) - self.r,
      i: 0,
      a: self.a,
      b: self.b as *mut V,
      f: move |_, b| unsafe { &mut *b }
    }
  }

  fn internal_num_slots(&self) -> usize {
    let a = self.a;
    let b = self.b;
    if b.is_null() { return 0; }
    unsafe { (b as *mut u64).offset_from_unsigned(a) }
  }

  fn internal_allocation_size(&self) -> usize {
    allocation_size::<V>(self.internal_num_slots())
  }

  fn internal_load_factor(&self) -> f64 {
    self.len() as f64 / self.internal_num_slots() as f64
  }
}

impl<V> Drop for HashMap<V> {
  fn drop(&mut self) {
    self.reset()
  }
}

impl<V> Index<NonZeroU64> for HashMap<V> {
  type Output = V;

  #[inline(always)]
  fn index(&self, index: NonZeroU64) -> &Self::Output {
    self.get(index).unwrap()
  }
}

struct Iter<V, T, F: FnMut(u64, *mut V) -> T> {
  n: usize,
  i: usize,
  a: *const u64,
  b: *mut V,
  f: F,
}

impl<V, T, F: FnMut(u64, *mut V) -> T> Iterator for Iter<V, T, F> {
  type Item = T;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let n = self.n;
    if n == 0 { return None; }
    let a = self.a;
    let b = self.b;
    let mut i = self.i;
    let mut x;
    loop {
      x = unsafe { a.wrapping_add(i).read() };
      if x != u64::MAX { break }
      i = i + 1;
    }
    self.n = n - 1;
    self.i = i + 1;
    Some((self.f)(x, b.wrapping_add(i)))
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.n, Some(self.n))
  }

  #[inline(always)]
  fn fold<U, G: FnMut(U, T) -> U>(self, init: U, g: G) -> U {
    let a = self.a;
    let b = self.b;
    let mut n = self.n;
    let mut i = self.i;
    let mut f = self.f;
    let mut u = init;
    let mut g = g;
    if n != 0 {
      loop {
        let x = unsafe { a.wrapping_add(i).read() };
        if x != u64::MAX {
          u = g(u, f(x, b.wrapping_add(i)));
          n = n - 1;
          if n == 0 { break }
        }
        i = i + 1;
      }
    }
    u
  }
}

impl<V, T, F: FnMut(u64, *mut V) -> T> ExactSizeIterator for Iter<V, T, F> {
  #[inline(always)]
  fn len(&self) -> usize {
    self.n
  }
}

impl<V: Clone> Clone for HashMap<V> {
  fn clone(&self) -> Self {
    unimplemented!()
  }
}

impl <V: Debug> Debug for HashMap<V> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let _ = f;
    unimplemented!()
  }
}

impl<V> Default for HashMap<V> {
  fn default() -> Self {
    Self::new()
  }
}

impl<V> FromIterator<(NonZeroU64, V)> for HashMap<V> {
  fn from_iter<I: IntoIterator<Item = (NonZeroU64, V)>>(iter: I) -> Self {
    let mut t = Self::new();
    iter.into_iter().for_each(|(x, y)| { let _ = t.insert(x, y); });
    t
  }
}

pub mod internal {
  //! Unstable API exposing implementation details for benchmarks and tests.

  #![allow(missing_docs)]

  use super::HashMap;

  pub fn num_slots<V>(t: &HashMap<V>) -> usize {
    return t.internal_num_slots();
  }

  pub fn allocation_size<V>(t: &HashMap<V>) -> usize {
    return t.internal_allocation_size();
  }

  pub fn load_factor<V>(t: &HashMap<V>) -> f64 {
    return t.internal_load_factor();
  }
}

pub fn get(t: &HashMap<u32>, key: NonZeroU64) -> Option<&u32> {
  t.get(key)
}

pub fn get_value(t: &HashMap<u32>, key: NonZeroU64) -> Option<u32> {
  match t.get(key) { None => None, Some(&y) => Some(y) }
}

pub fn contains_key(t: &HashMap<u32>, key: NonZeroU64) -> bool {
  t.contains_key(key)
}

pub fn insert(t: &mut HashMap<u32>, key: NonZeroU64, value: u32) {
  let _ = t.insert(key, value);
}

pub fn remove(t: &mut HashMap<u32>, key: NonZeroU64) {
  let _ = t.remove(key);
}

pub fn clear(t: &mut HashMap<u32>) {
  t.clear();
}

pub fn reset(t: &mut HashMap<u32>) {
  t.reset();
}
