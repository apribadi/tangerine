#![allow(missing_docs)]

extern crate alloc;

use alloc::alloc::Layout;
use alloc::alloc::alloc;
use alloc::alloc::dealloc;
use alloc::alloc::handle_alloc_error;
use core::fmt::Debug;
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
      a: &raw const EMPTY[0],
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
    let _ = h;
    let _ = value;
    unimplemented!()
  }

  #[inline(never)]
  #[cold]
  fn internal_grow(&mut self, last_written_slot: usize) {
    let _ = last_written_slot;
    unimplemented!()
  }

  #[inline(always)]
  pub fn insert(&mut self, key: NonZeroU64, value: V) -> Option<V> {
    let m = self.m;
    let s = self.s;
    let a = self.a as *mut u64;
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
    let c = capacity(s);
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
        // Also, we update `self.r` as we go instead of once at the end.
        let mut n = n;
        let mut r = r;
        let mut i = unsafe { (b as *mut u64).offset_from_unsigned(a) } - 1;
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
        let mut p = a;
        loop {
          unsafe { write_bytes(p, 0xff, 4) };
          p = p.wrapping_add(4);
          if addr_eq(p, b) { break }
        }
      }
    }
  }

  pub fn reset(&mut self) {
    let s = self.s;
    let a = self.a;
    let b = self.b as *mut V;
    let r = self.r;
    if b.is_null() { return; }
    self.s = 63;
    self.a = &raw const EMPTY[0];
    self.b = null();
    self.r = 1;
    if needs_drop::<V>() {
      let n = capacity(s) - r;
      if n != 0 {
        let mut n = n;
        let mut p = a;
        let mut q = b;
        loop {
          if unsafe { p.read() } != u64::MAX {
            unsafe { q.drop_in_place() };
            n = n - 1;
            if n == 0 { break }
          }
          p = p.wrapping_add(1);
          q = q.wrapping_add(1);
        }
      }
    }
    let d = unsafe { (b as *mut u64).offset_from_unsigned(a) };
    // let l = unsafe { Layout::from_size_align_unchecked
    unimplemented!()
  }

  #[inline(always)]
  pub fn values(&self) -> impl ExactSizeIterator<Item = &V> + use<'_, V> {
    Iter {
      n: capacity(self.s) - self.r,
      a: self.a,
      b: self.b as *mut V,
      f: move |_, b| unsafe { &*b }
    }
  }

  #[inline(always)]
  pub fn values_mut(&mut self) -> impl ExactSizeIterator<Item = &mut V> + use<'_, V> {
    Iter {
      n: capacity(self.s) - self.r,
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
    self.internal_num_slots() * (size_of::<u64>() + size_of::<V>())
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
    return self.get(index).unwrap();
  }
}

struct Iter<V, T, F: FnMut(u64, *mut V) -> T> {
  n: usize,
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
    let mut a = self.a;
    let mut b = self.b;
    let mut x;
    loop {
      x = unsafe { a.read() };
      if x != u64::MAX { break }
      a = a.wrapping_add(1);
      b = b.wrapping_add(1);
    }
    self.n = n - 1;
    self.a = a.wrapping_add(1);
    self.b = b.wrapping_add(1);
    Some((self.f)(x, b))
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    return (self.n, Some(self.n));
  }

  #[inline(always)]
  fn fold<U, G: FnMut(U, T) -> U>(self, init: U, g: G) -> U {
    let mut n = self.n;
    let mut a = self.a;
    let mut b = self.b;
    let mut f = self.f;
    let mut u = init;
    let mut g = g;
    if n != 0 {
      loop {
        let x = unsafe { a.read() };
        if x != u64::MAX {
          u = g(u, f(x, b));
          n = n - 1;
          if n == 0 { break }
        }
        a = a.wrapping_add(1);
        b = b.wrapping_add(1);
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
