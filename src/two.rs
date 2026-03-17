#![allow(missing_docs)]

use rand_core::RngCore;
use std::hint::select_unpredictable;
use std::mem::needs_drop;
use std::num::NonZeroU64;
use std::ops::Index;
use std::ptr::null;

pub struct HashMap<V> {
  mult: u64,
  lshr: u32,
  room: usize,
  hash: *const u64,
  data: *const V,
}

static EMPTY: [u64; 3] = [u64::MAX; 3];

#[inline(always)]
fn capacity(s: u32) -> usize {
  1 << 64 - s - 1
}

#[inline(always)]
fn slot(x: u64, s: u32) -> usize {
  x.wrapping_shr(s) as usize
}

impl<V> HashMap<V> {
  #[inline(always)]
  fn internal_new(m: u64) -> Self {
    Self {
      mult: m | 1,
      lshr: 63,
      room: 1,
      hash: &EMPTY[0] as *const _,
      data: null(),
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
    let s = self.lshr;
    let r = self.room;

    capacity(s) - r
  }

  #[inline(always)]
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  #[inline(always)]
  pub fn contains_key(&self, key: NonZeroU64) -> bool {
    let m = self.mult;
    let s = self.lshr;
    let a = self.hash;
    let h = key.get().wrapping_mul(m).wrapping_sub(1);
    let k = slot(h, s);
    let u = unsafe { a.add(k).read() };
    let v = unsafe { a.add(k).add(1).read() };
    let mut i;
    let mut x = select_unpredictable(u < h, v, u);
    if v < h {
      i = k + 1;
      loop {
        i = i + 1;
        x = unsafe { a.add(i).read() };
        if ! (x < h) { break; }
      }
    }
    x == h
  }

  #[inline(always)]
  pub fn get(&self, key: NonZeroU64) -> Option<&V> {
    let m = self.mult;
    let s = self.lshr;
    let a = self.hash;
    let b = self.data;
    let h = key.get().wrapping_mul(m).wrapping_sub(1);
    let k = slot(h, s);
    let u = unsafe { a.add(k).read() };
    let v = unsafe { a.add(k).add(1).read() };
    let mut i = select_unpredictable(u < h, k + 1, k);
    let mut x = select_unpredictable(u < h, v, u);
    if v < h {
      i = k + 1;
      loop {
        i = i + 1;
        x = unsafe { a.add(i).read() };
        if ! (x < h) { break; }
      }
    }
    if x != h {
      None
    } else {
      Some(unsafe { &*b.add(i) })
    }
  }

  #[inline(always)]
  pub fn get_mut(&mut self, key: NonZeroU64) -> Option<&mut V> {
    let m = self.mult;
    let s = self.lshr;
    let a = self.hash;
    let b = self.data as *mut V;
    let h = key.get().wrapping_mul(m).wrapping_sub(1);
    let k = slot(h, s);
    let u = unsafe { a.add(k).read() };
    let v = unsafe { a.add(k).add(1).read() };
    let mut i = select_unpredictable(u < h, k + 1, k);
    let mut x = select_unpredictable(u < h, v, u);
    if v < h {
      i = k + 1;
      loop {
        i = i + 1;
        x = unsafe { a.add(i).read() };
        if ! (x < h) { break; }
      }
    }
    if x != h {
      None
    } else {
      Some(unsafe { &mut *b.add(i) })
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
    let m = self.mult;
    let s = self.lshr;
    let a = self.hash as *mut u64;
    let b = self.data as *mut V;
    let h = key.get().wrapping_mul(m).wrapping_sub(1);
    let k = slot(h, s);
    let u = unsafe { a.add(k).read() };
    let v = unsafe { a.add(k).add(1).read() };
    let mut i = select_unpredictable(u < h, k + 1, k);
    let mut x = select_unpredictable(u < h, v, u);
    if v < h {
      i = k + 1;
      loop {
        i = i + 1;
        x = unsafe { a.add(i).read() };
        if ! (x < h) { break; }
      }
    }
    if x == h {
      Some(unsafe { b.add(i).replace(value) })
    } else {
      if b.is_null() {
        self.internal_init(h, value);
      } else {
        let r = self.room;
        self.room = r.wrapping_sub(1);
        let mut y = value;
        unsafe { a.add(i).write(h) };
        while x != u64::MAX {
          y = unsafe { b.add(i).replace(y) };
          i = i + 1;
          x = unsafe { a.add(i).replace(x) };
        }
        unsafe { b.add(i).write(y) };
        if r == 0 || unsafe { a.add(i).add(1) } == b as *mut u64 {
          self.internal_grow(i);
        }
      }
      None
    }
  }

  #[inline(always)]
  pub fn remove(&mut self, key: NonZeroU64) -> Option<V> {
    let m = self.mult;
    let s = self.lshr;
    let a = self.hash as *mut u64;
    let b = self.data as *mut V;
    let r = self.room;
    let h = key.get().wrapping_mul(m).wrapping_sub(1);
    let k = slot(h, s);
    let u = unsafe { a.add(k).read() };
    let v = unsafe { a.add(k).add(1).read() };
    let mut i = select_unpredictable(u < h, k + 1, k);
    let mut x = select_unpredictable(u < h, v, u);
    if v < h {
      i = k + 1;
      loop {
        i = i + 1;
        x = unsafe { a.add(i).read() };
        if ! (x < h) { break; }
      }
    }
    if x != h {
      None
    } else {
      self.room = r + 1;
      let value = unsafe { b.add(i).read() };
      let mut x = unsafe { a.add(i).add(1).read() };
      while slot(x, s) <= i && /* likely */ x != u64::MAX {
        unsafe { a.add(i).write(x) };
        unsafe { b.add(i).write(b.add(i).add(1).read()) };
        i = i + 1;
        x = unsafe { a.add(i).add(1).read() };
      }
      unsafe { a.add(i).write(u64::MAX) };
      Some(value)
    }
  }

  pub fn clear(&mut self) {
    let s = self.lshr;
    let r = self.room;
    let a = self.hash as *mut u64;
    let b = self.data as *mut V;
    let c = capacity(s);
    let d = unsafe { (b as *mut u64).offset_from_unsigned(a) };
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
        // Also, we update `self.room` as we go instead of once at the end.
        let mut n = n;
        let mut r = r;
        let mut i = d - 1;
        loop {
          if unsafe { a.add(i).read() } != u64::MAX {
            unsafe { a.add(i).write(u64::MAX) };
            r = r + 1;
            self.room = r;
            unsafe { b.add(i).drop_in_place() };
            n = n - 1;
            if n == 0 { break; }
          }
          i = i - 1;
        }
      }
    } else {
      if n != 0 {
        for i in 0 .. d {
          // TODO: unroll?
          // TODO: no memset
          unsafe { a.add(i).write(u64::MAX) };
        }
        self.room = c;
      }
    }
  }

  pub fn reset(&mut self) {
    let s = self.lshr;
    let r = self.room;
    let a = self.hash;
    let b = self.data;
    if b.is_null() { return; }
    self.lshr = 63;
    self.room = 1;
    self.hash = &EMPTY[0] as *const _;
    self.data = null();
    if needs_drop::<V>() {
      unimplemented!()
    }
    unimplemented!()
  }

  fn internal_num_slots(&self) -> usize {
    let a = self.hash;
    let b = self.data;
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
