#![allow(missing_docs)]

extern crate alloc;

use alloc::alloc::Layout;
use alloc::alloc::alloc;
use alloc::alloc::dealloc;
use alloc::alloc::handle_alloc_error;
use core::fmt::Debug;
use core::hint::select_unpredictable;
use core::mem::MaybeUninit;
use core::mem::needs_drop;
use core::mem::offset_of;
use core::num::NonZeroU64;
use core::ops::Index;
use core::ptr::null;
use rand_core::RngCore;

pub struct HashMap<V> {
  z: (u64, u64),
  m: (u64, u64),
  t: *const Slot<V>,
  s: usize,
  u: *const Slot<V>,
  r: usize,
}

struct Slot<V> {
  hash: u64,
  data: MaybeUninit<V>,
}

#[inline(always)]
fn slot_hash<V>(a: *mut Slot<V>) -> *mut u64 {
  a.wrapping_byte_add(offset_of!(Slot<V>, hash)).cast()
}

#[inline(always)]
fn slot_data<V>(a: *mut Slot<V>) -> *mut V {
  a.wrapping_byte_add(offset_of!(Slot<V>, data)).cast()
}

static EMPTY: [u64; 12] = [0u64; 12];

#[inline(always)]
const fn empty<V>() -> *const Slot<V> {
  const { assert!(size_of::<Slot<V>>() <= 32) };
  &EMPTY as *const u64 as *const Slot<V>
}

#[inline(always)]
fn ctz(n: usize) -> usize {
  n.trailing_zeros() as usize
}

#[inline(always)]
const fn allocation_max_num_slots<V>() -> usize {
  isize::MAX as usize / size_of::<Slot<V>>()
}

#[inline(always)]
const fn allocation_size<V>(num_slots: usize) -> usize {
  num_slots * size_of::<Slot<V>>()
}

#[inline(always)]
unsafe fn allocation_layout<V>(num_slots: usize) -> Layout {
  let s = allocation_size::<V>(num_slots);
  let a = align_of::<Slot<V>>();
  unsafe { Layout::from_size_align_unchecked(s, a) }
}

#[inline(always)]
fn capacity(s: usize) -> usize {
  1 << 64 - s - 1
}

#[inline(always)]
fn hash(key: NonZeroU64, m: (u64, u64)) -> u64 {
  let h = key.get();
  let h = h.wrapping_mul(m.0);
  let h = h.swap_bytes();
  let h = h.wrapping_mul(m.1);
  h
}

#[inline(always)]
unsafe fn invert_hash(h: u64, m: (u64, u64)) -> NonZeroU64 {
  let h = h.wrapping_mul(m.0);
  let h = h.swap_bytes();
  let h = h.wrapping_mul(m.1);
  unsafe { NonZeroU64::new_unchecked(h) }
}

#[inline(always)]
fn slot(h: u64, s: usize) -> usize {
  (! h >> s) as usize
}

#[inline(always)]
fn invert_u64(a: u64) -> u64 {
  // https://arxiv.org/abs/2204.04342
  let x = a.wrapping_mul(3) ^ 2;
  let y = 1u64.wrapping_sub(a.wrapping_mul(x));
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  x
}

#[inline(always)]
fn invert_seed(m: (u64, u64)) -> (u64, u64) {
  let a = m.0;
  let b = m.1;
  let c = invert_u64(a.wrapping_mul(b));
  (c.wrapping_mul(a), c.wrapping_mul(b))
}

impl<V> HashMap<V> {
  #[inline(always)]
  fn internal_new(m: (u64, u64)) -> Self {
    Self {
      t: empty::<V>(),
      m: m,
      s: 63,
      r: capacity(63),
      u: null(),
      z: invert_seed(m),
    }
  }

  pub fn new() -> Self {
    let n = dandelion::thread_local::u128();
    let a = (n as u64) | 1;
    let b = ((n >> 64) as u64) | 1;
    Self::internal_new((a, b))
  }

  pub fn new_seeded(rng: &mut impl RngCore) -> Self {
    let a = rng.next_u64() | 1;
    let b = rng.next_u64() | 1;
    Self::internal_new((a, b))
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
    let t = self.t as *mut Slot<V>;
    let m = self.m;
    let s = self.s;
    let h = hash(key, m);
    let k = slot(h, s);
    let b = t.wrapping_add(k);
    let y = unsafe { slot_hash(b).read() };
    let mut a = b;
    let mut x;
    loop {
      a = a.wrapping_add(1);
      x = unsafe { slot_hash(a).read() };
      if ! (x > h) { break }
    }
    let x = select_unpredictable(y > h, x, y);
    x == h
  }

  #[inline(always)]
  pub fn get(&self, key: NonZeroU64) -> Option<&V> {
    let t = self.t as *mut Slot<V>;
    let m = self.m;
    let s = self.s;
    let h = hash(key, m);
    let k = slot(h, s);
    let b = t.wrapping_add(k);
    let y = unsafe { slot_hash(b).read() };
    let mut a = b;
    let mut x;
    loop {
      a = a.wrapping_add(1);
      x = unsafe { slot_hash(a).read() };
      if ! (x > h) { break }
    }
    let a = select_unpredictable(y > h, a, b);
    let x = select_unpredictable(y > h, x, y);
    if x != h {
      None
    } else {
      Some(unsafe { &*slot_data(a) })
    }
  }

  #[inline(always)]
  pub fn get_mut(&mut self, key: NonZeroU64) -> Option<&mut V> {
    let t = self.t as *mut Slot<V>;
    let m = self.m;
    let s = self.s;
    let h = hash(key, m);
    let k = slot(h, s);
    let b = t.wrapping_add(k);
    let y = unsafe { slot_hash(b).read() };
    let mut a = b;
    let mut x;
    loop {
      a = a.wrapping_add(1);
      x = unsafe { slot_hash(a).read() };
      if ! (x > h) { break }
    }
    let a = select_unpredictable(y > h, a, b);
    let x = select_unpredictable(y > h, x, y);
    if x != h {
      None
    } else {
      Some(unsafe { &mut *slot_data(a) })
    }
  }

  #[inline(never)]
  #[cold]
  fn internal_init(&mut self, h: u64, value: V) {
    const { assert!(40 <= allocation_max_num_slots::<V>()) };
    let w = 32;
    let d = 40;
    let s = 64 - ctz(w);
    let l = unsafe { allocation_layout::<V>(d) };
    let t = unsafe { alloc(l) } as *mut Slot<V>;
    if t.is_null() { match handle_alloc_error(l) { } }
    let k = slot(h, s);
    for i in 0 .. d { unsafe { slot_hash(t.wrapping_add(i)).write(0) } }
    unsafe { slot_hash(t.wrapping_add(k)).write(h) };
    unsafe { slot_data(t.wrapping_add(k)).write(value) };
    self.t = t;
    self.s = s;
    self.r = capacity(s) - 1;
    self.u = t.wrapping_add(d);
  }

  #[inline(never)]
  #[cold]
  fn internal_grow(&mut self, last_write: *mut Slot<V>) {
    let old_t = self.t as *mut Slot<V>;
    let old_s = self.s;
    let old_r = self.r.wrapping_add(1);
    let old_u = self.u as *mut Slot<V>;
    let old_c = capacity(old_s);
    let old_d = unsafe { old_u.offset_from_unsigned(old_t) };
    let old_w = 1 << 64 - old_s;
    let old_e = old_d - old_w;
    let old_l = unsafe { allocation_layout::<V>(old_d) };
    // Temporarily place the table in a valid state in case we panic.
    let h = unsafe { slot_hash(last_write).replace(0) };
    self.r = old_r;
    let new_s = if old_r == 0 { old_s - 1 } else { old_s };
    let new_c = capacity(new_s);
    let new_w = 1 << 64 - new_s;
    let new_e = if last_write.wrapping_add(1) == old_u { 2 * old_e } else { old_e };
    let new_d = new_w + new_e;
    // Panic if the layout would overflow.
    assert!(new_d <= allocation_max_num_slots::<V>());
    // Alloc.
    let new_l = unsafe { allocation_layout::<V>(new_d) };
    let new_t = unsafe { alloc(new_l) } as *mut Slot<V>;
    if new_t.is_null() { match handle_alloc_error(new_l) { } }
    // At this point, we're guaranteed to successfully finish growing the
    // table.
    let new_u = new_t.wrapping_add(new_d);
    // We re-add the last write and compute some values that include that slot.
    unsafe { slot_hash(last_write).write(h) };
    let old_n = old_c - old_r + 1;
    let new_r = old_r + (new_c - old_c) - 1;
    // Update struct fields.
    self.t = new_t;
    self.s = new_s;
    self.r = new_r;
    self.u = new_u;
    // Compress non-empty slots.
    let mut a = old_t;
    let mut b = old_t;
    loop {
      let x = unsafe { slot_hash(a).read() };
      let y = unsafe { slot_data(a).cast::<MaybeUninit<V>>().read() };
      unsafe { slot_hash(b).write(x) };
      unsafe { slot_data(b).cast::<MaybeUninit<V>>().write(y) };
      a = a.wrapping_add(1);
      b = b.wrapping_add((x != 0) as usize);
      if a == old_u { break }
    }
    debug_assert!(unsafe { b.offset_from_unsigned(old_t) } == old_n);
    // Initialize new table.
    let mut a = new_u;
    loop {
      a = a.wrapping_sub(1);
      unsafe { slot_hash(a).write(0) };
      if a == new_t { break }
    }
    // Copy slots to new allocated block.
    let mut i = 0;
    let mut j = 0;
    loop {
      let x = unsafe { slot_hash(old_t.wrapping_add(i)).read() };
      let y = unsafe { slot_data(old_t.wrapping_add(i)).read() };
      let k = slot(x, new_s);
      j = select_unpredictable(j > k, j, k);
      unsafe { slot_hash(new_t.wrapping_add(j)).write(x) };
      unsafe { slot_data(new_t.wrapping_add(j)).write(y) };
      i = i + 1;
      j = j + 1;
      if i == old_n { break }
    }
    // The map is now in a valid state, even if deallocating panics.
    unsafe { dealloc(old_t as *mut u8, old_l) }
  }

  /*
  #[inline(never)]
  #[cold]
  fn internal_grow2(&mut self, last_write: *mut Slot<V>) {
    let old_t = self.t as *mut Slot<V>;
    let old_s = self.s;
    let old_r = self.r.wrapping_add(1);
    let old_u = self.u as *mut Slot<V>;
    let old_c = capacity(old_s);
    let old_d = unsafe { old_u.offset_from_unsigned(old_t) };
    let old_w = 1 << 64 - old_s;
    let old_e = old_d - old_w;
    let old_l = unsafe { allocation_layout::<V>(old_d) };
    // Temporarily place the table in a valid state in case we panic.
    let h = unsafe { slot_hash(last_write).replace(0) };
    self.r = old_r;
    let new_s = old_s - 1;
    let new_c = capacity(new_s);
    let new_w = 1 << 64 - new_s;
    let new_e = if last_write.wrapping_add(1) == old_u { 2 * old_e } else { old_e };
    let new_d = new_w + new_e;
    // Panic if the layout would overflow.
    assert!(new_d <= allocation_max_num_slots::<V>());
    // Alloc.
    let new_l = unsafe { allocation_layout::<V>(new_d) };
    let new_t = unsafe { alloc(new_l) } as *mut Slot<V>;
    if new_t.is_null() { match handle_alloc_error(new_l) { } }
    // At this point, we're guaranteed to successfully finish growing the
    // table.
    let new_u = new_t.wrapping_add(new_d);
    // Update struct fields.
    self.t = new_t;
    self.s = new_s;
    self.r = old_r + (new_c - old_c) - 1; // includes removed value
    self.u = new_u;
    // ???
    let mut i = 0;
    let mut j = 0;
    loop {
      let x = unsafe { slot_hash(old_t.wrapping_add(j)).read() };
      let y = unsafe { slot_data(old_t.wrapping_add(j)).cast_uninit().read() };
      let k = 2 * i;
      let p = select_unpredictable(slot(x, new_s) <= k && x != 0, u64::MAX, 0);
      unsafe { slot_hash(new_t.wrapping_add(k)).write(x & p) };
      unsafe { slot_data(new_t.wrapping_add(k)).cast_uninit().write(y) };
      j = j.wrapping_sub(p as i64 as isize as usize);
      let x = unsafe { slot_hash(old_t.wrapping_add(j)).read() };
      let y = unsafe { slot_data(old_t.wrapping_add(j)).cast_uninit().read() };
      let k = 2 * i + 1;
      let p = select_unpredictable(slot(x, new_s) <= k && x != 0, u64::MAX, 0);
      let q = select_unpredictable(i == j, u64::MAX, p);
      unsafe { slot_hash(new_t.wrapping_add(k)).write(x & p) };
      unsafe { slot_data(new_t.wrapping_add(k)).cast_uninit().write(y) };
      j = j.wrapping_sub(q as i64 as isize as usize);
      i = i + 1;
      if i == old_w { break }
    }
    // ???
    let mut k = new_w;
    loop {
      let x = unsafe { slot_hash(old_t.wrapping_add(j)).read() };
      let y = unsafe { slot_data(old_t.wrapping_add(j)).cast_uninit().read() };
      let p = select_unpredictable(x != 0, u64::MAX, 0);
      unsafe { slot_hash(new_t.wrapping_add(k)).write(x & p) };
      unsafe { slot_data(new_t.wrapping_add(k)).cast_uninit().write(y) };
      j = j.wrapping_sub(p as i64 as isize as usize);
      k = k + 1;
      if k == new_d { break };
    }
    // ???
    let mut k = slot(h, new_s);
    while unsafe { slot_hash(new_t.wrapping_add(k)).read() } != 0 {
      k = k + 1;
    }
    unsafe { slot_hash(new_t.wrapping_add(k)).write(h) };
    unsafe { slot_data(new_t.wrapping_add(k)).write(slot_data(last_write).read()) };
    // The map is now in a valid state, even if deallocating panics.
    unsafe { dealloc(old_t as *mut u8, old_l) }
  }
  */

  #[inline(always)]
  pub fn insert(&mut self, key: NonZeroU64, value: V) -> Option<V> {
    let t = self.t as *mut Slot<V>;
    let m = self.m;
    let s = self.s;
    let r = self.r;
    let u = self.u as *mut Slot<V>;
    let h = hash(key, m);
    let k = slot(h, s);
    let b = t.wrapping_add(k);
    let y = unsafe { slot_hash(b).read() };
    let mut a = b;
    let mut x;
    loop {
      a = a.wrapping_add(1);
      x = unsafe { slot_hash(a).read() };
      if ! (x > h) { break }
    }
    let a = select_unpredictable(y > h, a, b);
    let x = select_unpredictable(y > h, x, y);
    if x == h {
      Some(unsafe { slot_data(b).replace(value) })
    } else {
      if u.is_null() {
        self.internal_init(h, value);
      } else {
        self.r = r.wrapping_sub(1);
        let mut a = a;
        let mut x = x;
        let mut y = value;
        unsafe { slot_hash(a).write(h) };
        while x != 0 {
          y = unsafe { slot_data(a).replace(y) };
          a = a.wrapping_add(1);
          x = unsafe { slot_hash(a).replace(x) };
        }
        unsafe { slot_data(a).write(y) };
        if r == 0 || a.wrapping_add(1) == u {
          self.internal_grow(a);
        }
      }
      None
    }
  }

  #[inline(always)]
  pub fn remove(&mut self, key: NonZeroU64) -> Option<V> {
    let t = self.t as *mut Slot<V>;
    let m = self.m;
    let s = self.s;
    let r = self.r;
    let h = hash(key, m);
    let k = slot(h, s);
    let y = unsafe { slot_hash(t.wrapping_add(k)).read() };
    let mut i = k;
    let mut x;
    loop {
      i = i + 1;
      x = unsafe { slot_hash(t.wrapping_add(i)).read() };
      if ! (x > h) { break }
    }
    let i = select_unpredictable(y > h, i, k);
    let x = select_unpredictable(y > h, x, y);
    if x != h {
      None
    } else {
      self.r = r + 1;
      let value = unsafe { slot_data(t.wrapping_add(i)).read() };
      let mut i = i;
      loop {
        let x = unsafe { slot_hash(t.wrapping_add(i + 1)).read() };
        if ! (slot(x, s) <= i && /* likely */ x != 0) { break }
        let y = unsafe { slot_data(t.wrapping_add(i + 1)).read() };
        unsafe { slot_hash(t.wrapping_add(i)).write(x) };
        unsafe { slot_data(t.wrapping_add(i)).write(y) };
        i = i + 1;
      }
      unsafe { slot_hash(t.wrapping_add(i)).write(0) };
      Some(value)
    }
  }

  pub fn clear(&mut self) {
    let t = self.t as *mut Slot<V>;
    let s = self.s;
    let r = self.r;
    let u = self.u as *mut Slot<V>;
    if u.is_null() { return }
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
        let mut a = u;
        loop {
          a = a.wrapping_sub(1);
          if unsafe { slot_hash(a).read() } != 0 {
            unsafe { slot_hash(a).write(0) };
            r = r + 1;
            self.r = r;
            unsafe { slot_data(a).drop_in_place() };
            n = n - 1;
            if n == 0 { break }
          }
        }
      }
    } else {
      if n != 0 {
        self.r = c;
        let mut a = u;
        loop {
          a = a.wrapping_sub(1);
          unsafe { slot_hash(a).write(0) };
          if a == t { break }
        }
      }
    }
  }

  pub fn reset(&mut self) {
    let t = self.t as *mut Slot<V>;
    let s = self.s;
    let r = self.r;
    let u = self.u as *mut Slot<V>;
    if u.is_null() { return }
    let n = capacity(s) - r;
    let d = unsafe { u.offset_from_unsigned(t) };
    self.t = empty::<V>();
    self.s = 63;
    self.r = capacity(63);
    self.u = null();
    if needs_drop::<V>() {
      if n != 0 {
        let mut n = n;
        let mut a = u;
        loop {
          a = a.wrapping_sub(1);
          if unsafe { slot_hash(a).read() } != 0 {
            unsafe { slot_data(a).drop_in_place() };
            n = n - 1;
            if n == 0 { break }
          }
        }
      }
    }
    unsafe { dealloc(t as *mut u8, allocation_layout::<V>(d)) };
  }

  #[inline(always)]
  pub fn iter(&self) -> impl ExactSizeIterator<Item = (NonZeroU64, &V)> + use<'_, V> {
    let z = self.z;
    Iter {
      n: capacity(self.s) - self.r,
      a: self.u as *mut Slot<V>,
      f: move |x, a| unsafe { (invert_hash(x, z), &*slot_data(a)) }
    }
  }

  #[inline(always)]
  pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = (NonZeroU64, &mut V)> + use<'_, V> {
    let z = self.z;
    Iter {
      n: capacity(self.s) - self.r,
      a: self.u as *mut Slot<V>,
      f: move |x, a| unsafe { (invert_hash(x, z), &mut *slot_data(a)) }
    }
  }

  #[inline(always)]
  pub fn keys(&self) -> impl ExactSizeIterator<Item = NonZeroU64> + use<'_, V> {
    let z = self.z;
    Iter {
      n: capacity(self.s) - self.r,
      a: self.u as *mut Slot<V>,
      f: move |x, _| unsafe { invert_hash(x, z) }
    }
  }

  #[inline(always)]
  pub fn values(&self) -> impl ExactSizeIterator<Item = &V> + use<'_, V> {
    Iter {
      n: capacity(self.s) - self.r,
      a: self.u as *mut Slot<V>,
      f: move |_, a| unsafe { &*slot_data(a) }
    }
  }

  #[inline(always)]
  pub fn values_mut(&mut self) -> impl ExactSizeIterator<Item = &mut V> + use<'_, V> {
    Iter {
      n: capacity(self.s) - self.r,
      a: self.u as *mut Slot<V>,
      f: move |_, a| unsafe { &mut *slot_data(a) }
    }
  }

  fn internal_num_slots(&self) -> usize {
    let t = self.t;
    let u = self.u;
    if u.is_null() { return 0 }
    unsafe { u.offset_from_unsigned(t) }
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

struct Iter<V, T, F: FnMut(u64, *mut Slot<V>) -> T> {
  n: usize,
  a: *mut Slot<V>,
  f: F,
}

impl<V, T, F: FnMut(u64, *mut Slot<V>) -> T> Iterator for Iter<V, T, F> {
  type Item = T;

  #[inline(always)]
  fn next(&mut self) -> Option<Self::Item> {
    let n = self.n;
    if n == 0 { return None }
    let mut a = self.a;
    let mut x;
    loop {
      a = a.wrapping_sub(1);
      x = unsafe { slot_hash(a).read() };
      if x != 0 { break }
    }
    self.n = n - 1;
    self.a = a;
    Some((self.f)(x, a))
  }

  #[inline(always)]
  fn size_hint(&self) -> (usize, Option<usize>) {
    (self.n, Some(self.n))
  }

  #[inline(always)]
  fn fold<U, G: FnMut(U, T) -> U>(self, init: U, g: G) -> U {
    let mut n = self.n;
    let mut a = self.a;
    let mut f = self.f;
    let mut u = init;
    let mut g = g;
    if n != 0 {
      loop {
        a = a.wrapping_sub(1);
        let x = unsafe { slot_hash(a).read() };
        if x != 0 {
          u = g(u, f(x, a));
          n = n - 1;
          if n == 0 { break }
        }
      }
    }
    u
  }
}

impl<V, T, F: FnMut(u64, *mut Slot<V>) -> T> ExactSizeIterator for Iter<V, T, F> {
  #[inline(always)]
  fn len(&self) -> usize {
    self.n
  }
}

impl<V: Clone> Clone for HashMap<V> {
  fn clone(&self) -> Self {
    let mut t = Self::new();
    self.iter().for_each(|(x, y)| { let _ = t.insert(x, y.clone()); });
    t
  }
}

impl <V: Debug> Debug for HashMap<V> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut a = self.iter().collect::<Box<[(NonZeroU64, &V)]>>();
    a.sort_by_key(|&(x, _)| x);
    f.debug_map().entries(a).finish()
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
    t.internal_num_slots()
  }

  pub fn allocation_size<V>(t: &HashMap<V>) -> usize {
    t.internal_allocation_size()
  }

  pub fn load_factor<V>(t: &HashMap<V>) -> f64 {
    t.internal_load_factor()
  }
}

pub fn contains_key(t: &HashMap<u32>, key: NonZeroU64) -> bool {
  t.contains_key(key)
}

pub fn get(t: &HashMap<u32>, key: NonZeroU64) -> Option<&u32> {
  t.get(key)
}

pub fn get_value(t: &HashMap<u32>, key: NonZeroU64) -> Option<u32> {
  match t.get(key) { None => None, Some(&y) => Some(y) }
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

pub fn clone(t: &mut HashMap<u32>) -> HashMap<u32> {
  t.clone()
}
