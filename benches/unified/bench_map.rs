use std::num::NonZeroU32;
use divan::Bencher;
use divan::black_box;
use crate::util::Map;

const ARGS: &'static [usize] = &[
  1_000,
  3_000,
  10_000,
  30_000,
  100_000,
  300_000,
  // 1_000_000,
];

const SAMPLE_COUNT: u32 = 9;

fn sizes_from_working_set(working_set: usize) -> [usize; 10] {
  let n: [usize; 10] = [
    50,
    54,
    57,
    62,
    66,
    71,
    76,
    81,
    87,
    93,
  ];
  let mut a = 0;
  for &n in &n { a += n; }
  let mut r = [0; 10];
  let mut b = 0;
  for i in 0 .. 9 { r[i] = n[i] * working_set / a; b += r[i]; }
  r[9] = working_set - b;
  r
}

struct KeyGen(u32);

impl KeyGen {
  fn new() -> Self {
    KeyGen(1)
  }

  fn next(&mut self) -> NonZeroU32 {
    let x = self.0;
    self.0 = x.wrapping_mul(5);
    unsafe { NonZeroU32::new_unchecked(x ^ x >> 16) }
  }

  fn peek(&mut self) -> NonZeroU32 {
    let x = self.0;
    unsafe { NonZeroU32::new_unchecked(x ^ x >> 16) }
  }
}

/*
struct KeyGen(u32);

impl KeyGen {
  fn new() -> Self {
    KeyGen(1)
  }

  fn next(&mut self) -> NonZeroU32 {
    let x = self.0;
    self.0 = x.wrapping_add(2);
    unsafe { NonZeroU32::new_unchecked(core::arch::aarch64::__crc32cw(0, x)) }
  }

  fn peek(&mut self) -> NonZeroU32 {
    let x = self.0;
    unsafe { NonZeroU32::new_unchecked(core::arch::aarch64::__crc32cw(0, x)) }
  }
}
*/

/*
struct KeyGen(NonZeroU64);

impl KeyGen {
  fn new() -> Self {
    KeyGen(unsafe { NonZeroU64::new_unchecked(0xcafe_babe_cafe_babe) })
  }

  fn next(&mut self) -> NonZeroU64 {
    let x = self.0;
    let y = x.get();
    let y = y ^ y << 9;
    let y = y ^ y >> 7;
    self.0 = unsafe { NonZeroU64::new_unchecked(y) };
    x
  }

  fn peek(&mut self) -> NonZeroU64 {
    self.0
  }
}
*/

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    foldhash::HashMap<NonZeroU32, NonZeroU32>,
    tangerine::map::HashMap<NonZeroU32, NonZeroU32>,
    tangerine::old_map::HashMap<NonZeroU32, NonZeroU32>,
    tangerine::two::HashMap<NonZeroU32, NonZeroU32>,
  ])]
#[inline(never)]
fn bench_get_chained<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut g = KeyGen::new();
      for _ in 0 .. m { let _ = t.insert(g.next(), g.peek()); }
      (t, KeyGen::new().peek())
    });
  bencher.bench_local(|| {
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut k) in &mut t {
        for _ in 0 .. 500 {
          match t.get(*k) {
            None => { *k = KeyGen::new().peek(); }
            Some(&y) => { *k = y; }
          }
        }
      }
    }
  });
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    foldhash::HashMap<NonZeroU32, usize>,
    tangerine::map::HashMap<NonZeroU32, usize>,
    tangerine::old_map::HashMap<NonZeroU32, usize>,
    tangerine::two::HashMap<NonZeroU32, usize>,
  ])]
#[inline(never)]
fn bench_get_unchained<T: Map<usize>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut g = KeyGen::new();
      for i in 0 .. m { let _ = t.insert(g.next(), i); }
      (t, KeyGen::new())
    });
  bencher.bench_local(|| {
    let mut z = 0usize;
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut g) in &mut t {
        for _ in 0 .. 500 {
          match t.get(g.next()) {
            None => { *g = KeyGen::new(); }
            Some(&y) => { z = z.wrapping_add(y); }
          }
        }
      }
    }
    black_box(z)
  });
}

#[divan::bench(
  sample_count = SAMPLE_COUNT,
  args = [1_000, 10_000, 100_000, 1_000_000, 10_000_000],
  types = [
    foldhash::HashMap<NonZeroU32, usize>,
    tangerine::map::HashMap<NonZeroU32, usize>,
    tangerine::old_map::HashMap<NonZeroU32, usize>,
    tangerine::two::HashMap<NonZeroU32, usize>,
  ])]
#[inline(never)]
fn bench_insert<T: Map<usize>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] = sizes.map(|n| (T::new(), n));
  let mut g = KeyGen::new();
  bencher.bench_local(|| {
    for _ in 0 .. 200 {
      for &mut (ref mut t, n) in &mut t {
        let mut k = t.len();
        for i in 0 .. 500 {
          if k == n { k = 0; *t = T::new(); }
          let _ = t.insert(g.next(), i);
          k = k + 1;
        }
      }
    }
  });
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    foldhash::HashMap<NonZeroU32, usize>,
    tangerine::map::HashMap<NonZeroU32, usize>,
    tangerine::old_map::HashMap<NonZeroU32, usize>,
    tangerine::two::HashMap<NonZeroU32, usize>,
  ])]
#[inline(never)]
fn bench_remove_insert<T: Map<usize>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut g = KeyGen::new();
      for i in 0 .. m { let _ = t.insert(g.next(), i); }
      (t, KeyGen::new(), g)
    });
  bencher.bench_local(|| {
    let mut z = 0usize;
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut a, ref mut b) in &mut t {
        for i in 0 .. 250 {
          if let Some(y) = t.remove(a.next()) { z = z.wrapping_add(y); }
          let _ = t.insert(b.next(), i);
        }
      }
    }
    black_box(z)
  });
}
