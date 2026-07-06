//! unified benchmarks

mod maps;

use crate::maps::Map;
use divan::Bencher;
use std::hint::black_box;
use std::num::NonZeroU8;
use std::num::NonZeroU32;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
  divan::main();
}

const ARGS: &'static [usize] = &[
  1_000,
  3_000,
  10_000,
  30_000,
  100_000,
  300_000,
  1_000_000,
  3_000_000,
  10_000_000,
];

const SAMPLE_COUNT: u32 = 9;

fn sizes_from_working_set(working_set: usize) -> [usize; 10] {
  let n: [usize; 10] = [
    500,
    535,
    574,
    615,
    659,
    707,
    757,
    812,
    870,
    933,
  ];
  let mut a = 0;
  for &n in &n { a += n; }
  let mut r = [0; 10];
  let mut b = 0;
  for i in 0 .. 9 { r[i] = n[i] * working_set / a; b += r[i]; }
  r[9] = working_set - b;
  r
}

#[derive(Clone)]
struct KeyGen {
  state: u32,
}

impl KeyGen {
  const fn new() -> Self {
    Self { state: 1 }
  }

  fn peek(&self) -> NonZeroU32 {
    let s = self.state;
    unsafe { NonZeroU32::new_unchecked(s) }
  }

  fn next(&mut self) -> NonZeroU32 {
    let s = self.state;
    self.state = s.wrapping_mul(5);
    unsafe { NonZeroU32::new_unchecked(s) }
  }
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    std::collections::HashMap<NonZeroU32, u32, foldhash::fast::RandomState>,
    intmap::IntMap<NonZeroU32, u32>,
    tangerine::map::IntMap<NonZeroU32, u32>,
  ])]
fn bench_lookup_throughput<T: Map<NonZeroU32, u32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32, u32>>(t: &mut [(T, KeyGen)]) -> u32 {
    let mut z = 0u32;
    for _ in 0 .. 500 {
      for &mut (ref mut t, ref mut a) in t.iter_mut() {
        for _ in 0 .. 200 {
          match t.get(a.next()) {
            None => { *a = KeyGen::new(); }
            Some(&y) => { z ^= y; }
          }
        }
      }
    }
    z
  }
  let sizes = sizes_from_working_set(working_set);
  let mut t =
    sizes.map(|m| {
      let mut t = T::new();
      let mut a = KeyGen::new();
      for _ in 0 .. m {
        let _ = t.insert(a.next(), a.peek().get());
      }
      (t, KeyGen::new())
    });
  bencher.bench_local(|| go(black_box(&mut t)));
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    std::collections::HashMap<NonZeroU32, NonZeroU32, foldhash::fast::RandomState>,
    intmap::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
  ])]
fn bench_lookup_latency<T: Map<NonZeroU32, NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32, NonZeroU32>>(t: &mut [(T, NonZeroU32)]) {
    for _ in 0 .. 500 {
      for &mut (ref mut t, ref mut a) in t.iter_mut() {
        for _ in 0 .. 200 {
          if let Some(&y) = t.get(*a) { *a = y; }
        }
      }
    }
  }
  let sizes = sizes_from_working_set(working_set);
  let mut t =
    sizes.map(|m| {
      let mut t = T::new();
      let mut a = KeyGen::new();
      for i in 0 .. m {
        if i == m - 1 {
          let _ = t.insert(a.next(), NonZeroU32::MIN);
        } else {
          let _ = t.insert(a.next(), a.peek());
        }
      }
      (t, NonZeroU32::MIN)
    });
  bencher.bench_local(|| go(black_box(&mut t)));
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    std::collections::HashMap<NonZeroU32, NonZeroU32, foldhash::fast::RandomState>,
    intmap::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
  ])]
fn bench_lookup_mixed<T: Map<NonZeroU32, NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32, NonZeroU32>>(t: &mut [(T, NonZeroU32, NonZeroU32)]) {
    for _ in 0 .. 500 {
      for &mut (ref mut t, ref mut a, ref mut b) in t.iter_mut() {
        for _ in 0 .. 100 {
          if let Some(&y) = t.get(*a) { *a = y; }
          if let Some(&y) = t.get(*b) { *b = y; }
        }
      }
    }
  }
  let sizes = sizes_from_working_set(working_set);
  let mut t =
    sizes.map(|m| {
      let mut t = T::new();
      let mut a = KeyGen::new();
      for i in 0 .. m {
        if i == m - 1 {
          let _ = t.insert(a.next(), NonZeroU32::MIN);
        } else {
          let _ = t.insert(a.next(), a.peek());
        }
      }
      let mut b = KeyGen::new();
      for _ in 0 .. m / 2 { let _ = b.next(); }
      (t, NonZeroU32::MIN, b.peek())
    });
  bencher.bench_local(|| go(black_box(&mut t)));
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    std::collections::HashMap<NonZeroU32, u32, foldhash::fast::RandomState>,
    intmap::IntMap<NonZeroU32, u32>,
    tangerine::map::IntMap<NonZeroU32, u32>,
  ])]
fn bench_insert<T: Map<NonZeroU32, u32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32, u32>>(t: &mut [(T, KeyGen, usize, usize)]) {
    for _ in 0 .. 500 {
      for &mut (ref mut t, ref mut a, ref mut n, limit) in t.iter_mut() {
        for _ in 0 .. 200 {
          if *n == limit {
            *t = T::new();
            *n = 0;
          }
          let _ = t.insert(a.next(), a.peek().get());
          *n = *n + 1;
        }
      }
    }
  }
  let sizes = sizes_from_working_set(working_set);
  let mut t =
    sizes.map(|m| {
      let mut t = T::new();
      let mut a = KeyGen::new();
      for _ in 0 .. m.saturating_sub(100_000) {
        let _ = t.insert(a.next(), a.peek().get());
      }
      let n = t.len();
      (t, a, n, m)
    });
  bencher.bench_local(|| go(black_box(&mut t)));
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    std::collections::HashMap<NonZeroU32, NonZeroU32, foldhash::fast::RandomState>,
    intmap::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
  ])]
fn bench_update<T: Map<NonZeroU32, NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32, NonZeroU32>>(t: &mut [(T, KeyGen, KeyGen)]) {
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut a, ref mut b) in t.iter_mut() {
        for _ in 0 .. 250 {
          if let Some(y) = t.remove(a.next()) {
            let _ = t.insert(y, b.next());
          }
        }
      }
    }
  }
  let sizes = sizes_from_working_set(working_set);
  let mut t =
    sizes.map(|m| {
      let mut t = T::new();
      let mut a = KeyGen::new();
      let mut b = KeyGen::new();
      for _ in 0 .. m {
        let _ = a.next();
      }
      for _ in 0 .. m {
        let _ = t.insert(b.next(), a.next());
      }
      (t, KeyGen::new(), a)
    });
  bencher.bench_local(|| go(black_box(&mut t)));
}

#[divan::bench(
  sample_count = SAMPLE_COUNT,
  types = [
    std::collections::HashMap<NonZeroU32, u32, foldhash::fast::RandomState>,
    intmap::IntMap<NonZeroU32, u32>,
    tangerine::map::IntMap<NonZeroU32, u32>,
  ])]
fn bench_iter_value<T: Map<NonZeroU32, u32>>(bencher: Bencher<'_, '_>) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32, u32>>(t: &mut T) -> u32 {
    let mut z = 0;
    t.for_each_value(|&x| { z ^= x; });
    z
  }
  let mut t = T::new();
  let mut k = KeyGen::new();
  for _ in 0 .. 1_000_000 { let _ = t.insert(k.next(), k.peek().get()); }
  bencher.bench_local(|| go(black_box(&mut t)));
}

#[divan::bench(
  sample_count = SAMPLE_COUNT,
  types = [
    std::collections::HashMap<NonZeroU8, (), foldhash::fast::RandomState>,
    intmap::IntMap<NonZeroU8, ()>,
    tangerine::map::IntMap<NonZeroU8, ()>,
  ])]
fn bench_insert_u8x255<T: Map<NonZeroU8, ()>>(bencher: Bencher<'_, '_>) {
  #[inline(never)]
  fn go<T: Map<NonZeroU8, ()>>(t: &mut T) {
    let mut i = 0;
    'done: loop {
      for k in NonZeroU8::MIN ..= NonZeroU8::MAX {
        let _ = t.insert(k, ());
        i += 1;
        if i == 1_000_000 { break 'done }
      }
      *t = T::new();
    }
  }
  let mut t = T::new();
  bencher.bench_local(|| go(black_box(&mut t)));
}
