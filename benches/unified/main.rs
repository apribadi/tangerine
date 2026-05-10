//! unified benchmarks

mod maps;

// use crate::maps::BranchyIntMap;
use crate::maps::BranchyNewMap;
use crate::maps::Map;
use divan::Bencher;
use std::hint::black_box;
use std::num::NonZeroU32;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
  divan::main();
}

const ARGS: &'static [usize] = &[
  100,
  300,
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

struct KeyGen {
  state: NonZeroU32,
}

impl KeyGen {
  const fn new() -> Self {
    Self { state: NonZeroU32::MIN }
  }

  fn peek(&self) -> NonZeroU32 {
    self.state
  }

  fn next(&mut self) -> NonZeroU32 {
    let s = self.state;
    let x = s.get().wrapping_mul(5);
    self.state = unsafe { NonZeroU32::new_unchecked(x) };
    s
  }

  fn reset(&mut self) {
    self.state = NonZeroU32::MIN;
  }
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    // ahash::AHashMap<NonZeroU32, NonZeroU32>,
    foldhash::HashMap<NonZeroU32, NonZeroU32>,
    // tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::new::NewMap<NonZeroU32, NonZeroU32>,
    // BranchyIntMap<NonZeroU32>,
    BranchyNewMap<NonZeroU32>,
  ])]
fn bench_get_chained<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32>>(t: &mut [(T, NonZeroU32)]) {
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut k) in t.iter_mut() {
        for _ in 0 .. 500 {
          match t.get(*k) {
            None => { *k = NonZeroU32::MIN; }
            Some(&y) => { *k = y; }
          }
        }
      }
    }
  }
  let sizes = sizes_from_working_set(working_set);
  let mut t =
    sizes.map(|m| {
      let mut t = T::new();
      let mut k = KeyGen::new();
      for _ in 0 .. m {
        let _ = t.insert(k.next(), k.peek());
      }
      (t, NonZeroU32::MIN)
    });
  bencher.bench_local(|| go(black_box(&mut t)));
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    // ahash::AHashMap<NonZeroU32, NonZeroU32>,
    foldhash::HashMap<NonZeroU32, NonZeroU32>,
    // tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::new::NewMap<NonZeroU32, NonZeroU32>,
    // BranchyIntMap<NonZeroU32>,
    BranchyNewMap<NonZeroU32>,
  ])]
fn bench_get_unchained<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32>>(t: &mut [(T, KeyGen)]) -> u32 {
    let mut z = 0;
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut k) in t.iter_mut() {
        for _ in 0 .. 500 {
          match t.get(k.next()) {
            None => { k.reset(); }
            Some(&y) => { z ^= y.get(); }
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
      let mut k = KeyGen::new();
      for _ in 0 .. m {
        let _ = t.insert(k.next(), k.peek());
      }
      (t, KeyGen::new())
    });
  bencher.bench_local(|| go(black_box(&mut t)));
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    // ahash::AHashMap<NonZeroU32, NonZeroU32>,
    foldhash::HashMap<NonZeroU32, NonZeroU32>,
    // tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::new::NewMap<NonZeroU32, NonZeroU32>,
  ])]
fn bench_insert<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32>>(t: &mut [(T, KeyGen, usize, usize)]) {
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut k, ref mut n, limit) in t.iter_mut() {
        for _ in 0 .. 500 {
          if *n == limit {
            *t = T::new();
            *n = 0;
          }
          let _ = t.insert(k.next(), NonZeroU32::MIN);
          *n = *n + 1;
        }
      }
    }
  }
  let sizes = sizes_from_working_set(working_set);
  let mut t =
    sizes.map(|m| {
      let mut t = T::new();
      let mut k = KeyGen::new();
      for _ in 0 .. m.saturating_sub(100_000) {
        let _ = t.insert(k.next(), NonZeroU32::MIN);
      }
      let n = t.len();
      (t, k, n, m)
    });
  bencher.bench_local(|| go(black_box(&mut t)));
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    // ahash::AHashMap<NonZeroU32, NonZeroU32>,
    foldhash::HashMap<NonZeroU32, NonZeroU32>,
    // tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::new::NewMap<NonZeroU32, NonZeroU32>,
  ])]
fn bench_remove_insert<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32>>(t: &mut [(T, KeyGen, KeyGen)]) -> u32 {
    let mut z = 0;
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut a, ref mut b) in t.iter_mut() {
        for _ in 0 .. 250 {
          if let Some(y) = t.remove(a.next()) { z ^= y.get(); }
          let _ = t.insert(b.next(), b.peek());
        }
      }
    }
    z
  }
  let sizes = sizes_from_working_set(working_set);
  let mut t =
    sizes.map(|m| {
      let mut t = T::new();
      let mut b = KeyGen::new();
      for _ in 0 .. m {
        let _ = t.insert(b.next(), b.peek());
      }
      (t, KeyGen::new(), b)
    });
  bencher.bench_local(|| go(black_box(&mut t)));
}

#[divan::bench(
  sample_count = SAMPLE_COUNT,
  types = [
    // ahash::AHashMap<NonZeroU32, NonZeroU32>,
    foldhash::HashMap<NonZeroU32, NonZeroU32>,
    // tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::new::NewMap<NonZeroU32, NonZeroU32>,
  ])]
fn bench_iter_key<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32>>(t: &mut T) -> u32 {
    let mut z = 0;
    t.for_each(|(x, _)| { z ^= x.get(); });
    z
  }
  let mut t = T::new();
  let mut k = KeyGen::new();
  for _ in 0 .. 1_000_000 { let _ = t.insert(k.next(), k.peek()); }
  bencher.bench_local(|| go(black_box(&mut t)));
}

#[divan::bench(
  sample_count = SAMPLE_COUNT,
  types = [
    // ahash::AHashMap<NonZeroU32, NonZeroU32>,
    foldhash::HashMap<NonZeroU32, NonZeroU32>,
    // tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::new::NewMap<NonZeroU32, NonZeroU32>,
  ])]
fn bench_iter_value<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32>>(t: &mut T) -> u32 {
    let mut z = 0;
    t.for_each(|(_, x)| { z ^= x.get(); });
    z
  }
  let mut t = T::new();
  let mut k = KeyGen::new();
  for _ in 0 .. 1_000_000 { let _ = t.insert(k.next(), k.peek()); }
  bencher.bench_local(|| go(black_box(&mut t)));
}
