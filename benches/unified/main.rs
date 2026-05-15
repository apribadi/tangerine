//! unified benchmarks

mod maps;

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
  state: u64,
}

impl KeyGen {
  const ROL: u32 = 25;

  const fn new() -> Self {
    Self { state: 1 }
  }

  fn peek(&self) -> NonZeroU32 {
    let s = self.state;
    let x = unsafe { NonZeroU32::new_unchecked((s as u32).rotate_left(Self::ROL)) };
    x
  }

  fn next(&mut self) -> NonZeroU32 {
    let s = self.state;
    let x = unsafe { NonZeroU32::new_unchecked((s as u32).rotate_left(Self::ROL)) };
    self.state = s.wrapping_add(2);
    x
  }
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    std::collections::HashMap<NonZeroU32, NonZeroU32, foldhash::fast::RandomState>,
    tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
  ])]
fn bench_get_chained<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32>>(t: &mut [(T, NonZeroU32)]) {
    for _ in 0 .. 1000 {
      for &mut (ref mut t, ref mut k) in t.iter_mut() {
        for _ in 0 .. 100 {
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
    std::collections::HashMap<NonZeroU32, u32, ahash::RandomState>,
    std::collections::HashMap<NonZeroU32, u32, foldhash::fast::RandomState>,
    std::collections::HashMap<NonZeroU32, u32, rustc_hash::FxBuildHasher>,
    tangerine::map::IntMap<NonZeroU32, u32>,
  ])]
fn bench_get_unchained<T: Map<u32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<u32>>(t: &mut [(T, KeyGen)]) -> u32 {
    let mut z = 0;
    for _ in 0 .. 1000 {
      for &mut (ref mut t, ref mut k) in t.iter_mut() {
        for _ in 0 .. 100 {
          match t.get(k.next()) {
            None => { *k = KeyGen::new(); }
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
      let mut k = KeyGen::new();
      for _ in 0 .. m {
        let _ = t.insert(k.next(), k.peek().get());
      }
      (t, KeyGen::new())
    });
  bencher.bench_local(|| go(black_box(&mut t)));
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    std::collections::HashMap<NonZeroU32, u32, foldhash::fast::RandomState>,
    std::collections::HashMap<NonZeroU32, u32, ahash::RandomState>,
    tangerine::map::IntMap<NonZeroU32, u32>,
  ])]
fn bench_insert<T: Map<u32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<u32>>(t: &mut [(T, KeyGen, usize, usize)]) {
    for _ in 0 .. 1000 {
      for &mut (ref mut t, ref mut k, ref mut n, limit) in t.iter_mut() {
        for _ in 0 .. 100 {
          if *n == limit {
            *t = T::new();
            *n = 0;
          }
          let _ = t.insert(k.next(), k.peek().get());
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
        let _ = t.insert(k.next(), k.peek().get());
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
    std::collections::HashMap<NonZeroU32, u32, foldhash::fast::RandomState>,
    tangerine::map::IntMap<NonZeroU32, u32>,
  ])]
fn bench_remove_insert<T: Map<u32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<u32>>(t: &mut [(T, KeyGen, KeyGen)]) -> u32 {
    let mut z = 0;
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut a, ref mut b) in t.iter_mut() {
        for _ in 0 .. 250 {
          if let Some(y) = t.remove(a.next()) { z ^= y; }
          let _ = t.insert(b.next(), b.peek().get());
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
        let _ = t.insert(b.next(), b.peek().get());
      }
      (t, KeyGen::new(), b)
    });
  bencher.bench_local(|| go(black_box(&mut t)));
}

#[divan::bench(
  sample_count = SAMPLE_COUNT,
  types = [
    std::collections::HashMap<NonZeroU32, u32, foldhash::fast::RandomState>,
    tangerine::map::IntMap<NonZeroU32, u32>,
  ])]
fn bench_iter_key<T: Map<u32>>(bencher: Bencher<'_, '_>) {
  #[inline(never)]
  fn go<T: Map<u32>>(t: &mut T) -> u32 {
    let mut z = 0;
    t.for_each(|(x, _)| { z ^= x.get(); });
    z
  }
  let mut t = T::new();
  let mut k = KeyGen::new();
  for _ in 0 .. 1_000_000 { let _ = t.insert(k.next(), k.peek().get()); }
  bencher.bench_local(|| go(black_box(&mut t)));
}

fn key_seq(n: u32) -> NonZeroU32 {
  let n = n | 0x8000_0000;
  let n = n.rotate_left(16);
  unsafe { NonZeroU32::new_unchecked(n) }
}

#[divan::bench(
  sample_count = SAMPLE_COUNT,
  types = [
    std::collections::HashMap<NonZeroU32, u32, foldhash::fast::RandomState>,
    tangerine::map::IntMap<NonZeroU32, u32>,
  ])]
fn bench_iter_value<T: Map<u32>>(bencher: Bencher<'_, '_>) {
  #[inline(never)]
  fn go<T: Map<u32>>(t: &mut T) -> u32 {
    let mut z = 0;
    t.for_each(|(_, x)| { z ^= x; });
    z
  }
  let mut t = T::new();
  // let mut k = KeyGen::new();
  // for _ in 0 .. 1_000_000 { let _ = t.insert(k.next(), k.peek()); }
  for i in 0 .. 1_000_000 { let _ = t.insert(key_seq(i), key_seq(i).get()); }
  bencher.bench_local(|| go(black_box(&mut t)));
}
