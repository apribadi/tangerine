use crate::util::BranchyIntMap;
use crate::util::BranchyNewMap;
use crate::util::Map;
use divan::Bencher;
use std::hint::black_box;
use std::num::NonZeroU32;

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

fn key_seq(n: u32) -> NonZeroU32 {
  let n = n | 0x8000_0000;
  let n = n.rotate_left(16);
  unsafe { NonZeroU32::new_unchecked(n) }
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    ahash::AHashMap<NonZeroU32, NonZeroU32>,
    foldhash::HashMap<NonZeroU32, NonZeroU32>,
    tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::new::NewMap<NonZeroU32, NonZeroU32>,
    BranchyIntMap<NonZeroU32>,
    BranchyNewMap<NonZeroU32>,
  ])]
fn bench_get_chained<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32>>(t: &mut [(T, NonZeroU32)]) {
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut k) in t.iter_mut() {
        for _ in 0 .. 500 {
          match t.get(*k) {
            None => { *k = key_seq(0); }
            Some(&y) => { *k = y; }
          }
        }
      }
    }
  }
  let sizes = sizes_from_working_set(working_set);
  let t =
    &mut sizes.map(|m| {
      let mut t = T::new();
      let mut k = 0;
      for _ in 0 .. m {
        let _ = t.insert(key_seq(k), key_seq(k + 1));
        k = k + 1;
      }
      (t, key_seq(0))
    });
  bencher.bench_local(|| go(black_box(t)));
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    ahash::AHashMap<NonZeroU32, NonZeroU32>,
    foldhash::HashMap<NonZeroU32, NonZeroU32>,
    tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::new::NewMap<NonZeroU32, NonZeroU32>,
    BranchyIntMap<NonZeroU32>,
    BranchyNewMap<NonZeroU32>,
  ])]
fn bench_get_unchained<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32>>(t: &mut [(T, u32)]) -> u32 {
    let mut z = 0;
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut k) in t.iter_mut() {
        for _ in 0 .. 500 {
          match t.get(key_seq(*k)) {
            None => { *k = 0; }
            Some(&y) => { *k = *k + 1; z ^= y.get(); }
          }
        }
      }
    }
    z
  }
  let sizes = sizes_from_working_set(working_set);
  let t =
    &mut sizes.map(|m| {
      let mut t = T::new();
      let mut k = 0;
      for _ in 0 .. m {
        let _ = t.insert(key_seq(k), key_seq(k + 1));
        k = k + 1;
      }
      (t, 0)
    });
  bencher.bench_local(|| go(black_box(t)));
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    ahash::AHashMap<NonZeroU32, NonZeroU32>,
    foldhash::HashMap<NonZeroU32, NonZeroU32>,
    tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::new::NewMap<NonZeroU32, NonZeroU32>,
  ])]
fn bench_insert<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32>>(t: &mut [(T, u32, usize, usize)]) {
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut k, ref mut n, m) in t.iter_mut() {
        for _ in 0 .. 500 {
          if *n == m {
            *n = 0;
            *t = T::new();
          }
          let _ = t.insert(key_seq(*k), NonZeroU32::MIN);
          *k = *k + 1;
          *n = *n + 1;
        }
      }
    }
  }
  let sizes = sizes_from_working_set(working_set);
  let t =
    &mut sizes.map(|m| {
      let mut t = T::new();
      let mut k = 0;
      for _ in 0 .. m.saturating_sub(100_000) {
        let _ = t.insert(key_seq(k), NonZeroU32::MIN);
        k = k + 1;
      }
      let n = t.len();
      (t, k, n, m)
    });
  bencher.bench_local(|| go(black_box(t)));
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    ahash::AHashMap<NonZeroU32, NonZeroU32>,
    foldhash::HashMap<NonZeroU32, NonZeroU32>,
    tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::new::NewMap<NonZeroU32, NonZeroU32>,
  ])]
fn bench_remove_insert<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32>>(t: &mut [(T, u32, u32)]) -> u32 {
    let mut z = 0;
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut i, ref mut j) in t.iter_mut() {
        for _ in 0 .. 250 {
          if let Some(y) = t.remove(key_seq(*i)) { z ^= y.get(); }
          let _ = t.insert(key_seq(*j), key_seq(*j));
          *i = *i + 1;
          *j = *j + 1;
        }
      }
    }
    z
  }
  let sizes = sizes_from_working_set(working_set);
  let t =
    &mut sizes.map(|m| {
      let mut t = T::new();
      let mut k = 0;
      for _ in 0 .. m {
        let _ = t.insert(key_seq(k), key_seq(k));
        k = k + 1;
      }
      (t, 0, k)
    });
  bencher.bench_local(|| go(black_box(t)));
}

#[divan::bench(
  sample_count = SAMPLE_COUNT,
  types = [
    ahash::AHashMap<NonZeroU32, NonZeroU32>,
    foldhash::HashMap<NonZeroU32, NonZeroU32>,
    tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::new::NewMap<NonZeroU32, NonZeroU32>,
  ])]
fn bench_for_each_key<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32>>(t: &mut T) -> u32 {
    let mut z = 0;
    t.for_each(|(x, _)| { z ^= x.get(); });
    z
  }
  let mut t = T::new();
  for i in 0 .. 1_000_000 { let _ = t.insert(key_seq(i), key_seq(i)); }
  bencher.bench_local(|| go(black_box(&mut t)));
}

#[divan::bench(
  sample_count = SAMPLE_COUNT,
  types = [
    ahash::AHashMap<NonZeroU32, NonZeroU32>,
    foldhash::HashMap<NonZeroU32, NonZeroU32>,
    tangerine::map::IntMap<NonZeroU32, NonZeroU32>,
    tangerine::new::NewMap<NonZeroU32, NonZeroU32>,
  ])]
fn bench_for_each_value<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>) {
  #[inline(never)]
  fn go<T: Map<NonZeroU32>>(t: &mut T) -> u32 {
    let mut z = 0;
    t.for_each(|(_, x)| { z ^= x.get(); });
    z
  }
  let mut t = T::new();
  for i in 0 .. 1_000_000 { let _ = t.insert(key_seq(i), key_seq(i)); }
  bencher.bench_local(|| go(black_box(&mut t)));
}
