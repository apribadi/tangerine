use std::num::NonZeroU32;
use divan::Bencher;
use crate::util::Map;
use crate::util::BranchyIntMap;

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
  ])]
fn bench_get_chained<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut k = 0;
      for _ in 0 .. m {
        let _ = t.insert(key_seq(k), key_seq(k + 1));
        k = k + 1;
      }
      (t, key_seq(0))
    });
  bencher.bench_local(|| {
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut a) in &mut t {
        let mut k = *a;
        for _ in 0 .. 500 {
          match t.get(k) {
            None => { k = key_seq(0); }
            Some(&y) => { k = y; }
          }
        }
        *a = k;
      }
    }
  });
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
  ])]
fn bench_get_unchained<T: Map<NonZeroU32>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut k = 0;
      for _ in 0 .. m {
        let _ = t.insert(key_seq(k), key_seq(k + 1));
        k = k + 1;
      }
      (t, 0)
    });
  bencher.bench_local(|| {
    let mut z = 0;
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut a) in &mut t {
        let mut k = *a;
        for _ in 0 .. 500 {
          match t.get(key_seq(k)) {
            None => { k = 0; }
            Some(&y) => { k = k + 1; z ^= y.get(); }
          }
        }
        *a = k;
      }
    }
    z
  });
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
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut k = 0;
      for _ in 0 .. m.saturating_sub(100_000) {
        let _ = t.insert(key_seq(k), NonZeroU32::MIN);
        k = k + 1;
      }
      let n = t.len();
      (t, k, n, m)
    });
  bencher.bench_local(|| {
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut a, ref mut b, m) in &mut t {
        let mut k = *a;
        let mut n = *b;
        for _ in 0 .. 500 {
          if n == m {
            n = 0;
            *t = T::new();
          }
          let _ = t.insert(key_seq(k), NonZeroU32::MIN);
          k = k + 1;
          n = n + 1;
        }
        *a = k;
        *b = n;
      }
    }
  });
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
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut k = 0;
      for _ in 0 .. m {
        let _ = t.insert(key_seq(k), key_seq(k));
        k = k + 1;
      }
      (t, 0, k)
    });
  bencher.bench_local(|| {
    let mut z = 0;
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut a, ref mut b) in &mut t {
        let mut i = *a;
        let mut j = *b;
        for _ in 0 .. 250 {
          if let Some(y) = t.remove(key_seq(i)) { z ^= y.get(); }
          let _ = t.insert(key_seq(j), key_seq(j));
          i = i + 1;
          j = j + 1;
        }
        *a = i;
        *b = j;
      }
    }
    z
  });
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
  let mut t = T::new();
  for i in 0 .. 1_000_000 { let _ = t.insert(key_seq(i), key_seq(i)); }
  bencher.bench_local(|| {
    let mut z = 0;
    t.for_each(|(x, _)| { z ^= x.get(); });
    z
  });
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
  let mut t = T::new();
  for i in 0 .. 1_000_000 { let _ = t.insert(key_seq(i), key_seq(i)); }
  bencher.bench_local(|| {
    let mut z = 0;
    t.for_each(|(_, x)| { z ^= x.get(); });
    z
  });
}
