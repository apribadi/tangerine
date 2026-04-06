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

fn key_seq(n: usize) -> NonZeroU32 {
  let n = n as u32;
  let n = n | 0x8000_0000;
  let n = n.rotate_left(16);
  unsafe { NonZeroU32::new_unchecked(n) }
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    foldhash::HashMap<NonZeroU32, usize>,
    tangerine::map::HashMap<NonZeroU32, usize>,
  ])]
#[inline(never)]
fn bench_get_chained<T: Map<usize>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      for i in 0 .. m { let _ = t.insert(key_seq(i), i); }
      (t, 0)
    });
  bencher.bench_local(|| {
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut k) in &mut t {
        for _ in 0 .. 500 {
          match t.get(key_seq(*k)) {
            None => { *k = 0; }
            Some(&y) => { *k = y + 1; }
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
  ])]
#[inline(never)]
fn bench_get_unchained<T: Map<usize>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      for i in 0 .. m { let _ = t.insert(key_seq(i), i); }
      (t, 0)
    });
  bencher.bench_local(|| {
    let mut z = 0;
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut k) in &mut t {
        for _ in 0 .. 500 {
          match t.get(key_seq(*k)) {
            None => { *k = 0; }
            Some(&y) => { *k = *k + 1; z = y.wrapping_add(z); }
          }
        }
      }
    }
    black_box(z)
  });
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    foldhash::HashMap<NonZeroU32, usize>,
    tangerine::map::HashMap<NonZeroU32, usize>,
  ])]
#[inline(never)]
fn bench_insert<T: Map<usize>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] = sizes.map(|m| (T::new(), m));
  let mut k = 0;
  bencher.bench_local(|| {
    for _ in 0 .. 200 {
      for &mut (ref mut t, m) in &mut t {
        let mut n = t.len();
        for _ in 0 .. 500 {
          if n == m { n = 0; *t = T::new(); }
          let _ = t.insert(key_seq(k), k);
          n = n + 1;
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
  ])]
#[inline(never)]
fn bench_remove_insert<T: Map<usize>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      for i in 0 .. m { let _ = t.insert(key_seq(i), i); }
      (t, 0, m)
    });
  bencher.bench_local(|| {
    let mut z = 0;
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut a, ref mut b) in &mut t {
        for i in 0 .. 250 {
          if let Some(y) = t.remove(key_seq(*a)) { z = y.wrapping_add(z); }
          let _ = t.insert(key_seq(*b), i);
          *a = *a + 1;
          *b = *b + 1;
        }
      }
    }
    black_box(z)
  });
}
