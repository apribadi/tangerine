use std::num::NonZeroU64;
use divan::Bencher;
use divan::black_box;
use crate::util::Map;

// TODO: keyed by NonZeroU32

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

struct KeyGen(NonZeroU64);

impl KeyGen {
  const fn new() -> Self {
    KeyGen(unsafe { NonZeroU64::new_unchecked(0xcafe_babe_cafe_babe) })
  }

  const fn next(&mut self) -> NonZeroU64 {
    let x = self.0;
    let y = x.get();
    let y = y ^ y << 9;
    let y = y ^ y >> 7;
    self.0 = unsafe { NonZeroU64::new_unchecked(y) };
    x
  }

  const fn peek(&mut self) -> NonZeroU64 {
    self.0
  }
}

#[divan::bench(
  args = ARGS,
  sample_count = SAMPLE_COUNT,
  types = [
    foldhash::HashMap<NonZeroU64, NonZeroU64>,
    tangerine::map::HashMap<NonZeroU64, NonZeroU64>,
    tangerine::old_map::HashMap<NonZeroU64, NonZeroU64>,
    tangerine::two::HashMap<NonZeroU64, NonZeroU64>,
  ])]
#[inline(never)]
fn bench_get_chained<T: Map<NonZeroU64>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut g = KeyGen::new();
      for _ in 0 .. m {
        t.insert(g.next(), g.peek());
      }
      (t, KeyGen::new().next())
    });
  bencher.bench_local(|| {
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut k) in &mut t {
        for _ in 0 .. 500 {
          match t.get(*k) {
            None => { *k = KeyGen::new().next(); }
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
    foldhash::HashMap<NonZeroU64, u64>,
    tangerine::map::HashMap<NonZeroU64, u64>,
    tangerine::old_map::HashMap<NonZeroU64, u64>,
    tangerine::two::HashMap<NonZeroU64, u64>,
  ])]
#[inline(never)]
fn bench_get_unchained<T: Map<u64>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut g = KeyGen::new();
      for i in 0 .. m {
        t.insert(g.next(), i as u64);
      }
      (t, KeyGen::new())
    });
  bencher.bench_local(|| {
    let mut a = 0u64;
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut g) in &mut t {
        for _ in 0 .. 500 {
          match t.get(g.next()) {
            None => { *g = KeyGen::new(); }
            Some(&y) => { a = a.wrapping_add(y); }
          }
        }
      }
    }
    black_box(a)
  });
}


#[divan::bench(
  sample_count = SAMPLE_COUNT,
  args = [1_000, 10_000, 100_000, 1_000_000, 10_000_000],
  types = [
    foldhash::HashMap<NonZeroU64, u64>,
    tangerine::map::HashMap<NonZeroU64, u64>,
    tangerine::old_map::HashMap<NonZeroU64, u64>,
    tangerine::two::HashMap<NonZeroU64, u64>,
  ])]
#[inline(never)]
fn bench_insert<T: Map<u64>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] = sizes.map(|n| (T::new(), n));
  let mut g = KeyGen::new();
  bencher.bench_local(|| {
    for _ in 0 .. 200 {
      for &mut (ref mut t, n) in &mut t {
        let mut k = t.len();
        for i in 0 .. 500 {
          if k == n { k = 0; *t = T::new(); }
          t.insert(g.next(), i as u64);
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
    foldhash::HashMap<NonZeroU64, u64>,
    tangerine::map::HashMap<NonZeroU64, u64>,
    tangerine::old_map::HashMap<NonZeroU64, u64>,
    tangerine::two::HashMap<NonZeroU64, u64>,
  ])]
#[inline(never)]
fn bench_remove_insert<T: Map<u64>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut g = KeyGen::new();
      for i in 0 .. m {
        t.insert(g.next(), i as u64);
      }
      (t, KeyGen::new(), g)
    });
  bencher.bench_local(|| {
    for _ in 0 .. 200 {
      for &mut (ref mut t, ref mut a, ref mut b) in &mut t {
        for i in 0 .. 250 {
          let _ = t.remove(a.next());
          let _ = t.insert(b.next(), i);
        }
      }
    }
  });
}
