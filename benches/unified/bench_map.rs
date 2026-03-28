use std::num::NonZeroU64;
use std::array;
use divan::Bencher;
use divan::black_box;
use crate::util::Map;

// TODO: keyed by NonZeroU32

const ARGS: [usize; 7] = [
  1_000,
  3_000,
  10_000,
  30_000,
  100_000,
  300_000,
  1_000_000,
];

const N: usize = 1_000_000;
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
  let s = n.iter().sum::<usize>();
  let mut r = [0; 10];
  for i in 0 .. 9 { r[i] = n[i] * working_set / s; }
  r[9] = working_set - r[0 .. 9].iter().sum::<usize>();
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

/*
struct KeyGen(u64);

impl KeyGen {
  const fn new() -> Self {
    KeyGen(unsafe { NonZeroU64::new_unchecked(1) })
  }

  const fn next(&mut self) -> NonZeroU64 {
    let x = self.0;
    self.0 = x.wrapping_add(1);
    unsafe { NonZeroU64::new_unchecked(x.reverse_bits() | 1) }
  }
}
*/

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
  let mut ts: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut g = KeyGen::new();
      for _ in 0 .. m {
        t.insert(g.next(), g.peek());
      }
      (t, KeyGen::new().next())
    });
  bencher.bench_local(|| {
    let mut n = N;
    'done: loop {
      for &mut (ref mut t, ref mut k) in ts.iter_mut() {
        for _ in 0 .. 500 {
          match t.get(*k) {
            None => {
              *k = KeyGen::new().next();
            }
            Some(&y) => {
              *k = y;
            }
          };
          n = n - 1;
          if n == 0 { break 'done; }
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
  let mut ts: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut g = KeyGen::new();
      for i in 0 .. m {
        t.insert(g.next(), i as u64);
      }
      (t, KeyGen::new())
    });
  bencher.bench_local(|| {
    let mut n = N;
    let mut a = 0u64;
    'done: loop {
      for &mut (ref mut t, ref mut g) in ts.iter_mut() {
        for _ in 0 .. 500 {
          match t.get(g.next()) {
            None => {
              *g = KeyGen::new();
            }
            Some(&y) => {
              a = a.wrapping_add(y);
            }
          };
          n = n - 1;
          if n == 0 { break 'done; }
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
  let mut t: [_; 10] = array::from_fn(|_| T::new());
  let mut g = KeyGen::new();
  bencher.bench_local(|| {
    let mut n = N;
    'done: loop {
      for (i, t) in t.iter_mut().enumerate() {
        let limit = sizes[i];
        let mut k = t.len();
        for _ in 0 .. 500 {
          if k == limit {
            k = 0;
            *t = T::new();
          }
          t.insert(g.next(), 0);
          k = k + 1;
          n = n - 1;
          if n == 0 { break 'done; }
        }
      }
    }
  });
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
fn bench_remove_insert_chained<T: Map<NonZeroU64>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut ts: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut g = KeyGen::new();
      for _ in 0 .. m {
        t.insert(g.next(), g.peek());
      }
      (t, KeyGen::new().next(), g)
    });
  bencher.bench_local(|| {
    let mut n = N;
    'done: loop {
      for &mut (ref mut t, ref mut a, ref mut b) in ts.iter_mut() {
        for _ in 0 .. 250 {
          *a = t.remove(*a).unwrap();
          n = n - 1;
          if n == 0 { break 'done; }
          // TODO: make insert depend on removed item??
          let _ = t.insert(b.next(), b.peek());
          n = n - 1;
          if n == 0 { break 'done; }
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
fn bench_remove_insert_unchained<T: Map<u64>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut ts: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut g = KeyGen::new();
      for i in 0 .. m {
        t.insert(g.next(), i as u64);
      }
      (t, KeyGen::new(), g)
    });
  bencher.bench_local(|| {
    let mut n = N;
    'done: loop {
      for &mut (ref mut t, ref mut a, ref mut b) in ts.iter_mut() {
        for i in 0 .. 250 {
          let _ = t.remove(a.next());
          n = n - 1;
          if n == 0 { break 'done; }
          let _ = t.insert(b.next(), i);
          n = n - 1;
          if n == 0 { break 'done; }
        }
      }
    }
  });
}

/*
const N: usize = 10;
const C: usize = 500;
const K: usize = 100;

const _: () = assert!(N * C == 5_000); // total working set
const _: () = assert!(K * N * C * 2 == 1_000_000); // number of operations

#[divan::bench(
  sample_count = SAMPLE_COUNT,
  types = [
    foldhash::HashMap<NonZeroU64, u64>,
    tangerine::map::HashMap<NonZeroU64, u64>,
    tangerine::new::HashMap<u64>,
    tangerine::two::HashMap<NonZeroU64, u64>,
  ])]
#[inline(never)]
fn bench_insert_remove<T: Map<u64>>(bencher: Bencher<'_, '_>) {
  let mut t: [_; N] = array::from_fn(|_| T::new());
  bencher.bench_local(|| {
    for _ in 0 .. K {
      for i in 0 .. N {
        let t = &mut t[i];
        for x in 0 .. C { t.insert(make_key(x), x as u64); }
        for x in 0 .. C { t.remove(make_key(x)); }
      }
    }
  });
}
*/
