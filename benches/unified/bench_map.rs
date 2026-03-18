use std::num::NonZeroU64;
use std::array;
use divan::Bencher;
use divan::black_box;
use crate::util::Map;

/*
const SIZES: [usize; 10] = [
  50,
  53,
  57,
  61,
  66,
  70,
  75,
  81,
  87,
  93,
];
*/

/*
const SIZES: [usize; 10] = [
  500,
  536,
  574,
  616,
  660,
  707,
  758,
  812,
  871,
  933,
];
*/

/*
const SIZES: [usize; 10] = [
  5000,
  5360,
  5740,
  6160,
  6600,
  7070,
  7580,
  8120,
  8710,
  9330,
];
*/

const SIZES: [usize; 10] = [
  50000,
  53600,
  57400,
  61600,
  66000,
  70700,
  75800,
  81200,
  87100,
  93300,
];

fn make_key(x: usize) -> NonZeroU64 {
  unsafe { NonZeroU64::new_unchecked((x as u64).rotate_left(16) | 1) }
}

#[divan::bench(
  sample_count = 9,
  types = [
    ahash::AHashMap<NonZeroU64, NonZeroU64>,
    foldhash::HashMap<NonZeroU64, NonZeroU64>,
    tangerine::map::HashMap<NonZeroU64, NonZeroU64>,
    tangerine::new::HashMap<NonZeroU64>,
    tangerine::two::HashMap<NonZeroU64>,
  ])]
#[inline(never)]
fn bench_get_chained<T: Map<NonZeroU64>>(bencher: Bencher<'_, '_>) {
  let mut t: [_; 10] =
    SIZES.map(|m| {
      let mut t = T::new();
      for i in 0 .. m { t.insert(make_key(i), make_key(i + 1)); }
      t
    });
  bencher.bench_local(|| {
    let mut n = 1_000_000;
    let mut k = make_key(0);
    'done: loop {
      for t in t.iter_mut() {
        for _ in 0 .. 1000 {
          k = match t.get(k) { None => make_key(0), Some(&y) => y };
          n = n - 1;
          if n == 0 { break 'done; }
        }
      }
    }
    black_box(k)
  });
}

#[divan::bench(
  sample_count = 9,
  types = [
    ahash::AHashMap<NonZeroU64, u64>,
    foldhash::HashMap<NonZeroU64, u64>,
    tangerine::map::HashMap<NonZeroU64, u64>,
    tangerine::new::HashMap<u64>,
    tangerine::two::HashMap<u64>,
  ])]
#[inline(never)]
fn bench_insert<T: Map<u64>>(bencher: Bencher<'_, '_>) {
  let mut t: [_; 10] = array::from_fn(|_| T::new());
  bencher.bench_local(|| {
    let mut n = 1_000_000;
    'done: loop {
      for (i, t) in t.iter_mut().enumerate() {
        let m = SIZES[i];
        let mut k = t.len();
        for _ in 0 .. 1000 {
          if k == m { k = 0; *t = T::new(); }
          t.insert(make_key(k), k as u64);
          k = k + 1;
          n = n - 1;
          if n == 0 { break 'done; }
        }
      }
    }
  });
}

const N: usize = 10;
const C: usize = 500;
const K: usize = 100;

const _: () = assert!(N * C == 5_000); // total working set
const _: () = assert!(K * N * C * 2 == 1_000_000); // number of operations

#[divan::bench(
  sample_count = 9,
  types = [
    ahash::AHashMap<NonZeroU64, u64>,
    foldhash::HashMap<NonZeroU64, u64>,
    tangerine::map::HashMap<NonZeroU64, u64>,
    tangerine::new::HashMap<u64>,
    tangerine::two::HashMap<u64>,
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
