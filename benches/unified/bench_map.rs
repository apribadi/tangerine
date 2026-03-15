use std::num::NonZeroU64;
use std::array;
use divan::Bencher;
use divan::black_box;
use crate::util::Map;

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

fn make_key(x: usize) -> NonZeroU64 {
  return unsafe { NonZeroU64::new_unchecked((x as u64).rotate_left(16) | 1) };
}

#[divan::bench(
  sample_count = 9,
  types = [
    ahash::AHashMap<NonZeroU64, NonZeroU64>,
    foldhash::HashMap<NonZeroU64, NonZeroU64>,
    tangerine::map::HashMap<NonZeroU64, NonZeroU64>,
  ])]
#[inline(never)]
fn bench_get<T: Map<NonZeroU64>>(bencher: Bencher<'_, '_>) {
  let mut t: [_; 10] =
    SIZES.map(|n| {
      let mut t = T::new();
      for i in 0 .. n { t.insert(make_key(i), make_key(i + 1)); }
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
  ])]
#[inline(never)]
fn bench_insert<T: Map<u64>>(bencher: Bencher<'_, '_>) {
  let mut t: [_; N] = array::from_fn(|_| T::new());
  bencher.bench_local(|| {
    for _ in 0 .. K {
      for i in 0 .. N {
        let t = &mut t[i];
        *t = T::new();
        for x in 0 .. C { t.insert(make_key(x), x as u64); }
        *t = T::new();
        for x in 0 .. C { t.insert(make_key(x), x as u64); }
      }
    }
  });
}

#[divan::bench(
  sample_count = 9,
  types = [
    ahash::AHashMap<NonZeroU64, u64>,
    foldhash::HashMap<NonZeroU64, u64>,
    tangerine::map::HashMap<NonZeroU64, u64>,
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
