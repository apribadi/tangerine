use std::num::NonZeroU64;
use std::array;
use divan::Bencher;
use divan::black_box;
use crate::util::Map;

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
  n.map(|k| k * working_set / n.iter().sum::<usize>())
}

struct KeyGen(NonZeroU64);

impl KeyGen {
  const INITIAL: NonZeroU64 = unsafe { NonZeroU64::new_unchecked(1) };

  fn new() -> Self {
    KeyGen(KeyGen::INITIAL)
  }

  fn next(&mut self) -> NonZeroU64 {
    let x = self.0;
    let y = x.get();
    let y = y ^ y << 9;
    let y = y ^ y >> 7;
    self.0 = unsafe { NonZeroU64::new_unchecked(y) };
    x
  }
}

/*
struct KeyGen(u64);

impl KeyGen {
  const INITIAL: NonZeroU64 = unsafe { NonZeroU64::new_unchecked(1) };

  fn new() -> Self {
    KeyGen(0)
  }

  fn next(&mut self) -> NonZeroU64 {
    let x = self.0;
    self.0 = x.wrapping_add(1);
    unsafe { NonZeroU64::new_unchecked(x.reverse_bits() | 1) }
  }
}
*/

#[divan::bench(
  args = [10_000, 100_000, 1_000_000],
  sample_count = 9,
  types = [
    ahash::AHashMap<NonZeroU64, NonZeroU64>,
    foldhash::HashMap<NonZeroU64, NonZeroU64>,
    tangerine::map::HashMap<NonZeroU64, NonZeroU64>,
    tangerine::new::HashMap<NonZeroU64>,
    tangerine::two::HashMap<NonZeroU64>,
  ])]
#[inline(never)]
fn bench_get_chained<T: Map<NonZeroU64>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut g = KeyGen::new();
      let mut k = g.next();
      for _ in 0 .. m {
        let x = k;
        k = g.next();
        let y = k;
        t.insert(x, y);
      }
      t
    });
  bencher.bench_local(|| {
    let mut n = 1_000_000;
    let mut k = KeyGen::INITIAL;
    'done: loop {
      for t in t.iter_mut() {
        for _ in 0 .. 500 {
          match t.get(k) {
            None => {
              k = KeyGen::INITIAL;
            }
            Some(&y) => {
              k = y;
            }
          };
          n = n - 1;
          if n == 0 { break 'done; }
        }
      }
    }
    black_box(k)
  });
}

#[divan::bench(
  args = [10_000, 100_000, 1_000_000],
  sample_count = 9,
  types = [
    ahash::AHashMap<NonZeroU64, u64>,
    foldhash::HashMap<NonZeroU64, u64>,
    tangerine::map::HashMap<NonZeroU64, u64>,
    tangerine::new::HashMap<u64>,
    tangerine::two::HashMap<u64>,
  ])]
#[inline(never)]
fn bench_get_unchained<T: Map<u64>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] =
    sizes.map(|m| {
      let mut t = T::new();
      let mut g = KeyGen::new();
      for i in 0 .. m { t.insert(g.next(), i as u64); }
      t
    });
  bencher.bench_local(|| {
    let mut n = 1_000_000;
    let mut a = 0u64;
    let mut g = KeyGen::new();
    'done: loop {
      for t in t.iter_mut() {
        for _ in 0 .. 500 {
          match t.get(g.next()) {
            None => {
              g = KeyGen::new();
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
  sample_count = 9,
  args = [10_000, 100_000, 1_000_000],
  types = [
    ahash::AHashMap<NonZeroU64, u64>,
    foldhash::HashMap<NonZeroU64, u64>,
    tangerine::map::HashMap<NonZeroU64, u64>,
    tangerine::new::HashMap<u64>,
    tangerine::two::HashMap<u64>,
  ])]
#[inline(never)]
fn bench_insert<T: Map<u64>>(bencher: Bencher<'_, '_>, working_set: usize) {
  let sizes = sizes_from_working_set(working_set);
  let mut t: [_; 10] = array::from_fn(|_| T::new());
  let mut g = KeyGen::new();
  bencher.bench_local(|| {
    let mut n = 1_000_000;
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

/*
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
*/
