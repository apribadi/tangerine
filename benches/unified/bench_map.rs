use std::num::NonZeroU64;
use std::array;
use divan::Bencher;
use crate::util::Map;

const N: usize = 10;
const C: usize = 500;
const K: usize = 100;

const _: () = assert!(N * C == 5_000); // total working set
const _: () = assert!(K * N * C * 2 == 1_000_000); // number of operations

fn make_key(x: usize) -> NonZeroU64 {
  return unsafe { NonZeroU64::new_unchecked((x as u64).rotate_left(16) | 1) };
}

#[divan::bench(
  sample_count = 9,
  types = [
    tangerine::map::HashMap<NonZeroU64, u64>,
    ahash::AHashMap<NonZeroU64, u64>,
    foldhash::HashMap<NonZeroU64, u64>,
  ])]
#[inline(never)]
fn bench_get<T: Map>(bencher: Bencher<'_, '_>) {
  // TODO:
  // - different sized tables
  // - make next lookup depend on result of previous
  let mut t: [_; N] = array::from_fn(|_| T::new());
  for i in 0 .. N {
    let t = &mut t[i];
    for j in 0 .. C {
      t.insert(make_key(j), j as u64);
    }
  }

  bencher.bench_local(|| {
    let mut a = 0;
    for _ in 0 .. K {
      for i in 0 .. N {
        let t = &mut t[i];
        for j in 0 .. C { if let Some(&y) = t.get(make_key(j)) { a += y; } }
        for j in 0 .. C { if let Some(&y) = t.get(make_key(j)) { a += y; } }
      }
    }
    divan::black_box(a)
  });
}

#[divan::bench(
  sample_count = 9,
  types = [
    tangerine::map::HashMap<NonZeroU64, u64>,
    ahash::AHashMap<NonZeroU64, u64>,
    foldhash::HashMap<NonZeroU64, u64>,
  ])]
#[inline(never)]
fn bench_insert<T: Map>(bencher: Bencher<'_, '_>) {
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
    tangerine::map::HashMap<NonZeroU64, u64>,
    ahash::AHashMap<NonZeroU64, u64>,
    foldhash::HashMap<NonZeroU64, u64>,
  ])]
#[inline(never)]
fn bench_insert_remove<T: Map>(bencher: Bencher<'_, '_>) {
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
