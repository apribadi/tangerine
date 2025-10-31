use std::num::NonZeroU64;
use std::array;

const N: usize = 20;
const C: usize = 500;
const K: usize = 50;

const _: () = assert!(N * C == 10_000); // total working set
const _: () = assert!(K * N * C * 2 == 1_000_000); // number of operations

fn make_key(x: usize) -> NonZeroU64 {
  return unsafe { NonZeroU64::new_unchecked((x as u64).rotate_left(16) | 1) };
}

#[divan::bench]
fn insert_remove_tangerine() {
  let mut t: [_; N] = array::from_fn(|_| tangerine::map::HashMap::new());
  for _ in 0 .. K {
    for i in 0 .. N {
      for x in 0 .. C { let _ = t[i].insert(make_key(x), x); }
      for x in (0 .. C).rev() { let _ = t[i].remove(make_key(x)); }
    }
  }
}

#[divan::bench]
fn insert_remove_ahash() {
  let mut t: [_; N] = array::from_fn(|_| ahash::AHashMap::new());
  for _ in 0 .. K {
    for i in 0 .. N {
      for x in 0 .. C { let _ = t[i].insert(make_key(x), x); }
      for x in (0 .. C).rev() { let _ = t[i].remove(&make_key(x)); }
    }
  }
}

#[divan::bench]
fn insert_remove_foldhash() {
  let mut t: [_; N] = array::from_fn(|_| <foldhash::HashMap<_, _> as foldhash::HashMapExt>::new());
  for _ in 0 .. K {
    for i in 0 .. N {
      for x in 0 .. C { let _ = t[i].insert(make_key(x), x); }
      for x in (0 .. C).rev() { let _ = t[i].remove(&make_key(x)); }
    }
  }
}
