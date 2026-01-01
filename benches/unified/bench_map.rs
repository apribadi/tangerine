use std::num::NonZeroU64;
use std::array;

const N: usize = 10;
const C: usize = 500;
const K: usize = 100;

const _: () = assert!(N * C == 5_000); // total working set
const _: () = assert!(K * N * C * 2 == 1_000_000); // number of operations

fn make_key(x: usize) -> NonZeroU64 {
  return unsafe { NonZeroU64::new_unchecked((x as u64).rotate_left(16) | 1) };
}

#[inline(never)]
fn insert_only<T: crate::util::Map>() {
  let mut t: [_; N] = array::from_fn(|_| T::new());
  for _ in 0 .. K {
    for i in 0 .. N {
      let t = &mut t[i];
      *t = T::new();
      for x in 0 .. C { t.insert(make_key(x), x as u64); }
      *t = T::new();
      for x in 0 .. C { t.insert(make_key(x), x as u64); }
    }
  }
}

#[inline(never)]
fn insert_remove<T: crate::util::Map>() {
  let mut t: [_; N] = array::from_fn(|_| T::new());
  for _ in 0 .. K {
    for i in 0 .. N {
      let t = &mut t[i];
      for x in 0 .. C { t.insert(make_key(x), x as u64); }
      for x in 0 .. C { t.remove(make_key(x)); }
    }
  }
}

#[divan::bench]
fn insert_only_tangerine() {
  insert_only::<tangerine::map::HashMap<NonZeroU64, u64>>();
}

/*
#[divan::bench]
fn insert_only_ahash() {
  insert_only::<ahash::AHashMap<NonZeroU64, u64>>();
}
*/

#[divan::bench]
fn insert_only_foldhash() {
  insert_only::<foldhash::HashMap<NonZeroU64, u64>>();
}

#[divan::bench]
fn insert_remove_tangerine() {
  insert_remove::<tangerine::map::HashMap<NonZeroU64, u64>>();
}

/*
#[divan::bench]
fn insert_remove_ahash() {
  insert_remove::<ahash::AHashMap<NonZeroU64, u64>>();
}
*/

#[divan::bench]
fn insert_remove_foldhash() {
  insert_remove::<foldhash::HashMap<NonZeroU64, u64>>();
}
