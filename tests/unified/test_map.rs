#![allow(unused_must_use)]

use dandelion::Rng;
use expect_test::expect;
use std::fmt::Write;
use std::num::NonZeroU128;
use std::num::NonZeroU32;
use std::num::NonZeroU8;
use std::num::NonZeroU16;
use std::write;
use tangerine::map::IntMap;
use tangerine::map;
use tangerine::hash;

/*
#[test]
fn test_lifetime() {
  let mut g = Rng::new(NonZeroU128::MIN);
  let mut t = IntMap::with_seed(&mut g);
  let key = NonZeroU32::new(13).unwrap();
  t.insert(key, 1u64);
  let mut i = t.keys();
  let _ = i.next();
  t.reset();
  let _ = i.next();
}
*/

#[test]
fn test_api() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);
  let mut t = IntMap::with_seed(&mut g);

  t.clear();
  t.reset();

  let key = NonZeroU32::new(13).unwrap();

  write!(s, "{:?} <- t.len()\n", t.len());
  write!(s, "{:?} <- t.is_empty()\n", t.is_empty());
  write!(s, "{:?} <- t.contains_key({:?})\n", t.contains_key(key), key);
  write!(s, "{:?} <- t.get({:?})\n", t.get(key), key);
  write!(s, "{:?} <- t.get_mut({:?})\n", t.get_mut(key), key);
  write!(s, "{:?} <- map::internal::num_slots(&t))\n", map::internal::num_slots(&t));
  write!(s, "{:?} <- map::internal::load_factor(&t))\n", map::internal::load_factor(&t));
  write!(s, "{:?} <- map::internal::allocation_size(&t))\n", map::internal::allocation_size(&t));
  write!(s, "{:?} <- t.try_insert({:?}, {:?})\n", t.insert(key, 40), key, 40);
  write!(s, "{:?} <- t.try_insert({:?}, {:?})\n", t.insert(key, 41), key, 41);
  write!(s, "{:?} <- t.insert({:?}, {:?})\n", t.insert(key, 42), key, 42);
  write!(s, "{:?} <- t.len()\n", t.len());
  write!(s, "{:?} <- t.is_empty()\n", t.is_empty());
  write!(s, "{:?} <- t.contains_key({:?})\n", t.contains_key(key), key);
  write!(s, "{:?} <- t.get({:?})\n", t.get(key), key);
  write!(s, "{:?} <- t.get_mut({:?})\n", t.get_mut(key), key);
  write!(s, "{:?} <- t.get_disjoint_mut([])\n", t.get_disjoint_mut([]));
  write!(s, "{:?} <- t.get_disjoint_mut({:?})\n", t.get_disjoint_mut([NonZeroU32::MIN, key]), [NonZeroU32::MIN, key]);
  write!(s, "{:?} <- t.remove({:?})\n", t.remove(key), key);
  write!(s, "{:?} <- t.len()\n", t.len());
  write!(s, "{:?} <- t.is_empty()\n", t.is_empty());
  write!(s, "{:?} <- t.contains_key({:?})\n", t.contains_key(key), key);
  write!(s, "{:?} <- t.get({:?})\n", t.get(key), key);
  write!(s, "{:?} <- map::internal::num_slots(&t))\n", map::internal::num_slots(&t));
  write!(s, "{:?} <- map::internal::load_factor(&t))\n", map::internal::load_factor(&t));
  write!(s, "{:?} <- map::internal::allocation_size(&t))\n", map::internal::allocation_size(&t));

  let _ = t.insert(key, 0);
  t.clear();
  let _ = t.insert(key, 0);
  t.reset();

  expect![[r#"
      0 <- t.len()
      true <- t.is_empty()
      false <- t.contains_key(13)
      None <- t.get(13)
      None <- t.get_mut(13)
      0 <- map::internal::num_slots(&t))
      NaN <- map::internal::load_factor(&t))
      0 <- map::internal::allocation_size(&t))
      None <- t.try_insert(13, 40)
      Some(40) <- t.try_insert(13, 41)
      Some(41) <- t.insert(13, 42)
      1 <- t.len()
      false <- t.is_empty()
      true <- t.contains_key(13)
      Some(42) <- t.get(13)
      Some(42) <- t.get_mut(13)
      [] <- t.get_disjoint_mut([])
      [None, Some(42)] <- t.get_disjoint_mut([1, 13])
      Some(42) <- t.remove(13)
      0 <- t.len()
      true <- t.is_empty()
      false <- t.contains_key(13)
      None <- t.get(13)
      20 <- map::internal::num_slots(&t))
      0.0 <- map::internal::load_factor(&t))
      160 <- map::internal::allocation_size(&t))
  "#]].assert_eq(s.drain(..).as_str());
}

#[test]
fn test_empty() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);
  let mut t = IntMap::<NonZeroU32, u64>::with_seed(&mut g);

  let key = NonZeroU32::new(13).unwrap();

  write!(s, "{:?} <- t.len()\n", t.len());
  write!(s, "{:?} <- t.is_empty()\n", t.is_empty());
  write!(s, "{:?} <- t.contains_key({:?})\n", t.contains_key(key), key);
  write!(s, "{:?} <- t.get({:?})\n", t.get(key), key);
  write!(s, "{:?} <- t.get_mut({:?})\n", t.get_mut(key), key);
  write!(s, "{:?} <- map::internal::num_slots(&t))\n", map::internal::num_slots(&t));
  write!(s, "{:?} <- map::internal::load_factor(&t))\n", map::internal::load_factor(&t));
  write!(s, "{:?} <- map::internal::allocation_size(&t))\n", map::internal::allocation_size(&t));

  for _ in t.iter() { panic!() }
  for _ in t.keys() { panic!() }
  for _ in t.values() { panic!() }

  t.clear();
  t.reset();

  expect![[r#"
      0 <- t.len()
      true <- t.is_empty()
      false <- t.contains_key(13)
      None <- t.get(13)
      None <- t.get_mut(13)
      0 <- map::internal::num_slots(&t))
      NaN <- map::internal::load_factor(&t))
      0 <- map::internal::allocation_size(&t))
  "#]].assert_eq(&s.drain(..).as_str());
}

#[test]
fn test_iter() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);
  let mut t = IntMap::with_seed(&mut g);

  for i in 1 ..= 10 {
    let k = NonZeroU32::new(i).unwrap();
    let _ = t.insert(k, 10 * i);
  }

  write!(s, "num_slots = {}\n", map::internal::num_slots(&t));
  write!(s, "load = {}\n", map::internal::load_factor(&t));
  write!(s, "allocation_size = {}\n", map::internal::allocation_size(&t));

  let values = t.values();
  let _ = t.get(NonZeroU32::MIN);
  let mut values = values.collect::<Box<[_]>>();
  values.sort();

  write!(s, "{:?}\n", values);

  expect![[r#"
      num_slots = 40
      load = 0.25
      allocation_size = 320
      [10, 20, 30, 40, 50, 60, 70, 80, 90, 100]
  "#]].assert_eq(&s.drain(..).as_str());

  write!(s, "{:?}\n", t);

  expect![[r#"
      {1: 10, 2: 20, 3: 30, 4: 40, 5: 50, 6: 60, 7: 70, 8: 80, 9: 90, 10: 100}
  "#]].assert_eq(&s.drain(..).as_str());
}

#[test]
fn test_1() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);
  let mut t = IntMap::with_seed(&mut g);

  for i in 1 ..= 100 {
    let k = NonZeroU32::new(i).unwrap();
    let _ = t.insert(k, 10 * i);
  }

  assert!(t.len() == 100);

  write!(s, "len = {}\n", t.len());
  write!(s, "num_slots = {}\n", map::internal::num_slots(&t));
  write!(s, "load = {}\n", map::internal::load_factor(&t));
  write!(s, "allocation_size = {}\n", map::internal::allocation_size(&t));

  for i in 1 ..= 100 {
    let k = NonZeroU32::new(i).unwrap();
    assert!(t.contains_key(k));
  }

  for i in 1 ..= 100 {
    if i & 1 == 0 {
      let k = NonZeroU32::new(i).unwrap();
      assert!(t.remove(k).is_some());
    }
  }

  write!(s, "len = {}\n", t.len());
  write!(s, "num_slots = {}\n", map::internal::num_slots(&t));
  write!(s, "load = {}\n", map::internal::load_factor(&t));
  write!(s, "allocation_size = {}\n", map::internal::allocation_size(&t));

  for i in 1 ..= 100 {
    let k = NonZeroU32::new(i).unwrap();
    write!(s, "{}: {:?}\n", k, t.get(k));
  }

  expect![[r#"
      len = 100
      num_slots = 264
      load = 0.3787878787878788
      allocation_size = 2112
      len = 50
      num_slots = 264
      load = 0.1893939393939394
      allocation_size = 2112
      1: Some(10)
      2: None
      3: Some(30)
      4: None
      5: Some(50)
      6: None
      7: Some(70)
      8: None
      9: Some(90)
      10: None
      11: Some(110)
      12: None
      13: Some(130)
      14: None
      15: Some(150)
      16: None
      17: Some(170)
      18: None
      19: Some(190)
      20: None
      21: Some(210)
      22: None
      23: Some(230)
      24: None
      25: Some(250)
      26: None
      27: Some(270)
      28: None
      29: Some(290)
      30: None
      31: Some(310)
      32: None
      33: Some(330)
      34: None
      35: Some(350)
      36: None
      37: Some(370)
      38: None
      39: Some(390)
      40: None
      41: Some(410)
      42: None
      43: Some(430)
      44: None
      45: Some(450)
      46: None
      47: Some(470)
      48: None
      49: Some(490)
      50: None
      51: Some(510)
      52: None
      53: Some(530)
      54: None
      55: Some(550)
      56: None
      57: Some(570)
      58: None
      59: Some(590)
      60: None
      61: Some(610)
      62: None
      63: Some(630)
      64: None
      65: Some(650)
      66: None
      67: Some(670)
      68: None
      69: Some(690)
      70: None
      71: Some(710)
      72: None
      73: Some(730)
      74: None
      75: Some(750)
      76: None
      77: Some(770)
      78: None
      79: Some(790)
      80: None
      81: Some(810)
      82: None
      83: Some(830)
      84: None
      85: Some(850)
      86: None
      87: Some(870)
      88: None
      89: Some(890)
      90: None
      91: Some(910)
      92: None
      93: Some(930)
      94: None
      95: Some(950)
      96: None
      97: Some(970)
      98: None
      99: Some(990)
      100: None
  "#]].assert_eq(&s);
}

#[test]
fn test_probe_count() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);
  let mut t = IntMap::with_seed(&mut g);

  for i in 1 ..= 512 {
    let k = NonZeroU32::new(i).unwrap();
    let _ = t.insert(k, ());
  }

  write!(s, "num_slots = {}\n", map::internal::num_slots(&t));
  write!(s, "len = {}\n", t.len());
  write!(s, "load_factor = {}\n", map::internal::load_factor(&t));

  for (i, &c) in map::internal::probe_count_histogram(&t).iter().enumerate() {
    write!(s, "{}: {}\n", i, c);
  }

  match hash::internal::BACKEND {
    hash::internal::Backend::AArch64 => {
      expect![[r#"
          num_slots = 1036
          len = 512
          load_factor = 0.4942084942084942
          0: 317
          1: 136
          2: 47
          3: 11
          4: 1
          5: 0
          6: 0
          7: 0
          8: 0
          9: 0
          10: 0
          11: 0
          12: 0
          13: 0
          14: 0
          15: 0
          16: 0
          17: 0
          18: 0
          19: 0
      "#]].assert_eq(&s.drain(..).as_str());
    }
    hash::internal::Backend::Basic => {
      expect![[r#"
          num_slots = 1036
          len = 512
          load_factor = 0.4942084942084942
          0: 285
          1: 146
          2: 56
          3: 19
          4: 6
          5: 0
          6: 0
          7: 0
          8: 0
          9: 0
      "#]].assert_eq(&s.drain(..).as_str());
    }
  }
}


/*

fn key_seq(n: u32) -> NonZeroU32 {
  let n = n | 0x8000_0000;
  let n = n.rotate_left(16);
  unsafe { NonZeroU32::new_unchecked(n) }
}
*/

struct KeyGen {
  state: NonZeroU32,
}

impl KeyGen {
  const fn new() -> Self {
    Self { state: NonZeroU32::MIN }
  }

  fn peek(&self) -> NonZeroU32 {
    self.state
  }

  fn next(&mut self) -> NonZeroU32 {
    let s = self.state;
    let x = s.get().wrapping_mul(5);
    self.state = unsafe { NonZeroU32::new_unchecked(x) };
    s
  }
}

#[cfg(not(miri))]
#[test]
fn test_foo() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);
  let mut t = IntMap::with_seed(&mut g);
  // let mut t = IntMap::new();

  /*
  for i in 0 .. 1_000_000 { let _ = t.insert(key_seq(i), key_seq(i)); }

  for (i, &c) in internal::displacement_histogram(&t).iter().enumerate() {
    write!(s, "{}: {}\n", i, c);
  }

  write!(s, "\n");

  t.reset();
  */

  let mut k = KeyGen::new();
  for _ in 0 .. 1_000_000 { let _ = t.insert(k.next(), k.peek()); }

  for (i, &c) in map::internal::probe_count_histogram(&t).iter().enumerate() {
    write!(s, "{}: {}\n", i, c);
  }

  write!(s, "\n");

  for (i, &c) in map::internal::shift_count_histogram(&t).iter().enumerate() {
    write!(s, "{}: {}\n", i, c);
  }

  expect![[r#"
      0: 670482
      1: 236715
      2: 67958
      3: 18272
      4: 4794
      5: 1318
      6: 367
      7: 81
      8: 9
      9: 3
      10: 1
      11: 0
      12: 0
      13: 0
      14: 0
      15: 0
      16: 0
      17: 0
      18: 0
      19: 0

      0: 670482
      1: 146954
      2: 69658
      3: 39132
      4: 23916
      5: 15357
      6: 10196
      7: 7008
      8: 4809
      9: 3384
      10: 2382
      11: 1756
      12: 1273
      13: 967
      14: 725
      15: 529
      16: 395
      17: 295
      18: 211
      19: 571
  "#]].assert_eq(&s.drain(..).as_str());
}

#[test]
fn test_255u8() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);
  let mut t = IntMap::with_seed(&mut g);

  let mut n = 0;
  for k in NonZeroU8::MIN ..= NonZeroU8::MAX {
    let None = t.insert(k, ()) else { panic!() };
    let m = map::internal::allocation_size(&t);
    if m != n {
      n = m;
      write!(s,
          "len = {}, num_slots = {}, allocation_size = {}\n",
          t.len(),
          map::internal::num_slots(&t),
          map::internal::allocation_size(&t)
        );
    }
  }

  expect![[r#"
      len = 1, num_slots = 20, allocation_size = 20
      len = 9, num_slots = 40, allocation_size = 40
      len = 17, num_slots = 72, allocation_size = 72
      len = 33, num_slots = 136, allocation_size = 136
      len = 65, num_slots = 256, allocation_size = 256
  "#]].assert_eq(&s.drain(..).as_str());
}

#[cfg(not(miri))]
#[test]
fn test_65535u16() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);
  let mut t = IntMap::with_seed(&mut g);

  let mut n = 0;
  for k in NonZeroU16::MIN ..= NonZeroU16::MAX {
    let None = t.insert(k, ()) else { panic!() };
    let m = map::internal::allocation_size(&t);
    if m != n || k == NonZeroU16::MAX {
      n = m;
      write!(s,
          "len = {}, num_slots = {}, allocation_size = {}\n",
          t.len(),
          map::internal::num_slots(&t),
          map::internal::allocation_size(&t)
        );
    }
  }

  expect![[r#"
      len = 1, num_slots = 20, allocation_size = 40
      len = 9, num_slots = 40, allocation_size = 80
      len = 17, num_slots = 72, allocation_size = 144
      len = 33, num_slots = 136, allocation_size = 272
      len = 65, num_slots = 264, allocation_size = 528
      len = 129, num_slots = 524, allocation_size = 1048
      len = 257, num_slots = 1036, allocation_size = 2072
      len = 513, num_slots = 2060, allocation_size = 4120
      len = 1025, num_slots = 4108, allocation_size = 8216
      len = 2049, num_slots = 8208, allocation_size = 16416
      len = 4097, num_slots = 16400, allocation_size = 32800
      len = 8193, num_slots = 32784, allocation_size = 65568
      len = 16385, num_slots = 65536, allocation_size = 131072
      len = 65535, num_slots = 65536, allocation_size = 131072
  "#]].assert_eq(&s.drain(..).as_str());
}
