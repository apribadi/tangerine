#![allow(unused_must_use)]

use dandelion::Rng;
use expect_test::expect;
use std::fmt::Write;
use std::num::NonZeroU64;
use std::num::NonZeroU128;
use std::write;
use tangerine::map::IntMap;
use tangerine::map::internal;

/*
#[test]
fn test_lifetime() {
  let mut g = Rng::new(NonZeroU128::MIN);
  let mut t = IntMap::with_seed(&mut g);
  let key = NonZeroU64::new(13).unwrap();
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

  let key = NonZeroU64::new(13).unwrap();

  write!(s, "{:?} <- t.len()\n", t.len());
  write!(s, "{:?} <- t.is_empty()\n", t.is_empty());
  write!(s, "{:?} <- t.contains_key({:?})\n", t.contains_key(key), key);
  write!(s, "{:?} <- t.get({:?})\n", t.get(key), key);
  write!(s, "{:?} <- t.get_mut({:?})\n", t.get_mut(key), key);
  write!(s, "{:?} <- internal::num_slots(&t))\n", internal::num_slots(&t));
  write!(s, "{:?} <- internal::load_factor(&t))\n", internal::load_factor(&t));
  write!(s, "{:?} <- internal::allocation_size(&t))\n", internal::allocation_size(&t));
  write!(s, "{:?} <- t.try_insert({:?}, {:?})\n", t.insert(key, 40), key, 40);
  write!(s, "{:?} <- t.try_insert({:?}, {:?})\n", t.insert(key, 41), key, 41);
  write!(s, "{:?} <- t.insert({:?}, {:?})\n", t.insert(key, 42), key, 42);
  write!(s, "{:?} <- t.len()\n", t.len());
  write!(s, "{:?} <- t.is_empty()\n", t.is_empty());
  write!(s, "{:?} <- t.contains_key({:?})\n", t.contains_key(key), key);
  write!(s, "{:?} <- t.get({:?})\n", t.get(key), key);
  write!(s, "{:?} <- t.get_mut({:?})\n", t.get_mut(key), key);
  write!(s, "{:?} <- t.remove({:?})\n", t.remove(key), key);
  write!(s, "{:?} <- t.len()\n", t.len());
  write!(s, "{:?} <- t.is_empty()\n", t.is_empty());
  write!(s, "{:?} <- t.contains_key({:?})\n", t.contains_key(key), key);
  write!(s, "{:?} <- t.get({:?})\n", t.get(key), key);
  write!(s, "{:?} <- internal::num_slots(&t))\n", internal::num_slots(&t));
  write!(s, "{:?} <- internal::load_factor(&t))\n", internal::load_factor(&t));
  write!(s, "{:?} <- internal::allocation_size(&t))\n", internal::allocation_size(&t));

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
      0 <- internal::num_slots(&t))
      NaN <- internal::load_factor(&t))
      0 <- internal::allocation_size(&t))
      None <- t.try_insert(13, 40)
      Some(40) <- t.try_insert(13, 41)
      Some(41) <- t.insert(13, 42)
      1 <- t.len()
      false <- t.is_empty()
      true <- t.contains_key(13)
      Some(42) <- t.get(13)
      Some(42) <- t.get_mut(13)
      Some(42) <- t.remove(13)
      0 <- t.len()
      true <- t.is_empty()
      false <- t.contains_key(13)
      None <- t.get(13)
      20 <- internal::num_slots(&t))
      0.0 <- internal::load_factor(&t))
      240 <- internal::allocation_size(&t))
  "#]].assert_eq(s.drain(..).as_str());
}

#[test]
fn test_empty() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);
  let mut t = IntMap::<NonZeroU64, u64>::with_seed(&mut g);

  let key = NonZeroU64::new(13).unwrap();

  write!(s, "{:?} <- t.len()\n", t.len());
  write!(s, "{:?} <- t.is_empty()\n", t.is_empty());
  write!(s, "{:?} <- t.contains_key({:?})\n", t.contains_key(key), key);
  write!(s, "{:?} <- t.get({:?})\n", t.get(key), key);
  write!(s, "{:?} <- t.get_mut({:?})\n", t.get_mut(key), key);
  write!(s, "{:?} <- internal::num_slots(&t))\n", internal::num_slots(&t));
  write!(s, "{:?} <- internal::load_factor(&t))\n", internal::load_factor(&t));
  write!(s, "{:?} <- internal::allocation_size(&t))\n", internal::allocation_size(&t));

  for _ in t.iter() { panic!() }
  for _ in t.keys() { panic!() }
  for _ in t.values() { panic!() }

  t.clear();
  t.reset();
}

#[test]
fn test_iter() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);
  let mut t = IntMap::with_seed(&mut g);

  for i in 1 ..= 10 {
    let k = NonZeroU64::new(i).unwrap();
    let _ = t.insert(k, 10 * i);
  }

  write!(s, "num_slots = {}\n", internal::num_slots(&t));
  write!(s, "load = {}\n", internal::load_factor(&t));
  write!(s, "allocation_size = {}\n", internal::allocation_size(&t));

  let values = t.values();
  let _ = t.get(NonZeroU64::new(1).unwrap());
  let mut values = values.collect::<Box<[_]>>();
  values.sort();

  write!(s, "{:?}\n", values);

  expect![[r#"
      num_slots = 40
      load = 0.25
      allocation_size = 640
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
    let k = NonZeroU64::new(i).unwrap();
    let _ = t.insert(k, 10 * i);
  }

  assert!(t.len() == 100);

  write!(s, "len = {}\n", t.len());
  write!(s, "num_slots = {}\n", internal::num_slots(&t));
  write!(s, "load = {}\n", internal::load_factor(&t));
  write!(s, "allocation_size = {}\n", internal::allocation_size(&t));

  for i in 1 ..= 100 {
    let k = NonZeroU64::new(i).unwrap();
    assert!(t.contains_key(k));
  }

  for i in 1 ..= 100 {
    if i & 1 == 0 {
      let k = NonZeroU64::new(i).unwrap();
      assert!(t.remove(k).is_some());
    }
  }

  write!(s, "len = {}\n", t.len());
  write!(s, "num_slots = {}\n", internal::num_slots(&t));
  write!(s, "load = {}\n", internal::load_factor(&t));
  write!(s, "allocation_size = {}\n", internal::allocation_size(&t));

  for i in 1 ..= 100 {
    let k = NonZeroU64::new(i).unwrap();
    write!(s, "{}: {:?}\n", k, t.get(k));
  }

  expect![[r#"
      len = 100
      num_slots = 264
      load = 0.3787878787878788
      allocation_size = 4224
      len = 50
      num_slots = 264
      load = 0.1893939393939394
      allocation_size = 4224
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

fn sizes_from_working_set(working_set: usize) -> [usize; 10] {
  let n: [usize; 10] = [
    500,
    535,
    574,
    615,
    659,
    707,
    757,
    812,
    870,
    933,
  ];
  let mut a = 0;
  for &n in &n { a += n; }
  let mut r = [0; 10];
  let mut b = 0;
  for i in 0 .. 9 { r[i] = n[i] * working_set / a; b += r[i]; }
  r[9] = working_set - b;
  r
}

#[test]
fn test_working_set() {
  let mut s = String::new();
  write!(s, "{:?}\n", sizes_from_working_set(10_000));
  write!(s, "{:?}\n", sizes_from_working_set(10_000).iter().sum::<usize>());
  expect![[r#"
      [718, 768, 824, 883, 946, 1015, 1087, 1166, 1249, 1344]
      10000
  "#]].assert_eq(&s.drain(..).as_str());
}

#[test]
fn test_displacement_histogram() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);
  let mut t = IntMap::with_seed(&mut g);

  for i in 1 ..= 128 {
    let k = NonZeroU64::new(i).unwrap();
    let _ = t.insert(k, ());
  }

  write!(s, "num_slots = {}\n", internal::num_slots(&t));
  write!(s, "len = {}\n", t.len());
  write!(s, "load_factor = {}\n", internal::load_factor(&t));

  for (i, &c) in internal::displacement_histogram(&t).iter().enumerate() {
    write!(s, "{}: {}\n", i, c);
  }

  expect![[r#"
      num_slots = 264
      len = 128
      load_factor = 0.48484848484848486
      0: 79
      1: 35
      2: 9
      3: 3
      4: 1
      5: 1
      6: 0
      7: 0
      8: 0
      9: 0
  "#]].assert_eq(&s.drain(..).as_str());
}
