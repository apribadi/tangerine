#![allow(unused_must_use)]

use dandelion::Rng;
use expect_test::expect;
use std::iter;
use std::fmt::Write;
use std::num::NonZeroU128;
use std::num::NonZeroU32;
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
fn test_displacement_histogram() {
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

  for (i, &c) in map::internal::displacement_histogram(&t).iter().enumerate() {
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
      "#]].assert_eq(&s.drain(..).as_str());
    }
    hash::internal::Backend::Generic => {
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

#[test]
fn test_hash() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);

  let t = hash::internal::Hash8::with_seed(&mut g);

  for x in iter::chain([0], iter::repeat_with(|| g.u64() as u8).take(10)) {
    let y = t.hash(x);
    let z = t.invert_hash(y);
    let d = x ^ z;
    write!(s, "{:#04x} {:#04x} {:#04x} {:#04x}\n", x, y, z, d);
  }

  let t = hash::internal::Hash32::with_seed(&mut g);

  for x in iter::chain([0], iter::repeat_with(|| g.u32()).take(10)) {
    let y = t.hash(x);
    let z = t.invert_hash(y);
    let d = x ^ z;
    write!(s, "{:#010x} {:#010x} {:#010x} {:#010x}\n", x, y, z, d);
  }

  let t = hash::internal::Hash64::with_seed(&mut g);

  for x in iter::chain([0], iter::repeat_with(|| g.u64()).take(10)) {
    let y = t.hash(x);
    let z = t.invert_hash(y);
    let d = x ^ z;
    write!(s, "{:#018x} {:#018x} {:#018x} {:#018x}\n", x, y, z, d);
  }

  match hash::internal::BACKEND {
    hash::internal::Backend::AArch64 => {
      expect![[r#"
          0x00 0xff 0x00 0x00
          0xe1 0x94 0xe1 0x00
          0x84 0xfb 0x84 0x00
          0x24 0xd2 0x24 0x00
          0xae 0x80 0xae 0x00
          0xa4 0xe5 0xa4 0x00
          0x46 0xf6 0x46 0x00
          0x78 0x58 0x78 0x00
          0x3a 0x1c 0x3a 0x00
          0x19 0x70 0x19 0x00
          0xb7 0x45 0xb7 0x00
          0x00000000 0xffffffff 0x00000000 0x00000000
          0x18e13c60 0xe95781cc 0x18e13c60 0x00000000
          0xfff0a290 0x9961440e 0xfff0a290 0x00000000
          0x5074d8fd 0x94b6454d 0x5074d8fd 0x00000000
          0x7f91ccc4 0x012ef487 0x7f91ccc4 0x00000000
          0x8ef5ed81 0x186e3d71 0x8ef5ed81 0x00000000
          0xc1bf3aca 0x212bf010 0xc1bf3aca 0x00000000
          0xaa882eb0 0xd37f6a0f 0xaa882eb0 0x00000000
          0x338296e8 0x14e8c020 0x338296e8 0x00000000
          0x0b11f3ee 0xb7eb9e04 0x0b11f3ee 0x00000000
          0xa7e4edc4 0x13b4b0f9 0xa7e4edc4 0x00000000
          0x0000000000000000 0xffffffffffffffff 0x0000000000000000 0x0000000000000000
          0x8c3a32205b615928 0x2b67feb4e5126307 0x8c3a32205b615928 0x0000000000000000
          0x3f295f13110403c3 0x563ab39a79849166 0x3f295f13110403c3 0x0000000000000000
          0xc8e20217f12e2a3d 0xb4a87448bce4c498 0xc8e20217f12e2a3d 0x0000000000000000
          0x0cfd5586d4304dba 0x0d9cceea281c1171 0x0cfd5586d4304dba 0x0000000000000000
          0x10ffc9e8dec10f2e 0xf11cc13d0ef72255 0x10ffc9e8dec10f2e 0x0000000000000000
          0x39b241679c0ed812 0x76bf867bffa37be9 0x39b241679c0ed812 0x0000000000000000
          0xdf0c3f39cf93c05e 0xaa88ade4a803a9c5 0xdf0c3f39cf93c05e 0x0000000000000000
          0x88a33e396ff153dd 0x4912731cf5dcd1b8 0x88a33e396ff153dd 0x0000000000000000
          0x55124ccd6a441b50 0x6cc6393b94889b0f 0x55124ccd6a441b50 0x0000000000000000
          0x3ab2e9040397396f 0x88b35f4d058e3d22 0x3ab2e9040397396f 0x0000000000000000
      "#]].assert_eq(&s.drain(..).as_str());
    }
    hash::internal::Backend::Generic => {
      expect![[r#"
          0x00000000 0xffffffff 0x00000000 0x00000000
          0x0cda5a84 0x044d168f 0x0cda5a84 0x00000000
          0xd541b224 0xad99f459 0xd541b224 0x00000000
          0x3f24c4ae 0x31ba7fba 0x3f24c4ae 0x00000000
          0xac246ba4 0x2d6ac716 0xac246ba4 0x00000000
          0xcab9f146 0xcd5ce86e 0xcab9f146 0x00000000
          0x85fca478 0xa3196b75 0x85fca478 0x00000000
          0xaf7f073a 0xc94e544f 0xaf7f073a 0x00000000
          0xeea3aa19 0x7d5bb63e 0xeea3aa19 0x00000000
          0xd8b677b7 0x41e3e7e5 0xd8b677b7 0x00000000
          0xd9ad5229 0x180a45c7 0xd9ad5229 0x00000000
          0x0000000000000000 0xffffffffffffffff 0x0000000000000000 0x0000000000000000
          0x3e4b32845074d8fd 0xda8a962d6066de19 0x3e4b32845074d8fd 0x0000000000000000
          0x4a165da67f91ccc4 0x28a1dc40f24f3972 0x4a165da67f91ccc4 0x0000000000000000
          0x2c44afca8ef5ed81 0x8e014da1d955fc64 0x2c44afca8ef5ed81 0x0000000000000000
          0xb74aff78c1bf3aca 0xdc789a85c85b7119 0xb74aff78c1bf3aca 0x0000000000000000
          0x3ada70ecaa882eb0 0xeef50408dce298ec 0x3ada70ecaa882eb0 0x0000000000000000
          0x8e08d57f338296e8 0x41dacb1894fa9a40 0x8e08d57f338296e8 0x0000000000000000
          0x28c8426d0b11f3ee 0xa3247c14292e7948 0x28c8426d0b11f3ee 0x0000000000000000
          0x8500faf5a7e4edc4 0x2285863751f15969 0x8500faf5a7e4edc4 0x0000000000000000
          0x50ad8d427f8a958c 0x57712fc6baf702d1 0x50ad8d427f8a958c 0x0000000000000000
          0x8c3a32205b615928 0x2596ab9017c0a2ea 0x8c3a32205b615928 0x0000000000000000
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

#[test]
fn test_foo() {
  let mut s = String::new();
  // let mut g = Rng::new(NonZeroU128::MIN);
  // let mut g = Rng::new(NonZeroU128::new(2).unwrap());
  // let mut t = IntMap::with_seed(&mut g);
  let mut t = IntMap::new();

  for i in 0 .. 1_000_000 { let _ = t.insert(key_seq(i), key_seq(i)); }

  for (i, &c) in internal::displacement_histogram(&t).iter().enumerate() {
    write!(s, "{}: {}\n", i, c);
  }

  write!(s, "\n");

  t.reset();

  let mut k = KeyGen::new();
  for _ in 0 .. 1_000_000 { let _ = t.insert(k.next(), k.peek()); }

  for (i, &c) in internal::displacement_histogram(&t).iter().enumerate() {
    write!(s, "{}: {}\n", i, c);
  }

  expect![[r#"
  "#]].assert_eq(&s.drain(..).as_str());

}
*/

