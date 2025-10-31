use expect_test::expect;
use std::fmt::Write;
use std::num::NonZeroU64;
use std::write;
use tangerine::map::HashMap;
use dandelion::Rng;

#[test]
fn test_basic() -> Result<(), std::fmt::Error> {
  let mut s = String::new();
  let mut g = Rng::from_u64(0);
  let mut t = HashMap::new_seeded(&mut g);

  let key = NonZeroU64::new(13).unwrap();

  write!(s, "{:?} <- t.len()\n", t.len())?;
  write!(s, "{:?} <- t.is_empty()\n", t.is_empty())?;
  write!(s, "{:?} <- t.contains_key({:?})\n", t.contains_key(key), key)?;
  write!(s, "{:?} <- t.get({:?})\n", t.get(key), key)?;
  write!(s, "{:?} <- t.get_mut({:?})\n", t.get_mut(key), key)?;
  write!(s, "{:?} <- t.insert({:?}, {:?})\n", t.insert(key, 42), key, 42)?;
  write!(s, "{:?} <- t.len()\n", t.len())?;
  write!(s, "{:?} <- t.is_empty()\n", t.is_empty())?;
  write!(s, "{:?} <- t.contains_key({:?})\n", t.contains_key(key), key)?;
  write!(s, "{:?} <- t.get({:?})\n", t.get(key), key)?;
  write!(s, "{:?} <- t.get_mut({:?})\n", t.get_mut(key), key)?;
  write!(s, "{:?} <- t.remove({:?})\n", t.remove(key), key)?;
  write!(s, "{:?} <- t.len()\n", t.len())?;
  write!(s, "{:?} <- t.is_empty()\n", t.is_empty())?;
  write!(s, "{:?} <- t.contains_key({:?})\n", t.contains_key(key), key)?;
  write!(s, "{:?} <- t.get({:?})\n", t.get(key), key)?;
  write!(s, "{:?} <- t.get_mut({:?})\n", t.get_mut(key), key)?;

  expect![[r#"
      0 <- t.len()
      true <- t.is_empty()
      false <- t.contains_key(13)
      None <- t.get(13)
      None <- t.get_mut(13)
      None <- t.insert(13, 42)
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
      None <- t.get_mut(13)
  "#]].assert_eq(&s);

  Ok(())
}

#[test]
fn foo() -> Result<(), std::fmt::Error> {
  let mut g = Rng::from_u64(0);
  let mut s = String::new();
  let mut t = HashMap::<NonZeroU64, u64>::new_seeded(&mut g);

  for i in 1 ..= 100 {
    let k = NonZeroU64::new(i).unwrap();
    let _ = t.insert(k, 10 * i);
  }

  write!(s, "len = {}\n", t.len())?;
  write!(s, "num_slots = {}\n", tangerine::map::internal::num_slots(&t))?;
  write!(s, "load = {}\n", tangerine::map::internal::load_factor(&t))?;
  write!(s, "allocation_size = {}\n", tangerine::map::internal::allocation_size(&t))?;

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

  write!(s, "len = {}\n", t.len())?;
  write!(s, "num_slots = {}\n", tangerine::map::internal::num_slots(&t))?;
  write!(s, "load = {}\n", tangerine::map::internal::load_factor(&t))?;
  write!(s, "allocation_size = {}\n", tangerine::map::internal::allocation_size(&t))?;

  for i in 1 ..= 100 {
    let k = NonZeroU64::new(i).unwrap();
    if let Some(v) = t.get(k) {
      write!(s, "{}: {}\n", k, v)?;
    }
  }

  expect![[r#"
      len = 100
      num_slots = 384
      load = 0.2604166666666667
      allocation_size = 6144
      len = 50
      num_slots = 384
      load = 0.13020833333333334
      allocation_size = 6144
      1: 10
      3: 30
      5: 50
      7: 70
      9: 90
      11: 110
      13: 130
      15: 150
      17: 170
      19: 190
      21: 210
      23: 230
      25: 250
      27: 270
      29: 290
      31: 310
      33: 330
      35: 350
      37: 370
      39: 390
      41: 410
      43: 430
      45: 450
      47: 470
      49: 490
      51: 510
      53: 530
      55: 550
      57: 570
      59: 590
      61: 610
      63: 630
      65: 650
      67: 670
      69: 690
      71: 710
      73: 730
      75: 750
      77: 770
      79: 790
      81: 810
      83: 830
      85: 850
      87: 870
      89: 890
      91: 910
      93: 930
      95: 950
      97: 970
      99: 990
  "#]].assert_eq(&s);

  Ok(())
}

#[test]
fn test_iter() -> Result<(), std::fmt::Error> {
  let mut s = String::new();
  let mut t = HashMap::new();

  for i in 1 ..= 10 {
    let k = NonZeroU64::new(i).unwrap();
    let _ = t.insert(k, 10 * i);
  }

  let values = t.values();
  let _ = t.get(NonZeroU64::new(1).unwrap());
  let mut values = values.collect::<Vec<_>>();
  values.sort();

  write!(s, "{:?}\n", values)?;

  expect![[r#"
      [10, 20, 30, 40, 50, 60, 70, 80, 90, 100]
  "#]].assert_eq(&s);

  Ok(())
}
