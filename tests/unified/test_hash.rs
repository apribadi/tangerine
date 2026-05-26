#![allow(unused_must_use)]

use dandelion::Rng;
use expect_test::expect;
use std::iter;
use std::fmt::Write;
use std::num::NonZeroU128;
use std::write;
use tangerine::hash;

#[test]
fn test_hash_u8() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);

  let t = hash::internal::Hash8::with_seed(&mut g);

  for x in iter::chain([0], iter::repeat_with(|| g.u64() as u8).take(10)) {
    let y = t.hash(x);
    let z = t.invert_hash(y);
    let d = x ^ z;
    write!(s, "{:#04x} {:#04x} {:#04x} {:#04x}\n", x, y, z, d);
  }

  match hash::internal::BACKEND {
    hash::internal::Backend::AArch64 => {
      expect![[r#"
          0x00 0xff 0x00 0x00
          0x84 0xa4 0x84 0x00
          0x24 0x06 0x24 0x00
          0xae 0x4d 0xae 0x00
          0xa4 0xc4 0xa4 0x00
          0x46 0x86 0x46 0x00
          0x78 0x9a 0x78 0x00
          0x3a 0xfa 0x3a 0x00
          0x19 0x67 0x19 0x00
          0xb7 0xa5 0xb7 0x00
          0x29 0x57 0x29 0x00
      "#]].assert_eq(&s.drain(..).as_str());
    }
    hash::internal::Backend::Generic => {
      expect![[r#"
      "#]].assert_eq(&s.drain(..).as_str());
    }
  }
}

#[test]
fn test_hash() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);

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
          0x00000000 0xffffffff 0x00000000 0x00000000
          0x0cda5a84 0x2a7b3c0c 0x0cda5a84 0x00000000
          0xd541b224 0xf8493beb 0xd541b224 0x00000000
          0x3f24c4ae 0x3d0f6a8a 0x3f24c4ae 0x00000000
          0xac246ba4 0x3710a313 0xac246ba4 0x00000000
          0xcab9f146 0xefd52ce5 0xcab9f146 0x00000000
          0x85fca478 0x5b7e3603 0x85fca478 0x00000000
          0xaf7f073a 0x143d4e3f 0xaf7f073a 0x00000000
          0xeea3aa19 0xb3b7c142 0xeea3aa19 0x00000000
          0xd8b677b7 0xd227eb20 0xd8b677b7 0x00000000
          0xd9ad5229 0xa8c5fe83 0xd9ad5229 0x00000000
          0x0000000000000000 0xffffffffffffffff 0x0000000000000000 0x0000000000000000
          0x57f78f5dfff0a290 0x0d03fbd8c0d7588f 0x57f78f5dfff0a290 0x0000000000000000
          0x3e4b32845074d8fd 0x731ac2f04d7e83dc 0x3e4b32845074d8fd 0x0000000000000000
          0x4a165da67f91ccc4 0x8e06d03fda808643 0x4a165da67f91ccc4 0x0000000000000000
          0x2c44afca8ef5ed81 0xcf5fdd44a53a39e0 0x2c44afca8ef5ed81 0x0000000000000000
          0xb74aff78c1bf3aca 0xa99b8e9fd6c69e89 0xb74aff78c1bf3aca 0x0000000000000000
          0x3ada70ecaa882eb0 0xcdd26159113af0af 0x3ada70ecaa882eb0 0x0000000000000000
          0x8e08d57f338296e8 0x9962846f81c18de7 0x8e08d57f338296e8 0x0000000000000000
          0x28c8426d0b11f3ee 0xfc37a02e1b27352d 0x28c8426d0b11f3ee 0x0000000000000000
          0x8500faf5a7e4edc4 0xeafaded79ebc0743 0x8500faf5a7e4edc4 0x0000000000000000
          0x50ad8d427f8a958c 0xed87ca815e9b7a0b 0x50ad8d427f8a958c 0x0000000000000000
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
