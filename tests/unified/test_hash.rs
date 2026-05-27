#![allow(unused_must_use)]

use dandelion::Rng;
use expect_test::expect;
use std::fmt::Write;
use std::iter;
use std::num::NonZeroU128;
use std::write;
use tangerine::hash::internal::BACKEND;
use tangerine::hash::internal::Backend;
use tangerine::hash::internal::Hash;
use tangerine::hash::internal::HashU8;
use tangerine::hash::internal::HashU32;
use tangerine::hash::internal::HashU64;

#[test]
fn test_hash_u8() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);

  let t = HashU8::new(&mut g);

  for x in iter::chain(0 .. 10, iter::repeat_with(|| g.u32() as u8).take(10)) {
    let y = t.hash(x);
    let z = t.invert_hash(y);
    write!(s, "{:#04x} {:#04x} {:#04x}\n", x, y, x ^ z);
  }

  match BACKEND {
    Backend::AArch64 => {
      expect![[r#"
          0x00 0xff 0x00
          0x01 0xb1 0x00
          0x02 0xc0 0x00
          0x03 0xb2 0x00
          0x04 0xe6 0x00
          0x05 0x94 0x00
          0x06 0x65 0x00
          0x07 0x53 0x00
          0x08 0x49 0x00
          0x09 0x77 0x00
          0x84 0xa4 0x00
          0x24 0x06 0x00
          0xae 0x4d 0x00
          0xa4 0xc4 0x00
          0x46 0x86 0x00
          0x78 0x9a 0x00
          0x3a 0xfa 0x00
          0x19 0x67 0x00
          0xb7 0xa5 0x00
          0x29 0x57 0x00
      "#]].assert_eq(&s.drain(..).as_str());
    }
    Backend::Basic => {
      expect![[r#"
          0x00 0xff 0x00
          0x01 0xb1 0x00
          0x02 0xc0 0x00
          0x03 0xb2 0x00
          0x04 0xe6 0x00
          0x05 0x94 0x00
          0x06 0x65 0x00
          0x07 0x53 0x00
          0x08 0x49 0x00
          0x09 0x77 0x00
          0x84 0xa4 0x00
          0x24 0x06 0x00
          0xae 0x4d 0x00
          0xa4 0xc4 0x00
          0x46 0x86 0x00
          0x78 0x9a 0x00
          0x3a 0xfa 0x00
          0x19 0x67 0x00
          0xb7 0xa5 0x00
          0x29 0x57 0x00
      "#]].assert_eq(&s.drain(..).as_str());
    }
  }
}

#[test]
fn test_hash_u32() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);

  let t = HashU32::new(&mut g);

  for x in iter::chain(0 .. 10, iter::repeat_with(|| g.u32()).take(10)) {
    let y = t.hash(x);
    let z = t.invert_hash(y);
    write!(s, "{:#010x} {:#010x} {:#010x}\n", x, y, x ^ z);
  }

  match BACKEND {
    Backend::AArch64 => {
      expect![[r#"
          0x00000000 0xffffffff 0x00000000
          0x00000001 0xbb6a2bb7 0x00000000
          0x00000002 0x934ef060 0x00000000
          0x00000003 0xe2867718 0x00000000
          0x00000004 0x241e5a92 0x00000000
          0x00000005 0xaf0c90ea 0x00000000
          0x00000006 0xc50cee31 0x00000000
          0x00000007 0x53b2c189 0x00000000
          0x00000008 0x483cb525 0x00000000
          0x00000009 0xbd87039d 0x00000000
          0x0cda5a84 0x2a7b3c0c 0x00000000
          0xd541b224 0xf8493beb 0x00000000
          0x3f24c4ae 0x3d0f6a8a 0x00000000
          0xac246ba4 0x3710a313 0x00000000
          0xcab9f146 0xefd52ce5 0x00000000
          0x85fca478 0x5b7e3603 0x00000000
          0xaf7f073a 0x143d4e3f 0x00000000
          0xeea3aa19 0xb3b7c142 0x00000000
          0xd8b677b7 0xd227eb20 0x00000000
          0xd9ad5229 0xa8c5fe83 0x00000000
      "#]].assert_eq(&s.drain(..).as_str());
    }
    Backend::Basic => {
      expect![[r#"
          0x00000000 0xffffffff 0x00000000
          0x00000001 0xecabb44d 0x00000000
          0x00000002 0x37d76d9b 0x00000000
          0x00000003 0xc324a1e4 0x00000000
          0x00000004 0x0e505b32 0x00000000
          0x00000005 0x19a28f7b 0x00000000
          0x00000006 0x8b4943c9 0x00000000
          0x00000007 0x969b7812 0x00000000
          0x00000008 0x61c23160 0x00000000
          0x00000009 0x6d1465a9 0x00000000
          0x0cda5a84 0x044d168f 0x00000000
          0xd541b224 0xad99f459 0x00000000
          0x3f24c4ae 0x31ba7fba 0x00000000
          0xac246ba4 0x2d6ac716 0x00000000
          0xcab9f146 0xcd5ce86e 0x00000000
          0x85fca478 0xa3196b75 0x00000000
          0xaf7f073a 0xc94e544f 0x00000000
          0xeea3aa19 0x7d5bb63e 0x00000000
          0xd8b677b7 0x41e3e7e5 0x00000000
          0xd9ad5229 0x180a45c7 0x00000000
      "#]].assert_eq(&s.drain(..).as_str());
    }
  }
}

#[test]
fn test_hash_u64() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);

  let t = HashU64::new(&mut g);

  for x in iter::chain(0 .. 10, iter::repeat_with(|| g.u64()).take(10)) {
    let y = t.hash(x);
    let z = t.invert_hash(y);
    write!(s, "{:#018x} {:#018x} {:#018x}\n", x, y, x ^ z);
  }

  match BACKEND {
    Backend::AArch64 => {
      expect![[r#"
          0x0000000000000000 0xffffffffffffffff 0x0000000000000000
          0x0000000000000001 0x1f8e2342ce96bce0 0x0000000000000000
          0x0000000000000002 0x3f1c46859d2d79c1 0x0000000000000000
          0x0000000000000003 0xbc169f3c6bc436a2 0x0000000000000000
          0x0000000000000004 0x631badbc3a5af383 0x0000000000000000
          0x0000000000000005 0xb7df37f508f1b064 0x0000000000000000
          0x0000000000000006 0x76b34aa9d7886d45 0x0000000000000000
          0x0000000000000007 0xe6aed866a61f2a26 0x0000000000000000
          0x0000000000000008 0xc6375b7874b5e707 0x0000000000000000
          0x0000000000000009 0xd3138337434ca3e8 0x0000000000000000
          0x03f517a50cda5a84 0x293cafe3e7ba7e03 0x0000000000000000
          0x70738695d541b224 0x60c4c98506a801a3 0x0000000000000000
          0x46d86ef73f24c4ae 0x2aae207ac1b4a4ed 0x0000000000000000
          0x0fdd2ff9ac246ba4 0x600cd33215270b23 0x0000000000000000
          0x5a840d25cab9f146 0xfc40c8a96da07685 0x0000000000000000
          0x1965353a85fca478 0x69d685023a24ad77 0x0000000000000000
          0x61ecfcb4af7f073a 0x6a57e6176feff1f9 0x0000000000000000
          0x502e03cfeea3aa19 0x8c23eb5cb768dbf8 0x0000000000000000
          0x571f6003d8b677b7 0xf3fbe384df839bd6 0x0000000000000000
          0xd375dcd8d9ad5229 0x2c4a5ef9bbb15208 0x0000000000000000
      "#]].assert_eq(&s.drain(..).as_str());
    }
    Backend::Basic => {
      expect![[r#"
          0x0000000000000000 0xffffffffffffffff 0x0000000000000000
          0x0000000000000001 0xa6567dae60b6c377 0x0000000000000000
          0x0000000000000002 0xfc8c805cc16d86ef 0x0000000000000000
          0x0000000000000003 0xf167e85ad479a4ec 0x0000000000000000
          0x0000000000000004 0xbcf5bb63ba306864 0x0000000000000000
          0x0000000000000005 0x132bbe121ae72bdc 0x0000000000000000
          0x0000000000000006 0x080726102df349d9 0x0000000000000000
          0x0000000000000007 0x6907db13e92f0d51 0x0000000000000000
          0x0000000000000008 0x3495ae1ccee5d0c9 0x0000000000000000
          0x0000000000000009 0x1ef6e0cd374c73c6 0x0000000000000000
          0x70738695d541b224 0x96e6c4c5c2404107 0x0000000000000000
          0x46d86ef73f24c4ae 0x9b7f183c42099290 0x0000000000000000
          0x0fdd2ff9ac246ba4 0xdb85a9e90abe76d7 0x0000000000000000
          0x5a840d25cab9f146 0xa8382fd54f5e6a70 0x0000000000000000
          0x1965353a85fca478 0x2fa1053c94f1daa1 0x0000000000000000
          0x61ecfcb4af7f073a 0xa3e9aff3a9dbd24f 0x0000000000000000
          0x502e03cfeea3aa19 0x8a1a0245122340ad 0x0000000000000000
          0x571f6003d8b677b7 0x2597c1dbad55441f 0x0000000000000000
          0xd375dcd8d9ad5229 0xcb55186552310e0f 0x0000000000000000
          0xd91e4ed618e13c60 0x7819e1c971221e0f 0x0000000000000000
      "#]].assert_eq(&s.drain(..).as_str());
    }
  }
}
