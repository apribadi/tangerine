#![allow(unused_must_use)]

use dandelion::Rng;
use expect_test::expect;
use std::fmt::Write;
use std::iter;
use std::num::NonZeroU128;
use std::write;
use tangerine::key::internal::BACKEND;
use tangerine::key::internal::Backend;
use tangerine::key::internal::hash_u8;
use tangerine::key::internal::hash_u16;
use tangerine::key::internal::hash_u32;
use tangerine::key::internal::hash_u64;
use tangerine::key::internal::invert_hash_u8;
use tangerine::key::internal::invert_hash_u16;
use tangerine::key::internal::invert_hash_u32;
use tangerine::key::internal::invert_hash_u64;

#[test]
fn test_hash_u8() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);

  for x in iter::chain(0 .. 10, iter::repeat_with(|| g.uniform::<u8>()).take(10)) {
    let y = hash_u8(x);
    let z = invert_hash_u8(y);
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
          0xe1 0xf0 0x00
          0x31 0x81 0x00
          0x58 0x7a 0x00
          0x98 0x17 0x00
          0x80 0x41 0x00
          0x4e 0x4c 0x00
          0x50 0x30 0x00
          0x9a 0xd8 0x00
          0xc5 0x35 0x00
          0x21 0x91 0x00
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
fn test_hash_u16() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);

  for x in iter::chain(0 .. 10, iter::repeat_with(|| g.uniform::<u16>()).take(10)) {
    let y = hash_u16(x);
    let z = invert_hash_u16(y);
    write!(s, "{:#06x} {:#06x} {:#06x}\n", x, y, x ^ z);
  }

  match BACKEND {
    Backend::AArch64 => {
      expect![[r#"
          0x0000 0xffff 0x0000
          0x0001 0x3961 0x0000
          0x0002 0x2fa4 0x0000
          0x0003 0x2306 0x0000
          0x0004 0x5f49 0x0000
          0x0005 0x4027 0x0000
          0x0006 0x02ee 0x0000
          0x0007 0xa5cc 0x0000
          0x0008 0xbe93 0x0000
          0x0009 0x15f5 0x0000
          0xbce1 0xe14a 0x0000
          0xdc31 0xa9fb 0x0000
          0xdb58 0x501b 0x0000
          0x5b98 0x9ffd 0x0000
          0xd380 0x133f 0x0000
          0x5c4e 0xa469 0x0000
          0xd250 0x7cf9 0x0000
          0x209a 0x43a9 0x0000
          0x96c5 0x1054 0x0000
          0x6721 0x0584 0x0000
      "#]].assert_eq(&s.drain(..).as_str());
    }
    Backend::Basic => {
      expect![[r#"
      "#]].assert_eq(&s.drain(..).as_str());
    }
  }
}
#[test]
fn test_hash_u32() {
  let mut s = String::new();
  let mut g = Rng::new(NonZeroU128::MIN);

  for x in iter::chain(0 .. 10, iter::repeat_with(|| g.uniform::<u32>()).take(10)) {
    let y = hash_u32(x);
    let z = invert_hash_u32(y);
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
          0xce96bce1 0xb2b3b83f 0x00000000
          0xc929dc31 0x840b0d83 0x00000000
          0xc26adb58 0x80060fd8 0x00000000
          0x97005b98 0x9e832a5c 0x00000000
          0x4c6cd380 0xa3009611 0x00000000
          0xa03a5c4e 0xd62fc80b 0x00000000
          0x6701d250 0x99bd4718 0x00000000
          0xae2a209a 0x8fb5b923 0x00000000
          0x4bd896c5 0x797c7d4d 0x00000000
          0x45056721 0xeb514a1b 0x00000000
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

  for x in iter::chain(0 .. 10, iter::repeat_with(|| g.uniform::<u64>()).take(10)) {
    let y = hash_u64(x);
    let z = invert_hash_u64(y);
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
          0x9ea17ffbce96bce1 0x4614168aff073dc0 0x0000000000000000
          0xe6536c9dc929dc31 0xde258f03fe348310 0x0000000000000000
          0x7776db02c26adb58 0xa031a391ae8f6857 0x0000000000000000
          0x2bd7d07d97005b98 0x7419cfc0f5a42097 0x0000000000000000
          0x845a314d4c6cd380 0xff8fb50303f7e37f 0x0000000000000000
          0x83d3f43aa03a5c4e 0x2792a2a188c8688d 0x0000000000000000
          0x32e3bf606701d250 0xe46f358479ec984f 0x0000000000000000
          0xc0777aadae2a209a 0xfaf05b730933bf59 0x0000000000000000
          0x16d019024bd896c5 0x56e3b58a95832f24 0x0000000000000000
          0x3a77865d45056721 0xc266c5329cd1e000 0x0000000000000000
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
