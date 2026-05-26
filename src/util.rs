#[inline(always)]
pub(crate) fn invert_u8(x: u8) -> u8 {
  let u = x.wrapping_mul(3) ^ 2;
  let v = 1u8.wrapping_sub(x.wrapping_mul(u));
  let u = u.wrapping_mul(v.wrapping_add(1));
  u
}

#[inline(always)]
pub(crate) fn invert_u32(x: u32) -> u32 {
  // https://jeffhurchalla.com/2022/04/25/a-faster-multiplicative-inverse-mod-a-power-of-2/
  let u = x.wrapping_mul(3) ^ 2;
  let v = 1u32.wrapping_sub(x.wrapping_mul(u));
  let u = u.wrapping_mul(v.wrapping_add(1));
  let v = v.wrapping_mul(v);
  let u = u.wrapping_mul(v.wrapping_add(1));
  let v = v.wrapping_mul(v);
  let u = u.wrapping_mul(v.wrapping_add(1));
  u
}

#[inline(always)]
pub(crate) fn invert_u64(x: u64) -> u64 {
  // https://arxiv.org/abs/2204.04342
  let u = x.wrapping_mul(3) ^ 2;
  let v = 1u64.wrapping_sub(x.wrapping_mul(u));
  let u = u.wrapping_mul(v.wrapping_add(1));
  let v = v.wrapping_mul(v);
  let u = u.wrapping_mul(v.wrapping_add(1));
  let v = v.wrapping_mul(v);
  let u = u.wrapping_mul(v.wrapping_add(1));
  let v = v.wrapping_mul(v);
  let u = u.wrapping_mul(v.wrapping_add(1));
  u
}

#[test]
fn test_invert_u8() {
  for x in 0 ..= 255 {
    if x % 2 == 1 {
      let y = invert_u8(x);
      assert!(x.wrapping_mul(y) == 1)
    }
  }
}
