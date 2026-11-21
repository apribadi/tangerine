#![allow(dead_code)]

// Each function computes a multiplicative inverse of an odd integer. The result
// given an even integer is unspecified.
//
// For an exposition of the algorithm we use for computing a multiplicative
// inverse, see the following:
//
// - https://jeffhurchalla.com/2022/04/25/a-faster-multiplicative-inverse-mod-a-power-of-2/
// - https://arxiv.org/abs/2204.04342

#[inline(always)]
pub(crate) fn invert_mul_u8(x: u8) -> u8 {
  let u = x.wrapping_mul(3) ^ 2;
  let v = x.wrapping_mul(u).wrapping_sub(1).wrapping_neg();
  let u = u.wrapping_mul(v.wrapping_add(1));
  u
}

#[inline(always)]
pub(crate) fn invert_mul_u16(x: u16) -> u16 {
  let u = x.wrapping_mul(3) ^ 2;
  let v = x.wrapping_mul(u).wrapping_sub(1).wrapping_neg();
  let u = u.wrapping_mul(v.wrapping_add(1));
  let v = v.wrapping_mul(v);
  let u = u.wrapping_mul(v.wrapping_add(1));
  u
}

#[inline(always)]
pub(crate) fn invert_mul_u32(x: u32) -> u32 {
  let u = x.wrapping_mul(3) ^ 2;
  let v = x.wrapping_mul(u).wrapping_sub(1).wrapping_neg();
  let u = u.wrapping_mul(v.wrapping_add(1));
  let v = v.wrapping_mul(v);
  let u = u.wrapping_mul(v.wrapping_add(1));
  let v = v.wrapping_mul(v);
  let u = u.wrapping_mul(v.wrapping_add(1));
  u
}

#[inline(always)]
pub(crate) fn invert_mul_u64(x: u64) -> u64 {
  let u = x.wrapping_mul(3) ^ 2;
  let v = x.wrapping_mul(u).wrapping_sub(1).wrapping_neg();
  let u = u.wrapping_mul(v.wrapping_add(1));
  let v = v.wrapping_mul(v);
  let u = u.wrapping_mul(v.wrapping_add(1));
  let v = v.wrapping_mul(v);
  let u = u.wrapping_mul(v.wrapping_add(1));
  let v = v.wrapping_mul(v);
  let u = u.wrapping_mul(v.wrapping_add(1));
  u
}
