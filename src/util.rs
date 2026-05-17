#[allow(dead_code)]
#[inline(always)]
pub(crate) fn invert_u32(a: u32) -> u32 {
  // https://jeffhurchalla.com/2022/04/25/a-faster-multiplicative-inverse-mod-a-power-of-2/
  let x = a.wrapping_mul(3) ^ 2;
  let y = 1u32.wrapping_sub(a.wrapping_mul(x));
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  x
}

#[allow(dead_code)]
#[inline(always)]
pub(crate) fn invert_u64(a: u64) -> u64 {
  // https://arxiv.org/abs/2204.04342
  let x = a.wrapping_mul(3) ^ 2;
  let y = 1u64.wrapping_sub(a.wrapping_mul(x));
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  let y = y.wrapping_mul(y);
  let x = x.wrapping_mul(y.wrapping_add(1));
  x
}

#[inline(always)]
pub(crate) fn ptr_diff<T>(x: *const T, y: *const T) -> usize {
  x.addr().wrapping_sub(y.addr()) / size_of::<T>()
}
