#![feature(uint_carryless_mul)]
#![allow(missing_docs)]

#[inline(always)]
fn crc32cb(a: u32, x: u8) -> u32 {
  unsafe { core::arch::aarch64::__crc32cb(a, x) }
}

#[inline(always)]
fn crc32cw(a: u32, x: u32) -> u32 {
  unsafe { core::arch::aarch64::__crc32cw(a, x) }
}

#[inline(always)]
fn crc32cd(a: u32, x: u64) -> u32 {
  unsafe { core::arch::aarch64::__crc32cd(a, x) }
}

#[inline(always)]
fn vmull_p64(x: u64, y: u64) -> u128 {
  unsafe { core::arch::aarch64::vmull_p64(x, y) }
}

#[inline(never)]
fn uncrc32w(x: u32) -> u32 {
  crc32cd(0, vmull_p64(x as u64, 0xc915_ea3b) as u64)
}

#[inline(never)]
fn uncrc32w_b(x: u32) -> u32 {
  crc32cd(0, x.widening_carryless_mul(0xc915_ea3b))
}

fn main() {
  for i in 0 ..= 255u8 {
    print!("{:#04x}\n", crc32cb(0, i) as u8);
  }
}
