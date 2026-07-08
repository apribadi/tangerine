#![allow(unused)]
#![allow(missing_docs)]

use core::arch::aarch64::uint8x16_t;

#[inline(always)]
fn crc32cb(a: u32, x: u8) -> u32 {
  unsafe { core::arch::aarch64::__crc32cb(a, x) }
}

#[inline(always)]
fn crc32ch(a: u32, x: u16) -> u32 {
  unsafe { core::arch::aarch64::__crc32ch(a, x) }
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
fn widening_carryless_mul(x: u32, y: u32) -> u64 {
  unsafe { core::arch::aarch64::vmull_p64(x as u64, y as u64) as u64 }
}

#[inline(never)]
fn invert_crc32c_32(x: u32) -> u32 {
  crc32cd(0, widening_carryless_mul(x, 0xc915_ea3b))
}

#[inline(always)]
fn invert_crc32c_96(x: u32) -> u32 {
  crc32cd(0, widening_carryless_mul(x, 0x413d_19cd))
}

fn main() {
  let x = 1;
  let y = crc32cw(x, 0);
  for i in 0 ..= u32::MAX {
    if x == crc32cd(0, widening_carryless_mul(y, i)) {
      print!("{:#x}\n", i);
    }
  }
  let y = crc32cd(crc32cw(x, 0), 0);
  for i in 0 ..= u32::MAX {
    if x == crc32cd(0, widening_carryless_mul(y, i)) {
      print!("{:#x}\n", i);
    }
  }
}
