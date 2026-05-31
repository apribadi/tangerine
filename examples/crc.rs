#![allow(unused)]
#![feature(uint_carryless_mul)]
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
  for a in 0 ..= 16 {
    let mut m = [false; 65536];
    for i in 0 ..= u16::MAX {
      let x = crc32ch(0, i);
      let x = (x >> a) as u16;
      m[x as usize] = true;
    }
    let mut n = 0;
    for i in 0 ..= u16::MAX {
      if m[i as usize] {
        n += 1;
      }
    }
    print!("{}: {}\n", a, n);
  }
}

/*
    let x =
      unsafe {
        let z = core::arch::aarch64::vdupq_n_u8(0);
        let x = core::arch::aarch64::vdupq_n_u8(i);
        let x = core::arch::aarch64::vaeseq_u8(x, z);
        let x = core::arch::aarch64::vgetq_lane_u8(x, 0);
        x
      };
    let y =
      unsafe {
        let z = core::arch::aarch64::vdupq_n_u8(0);
        let x = core::arch::aarch64::vdupq_n_u8(x);
        let x = core::arch::aarch64::vaesdq_u8(x, z);
        let x = core::arch::aarch64::vgetq_lane_u8(x, 0);
        x
      };
    print!("{:#04x} {:#04x}\n", x, y);
*/
