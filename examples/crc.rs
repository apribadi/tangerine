#![feature(uint_carryless_mul)]
#![allow(missing_docs)]

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
fn clmul32(x: u32, y: u32) -> u64 {
  vmull_p64(x as u64, y as u64) as u64
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
  let x = 13;
  let y = crc32cw(0, x);
  let z = uncrc32w(y);
  let a = uncrc32w_b(y);
  print!("{:#x}\n", x);
  print!("{:#x}\n", y);
  print!("{:#x}\n", z);
  print!("{:#x}\n", a);
}
