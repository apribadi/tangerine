#![allow(missing_docs)]

fn main() {
  let mut r = [0u8; 256];
  for x in 0 ..= 255u8 {
    let y = unsafe { core::arch::aarch64::__crc32cb(0, x) };
    let y = (y >> 24) as u8;
    r[y as usize] = x;
  }
  let mut i = 0;
  print!("[\n");
  for _ in 0 .. 16 {
    print!(" ");
    for _ in 0 .. 16 {
      print!(" {:#04x},", r[i]);
      i += 1;
    }
    print!("\n");
  }
  print!("]\n");
}
