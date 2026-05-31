#![allow(missing_docs)]

fn main() {
  let mut a = [0u8; 256];
  let mut b = [0u8; 256];
  for x in 0 ..= u8::MAX {
    let y = unsafe { core::arch::aarch64::__crc32cb(0, x) };
    let y = (y >> 24) as u8;
    a[x as usize] = y;
    b[y as usize] = x;
  }
  print(&a);
  print(&b);
}

fn print(t: &[u8; 256]) {
  let mut i = 0;
  print!("[\n");
  for _ in 0 .. 32 {
    print!(" ");
    for _ in 0 .. 8 {
      print!(" {:#04x},", t[i]);
      i += 1;
    }
    print!("\n");
  }
  print!("]\n");
}
