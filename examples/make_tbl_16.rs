#![allow(missing_docs)]

fn main() {
  let mut a = [0u16; 256];
  let mut b = [0u16; 256];
  for i in 0 ..= u16::MAX {
    let x = unsafe { core::arch::aarch64::__crc32ch(0, i) };
    let x = (x >> 16) as u16;
    let u = x as u8;
    let v = (x >> 8) as u8;
    if v == 0 { a[u as usize] = i; }
    if u == 0 { b[v as usize] = i; }
  }
  print(&a);
  print(&b);
}

fn print(t: &[u16; 256]) {
  let mut i = 0;
  print!("[\n");
  for _ in 0 .. 32 {
    print!(" ");
    for _ in 0 .. 8 {
      print!(" {:#06x},", t[i]);
      i += 1;
    }
    print!("\n");
  }
  print!("]\n");
}
