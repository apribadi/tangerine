pub(crate) unsafe trait Word: Copy + Ord {
  const BITS: usize;

  const MAX: Self;

  fn capacity(_: usize) -> usize;

  fn slot(_: Self, _: usize) -> usize;
}

unsafe impl Word for u32 {
  const BITS: usize = 32;

  const MAX: Self = u32::MAX;

  #[inline(always)]
  fn capacity(s: usize) -> usize {
    const { assert!(usize::BITS >= 32) };
    let n = 0x8000_0000_usize >> s;
    let n = n as u32;
    let n = n | (((n as i32) >> 31) as u32);
    n as usize
  }

  #[inline(always)]
  fn slot(h: Self, s: usize) -> usize {
    const { assert!(usize::BITS >= 32) };
    (h as usize) >> s
  }
}

unsafe impl Word for u64 {
  const BITS: usize = 64;

  const MAX: Self = u64::MAX;

  #[inline(always)]
  fn capacity(s: usize) -> usize {
    let n = 0x8000_0000_0000_0000_u64 >> s;
    let n = n | (((n as i64) >> 63) as u64);
    n as usize
  }

  #[inline(always)]
  fn slot(h: Self, s: usize) -> usize {
    (h >> s) as usize
  }
}
