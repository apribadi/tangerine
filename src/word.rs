pub(crate) unsafe trait Word:
  Copy
  + Ord
  + core::ops::Add<Self, Output = Self>
  + core::ops::BitOr<Self, Output = Self>
  + core::ops::Not<Output = Self>
  + core::ops::Shr<usize, Output = Self>
{
  const BITS: usize;

  const ZERO: Self;

  fn asr(_: Self, _: usize) -> Self;

  fn into_usize(self) -> usize;
}

unsafe impl Word for u32 {
  const BITS: usize = 32;

  const ZERO: Self = 0;

  #[inline(always)]
  fn asr(x: Self, s: usize) -> Self {
    ((x as i32) >> s) as u32
  }

  #[inline(always)]
  fn into_usize(self) -> usize {
    self as usize
  }
}

unsafe impl Word for u64 {
  const BITS: usize = 64;

  const ZERO: Self = 0;

  #[inline(always)]
  fn asr(x: Self, s: usize) -> Self {
    ((x as i64) >> s) as u64
  }

  #[inline(always)]
  fn into_usize(self) -> usize {
    self as usize
  }
}
