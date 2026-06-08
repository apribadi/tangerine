#![allow(missing_docs)]
#![allow(unused)]

use dandelion::Rng;
use tangerine::map::IntMap;
use std::num::NonZeroU128;
use std::num::NonZeroU32;

fn main() {
  let mut g = Rng::new(NonZeroU128::MIN);

  for &c in [1024, 1025].iter() {
    const N: usize = 100_000;
    let mut stats = [0usize; 10];

    for _ in 0 .. N {
      let mut t = IntMap::with_seed(&mut g);
      for _ in 0 .. c {
        let _ = t.insert(g.uniform::<NonZeroU32>(), ());
      }
      for (i, &x) in tangerine::map::internal::probe_count_histogram(&t).iter().enumerate() {
        stats[i] += x;
      }
    }

    let mut n = 0;
    for i in 0 .. 10 {
      n += stats[i];
      print!("{} {:.6}\n", i, n as f64 / (c * N) as f64);
    }
    print!("\n");
  }
}
