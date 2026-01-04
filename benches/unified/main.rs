//! unified benchmarks


mod bench_map;
mod util;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
  divan::main();
}
