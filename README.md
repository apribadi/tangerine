# Synopsis

Tangerine is a high performance hashmap and hashset implementation for keys
representable as [`NonZeroU32`](std::num::NonZeroU32) or [`NonZeroU64`](std::num::NonZeroU64).

```rust
use tangerine::map::IntMap;
use std::num::NonZeroU32;

let mut t = IntMap::new();
let _ = t.insert(NonZeroU32::MIN, 0u64);
assert!(t.get(NonZeroU32::MIN) == Some(&0u64));
assert!(t.get(NonZeroU32::MAX) == None);
```

# Interface Differences from `std::collections::HashMap`

- 

# Cargo Features

- nightly

# Searching for a Key

# ???

# Searching for a Key, the Actual Algorithm

# Insertion and Removal

# Hashing (and Universal Hashing)
