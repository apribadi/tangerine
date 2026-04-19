# Synopsis

Tangerine provides a high performance hash map and hash set implementations for
keys representable as [`NonZeroU32`](std::num::NonZeroU32) or [`NonZeroU64`](std::num::NonZeroU64).

```rust
use std::num::NonZeroU32;
use tangerine::map::IntMap;

let mut t: IntMap<NonZeroU32, u64> = IntMap::new();
let _ = t.insert(NonZeroU32::MIN, 0);
assert!(t.get(NonZeroU32::MIN) == Some(&0));
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
