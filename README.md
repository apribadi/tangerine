# Synopsis

Tangerine provides high performance hash map and hash set implementations for
keys representable as `NonZeroU32` or `NonZeroU64`.

```rust
use core::num::NonZeroU32;
use tangerine::map::IntMap;

let mut t: IntMap<NonZeroU32, u64> = IntMap::new();
let _ = t.insert(NonZeroU32::MIN, 0);
assert!(t.get(NonZeroU32::MIN) == Some(&0));
assert!(t.get(NonZeroU32::MAX) == None);
```

# Ordered Linear Probing

# Searching for a Key

# Searching for a Key, Improved

# Insertion and Removal

# Hashing and Universal Hashing

# Interface Differences from `std::collections::HashMap`

- 

# Ghosts of Hash Maps Past

# References

- On the k-Independence Required by Linear Probing and Minwise Independence
  (Mikkel Thorup)  
  <https://arxiv.org/abs/1302.5127>

- More numerical experiments in hashing: a conclusion (Paul Khuong)  
  <https://pvk.ca/Blog/more_numerical_experiments_in_hashing.html>

- The other Robin Hood hashing (Paul Khuong)  
  <https://pvk.ca/Blog/2013/11/26/the-other-robin-hood-hashing/>

- My favourite small hash table (Peter Cawley)  
  <https://www.corsix.org/content/my-favourite-small-hash-table>

- (github comment on inverting crc32c) (Marc B Reynolds)  
  <https://github.com/skeeto/hash-prospector/issues/19#issuecomment-3748781340>
