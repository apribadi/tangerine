# Synopsis

Tangerine is a high performance hashmap and hashset implementation for keys
representable as [`NonZeroU32`](std::num::NonZeroU32) or [`NonZeroU64`](std::num::NonZeroU64).

```
use tangerine::map::IntMap;
use std::num::NonZeroU64;

let mut t = IntMap::new();
let _ = t.insert(NonZeroU64::new(1).unwrap(), 0);
assert!(t.get(NonZeroU64::new(1).unwrap()) == Some(&0));
assert!(t.get(NonZeroU64::new(2).unwrap()) == None);
```

# Interface Differences From [`std::collections::HashMap`]

- 

# Cargo Features

- nightly

# The Implementation of Tangerine

## A Simple Lookup

## The Actual Lookup Algorithm

## Insertion and Removal

## Hashing (and Universal Hashing)
