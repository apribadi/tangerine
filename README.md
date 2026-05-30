# Synopsis

Tangerine provides high performance hash map and hash set implementations for
keys representable as non-zero integers.

```rust
use core::num::NonZeroU32;
use tangerine::map::IntMap;

let mut t: IntMap<NonZeroU32, u32> = IntMap::new();
let _ = t.insert(NonZeroU32::MIN, 4);
assert!(t.get(NonZeroU32::MIN) == Some(&4));
assert!(t.get(NonZeroU32::MAX) == None);
```

# Ordered Linear Probing

The hash map uses open addressing and ordered linear probing. For each item,
the most significant bits of the hash are used to select a desired slot in the
table.

The following invariants are maintained:
- the hashes contained in occupied slots are in strictly increasing order,
- each item is in a slot with index greater than or equal to that of its
  desired slot, and
- there are no vacant slots between each item and its desired slot.

With those conditions, for any set of items the positions of those items is
uniquely specified.

The main table is sized as a power of two, and a small overflow region is
placed at the end.  The following diagram shows an example table with 8-bit
hashes, 16 main table slots, and 4 overflow slots.

```text
                                                          overflow
hashes │FF FF 2A 30 3C 44 4B FF FF FF A1 FF FF FF FF F8│FD FF FF FF│
values │      XX XX XX XX XX          XX             XX│XX         │
```

The maximum hash value is reserved as a sentinel to indicate an empty slot. To
support that, keys are required to be non-zero integers, and keys are hashed
(injectively!) such that zero would be mapped to the maximum hash.

# Searching for a Key

The basic procedure to search for a key in the table is as follows:

```text
i = h >> shift
loop:
    x = table[i].hash
    if x >= h:
        break
    i = i + 1
if x == h:
    ... search success, item in table[i] ...
else:
    ... search failure ...
```

In aarch64 assembly, this is:

```text
    lsr x10, x9, x10
    add x8, x8, x10, lsl #3
L1:
    ldr w10, [x8], #8
    cmp w10, w9
    b.lo L1
    b.ne L2
    ; ... search success, item in slot at [x8, #-8] ...
L2:
    ; ... search failure ...
```

For this search procedure to work, we require that there is at least one
unoccupied slot at the end of the table to act as a sentinel.

# Searching for a Key, Improved

While the previously described search procedure is correct, we actually use a
modified procedure for improved performance.

We keep the load factor of the hash table between 25% and 50%. At those load
factors, we can measure the CDFs of items' probe distance from their desired
slots.

```text
  │ LF 0.25 │ LF 0.5
──┼─────────┼─────────
0 │  0.852  │  0.649
1 │  0.983  │  0.894
2 │  0.998  │  0.969
3 │  0.999  │  0.991
4 │  0.999  │  0.997
```

For the common case where the search terminates at probe distance 0 or 1, we
execute a fast path with branch-free select operations in order to reduce the
number of branch mispredictions.

```text
i = h >> shift
v = table[i + 1].hash
if v >= h:
    u = table[i].hash
    i = select(u >= h, i, i + 1)
    x = select(u >= h, u, v)
else:
    i = i + 1
    loop:
        i = i + 1
        x = table[i].hash
        if x >= h:
            break
if x == h:
    ... search success, item in table[i] ...
else:
    ... search failure ...
```

In aarch64 assembly, this is:

```text
    lsr x10, x8, x10
    add x11, x9, x10, lsl #3
    mov x9, x11
    ldr w10, [x9, #8]!
    cmp w10, w8
    b.lo L3
    ldr w12, [x11]
    cmp w12, w8
    csel w10, w10, w12, lo
    csel x9, x9, x11, lo
L1:
    cmp w10, w8
    b.ne L2
    ; ... search success, item in slot at [x9] ...
L2:
    ; ... search failure ...
L3:
    ldr w10, [x9, #8]!
    cmp w10, w8
    b.lo L3
    b L1
```

Note that this modified procedure also requires at least one unoccupied
sentinel slot at the end of the table.

# Insertion and Removal

Insertion uses the same search procedure as lookup to find the insertion slot.

The only non-obvious point is that after insertion, in addition to checking the
load factor, we also need to check whether we have filled the *last* slot in
the table.

Removal, again, uses the same search procedure. Items are removed using
backward shift deletion rather than tombstones.

TODO: rewrite, add diagrams

# Prefetching

TODO:

# Full Size Tables

TODO:

# Hashing and Universal Hashing

The hashing strategies used by this library have the following goals and
non-goals:

- Excellent performance for input data distributions one might "organically"
  encounter.

  For comparision, the `rustc_hash` hash fails at this goal because it has
  catastrophic performance for 64-bit integer keys that only vary in the high
  bits.

- Adequate performance for adversarial but seed-independent input. In
  particular, operations degrading from `O(1)` expected amortized performance
  to `O(log(n))` would be acceptable.

  It is unknown whether we currently achieve this goal.

- No performance requirements for interactive adversarial input, e.g. for an
  adversary able to access hash ordering or side-channel timing information.

Our hashing strategies generally use an ad-hoc mixer followed by the
Dietzfelbinger multiply-shift scheme. The multiply-shift is 2-approximately
universal. That would be enough under a universal hashing model to guarantee
`O(1)` expected performance for a separate chaining hash table, but is not
enough for linear probing, which requires either 5-independence or something
like tabulation hashing. However, it is plausible to me that one could prove a
weaker result.

# Code Sizes

TODO: inlining, etc

# Allocation Sizes

TODO:

# On Traversals and Being Accidentally Quadratic

TODO:

# A Ghost of Hash Maps Past

A person familiar with the landscape of hash map implementations might note
that the design of this hash map has some high level similarities with the
design of Rust's previous "Robin Hood" standard library hash map. Why might
this library be better? (Some of the following is obviously subjective or
speculative.)

- My impression is that the old design erroneously used a theoretical result
  that applied to a Robin Hood hash map with random probing to justify a high
  load factor for a Robin Hood hash map with linear probing. My opinion is that
  the clustering produced by linear probing (even Robin Hood linear probing)
  means that high load factors are generally inappropriate.

  [comment from the old standard library hash map about load factor](https://github.com/rust-lang/rust/blob/5531c314a2855aec368e811da6fcd9e98365af51/src/libstd/collections/hash/map.rs#L89-L197)

- This library's precise design choices, e.g. integer keys, an invertible hash
  function, and strict ordering by hash, enable a bunch of low level
  efficiencies.

# Benchmarks

It seems that the Rust ecosystem has remarkably few independent hash map
implementations (in sharp contrast to, say, C++).

TODO: talk about benchmarks and methodology

# Interface Differences from `std::collections::HashMap`

- Keys are integer-like, so we expect that they will be `Copy`. Because of
  that, methods throughout take keys by value rather than by reference.

- Hashing strategies are not customizable.

- Sizing hint operations like `with_capacity` and `shrink_to` are not currently
  implemented.

- Some iterator operations like `drain` and `extract_if` are not currently
  implemented.

# Architecture Specific Code

TODO: crc32c, etc

# References

- High Speed Hashing for Integers and Strings (Mikkel Thorup)  
  <https://arxiv.org/abs/1504.06804>

- On the k-Independence Required by Linear Probing and Minwise Independence
  (Mikkel Thorup)  
  <https://arxiv.org/abs/1302.5127>

- More numerical experiments in hashing: a conclusion (Paul Khuong)  
  <https://pvk.ca/Blog/more_numerical_experiments_in_hashing.html>

- The other Robin Hood hashing (Paul Khuong)  
  <https://pvk.ca/Blog/2013/11/26/the-other-robin-hood-hashing/>

- My favourite small hash table (Peter Cawley)  
  <https://www.corsix.org/content/my-favourite-small-hash-table>

- inverse of crc32c (Marc B Reynolds)  
  <https://github.com/skeeto/hash-prospector/issues/19#issuecomment-3748781340>

- Rust hash iteration+reinsertion
  <https://accidentallyquadratic.tumblr.com/post/153545455987/rust-hash-iteration-reinsertion>
