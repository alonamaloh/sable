# ADR 0043 — Free-list traversal uses sorted offsets and the root-length sentinel

**Decided 2026-08-12.** ADR 0042 made free-block headers executable. The
remaining representation question is how ordinary runtime code walks those
headers without reading the erased `AllocatorState` view.

## Decision

The free list is a finite singly linked chain ordered by block offset. The
ordinary runtime head and every stored next link are `u64` offsets relative to
the allocator root. `root.len` is the unique end sentinel. Offset zero remains
available for a real first block, while every live key is strictly below the
sentinel.

For a node `(key, size, next)` in a root of length `limit`, the invariant is:

```text
0 <= key
16 <= size
key + size <= next
next <= limit
```

The tail satisfies the same invariant from `next`. A structural `Chain`
witness supplies finiteness and rules out cycles; the arithmetic ordering also
makes `limit - current` a nonnegative variant that strictly decreases after a
real step. These facts put both header words inside the root and, when the root
length fits `u64`, prove that stored sizes and links fit `u64` too.

Equality `key + size = next` identifies the local coalescing case. A split
creates a suffix node only when its aligned remainder is at least 16 bytes;
otherwise allocation consumes the whole candidate block rather than creating
an unusable node.

The runtime head is deliberately ordinary safe data paired with the erased
`AllocatorState` authority. Ghost aggregate state cannot be queried to obtain
it. A wrapper must preserve their relationship across every mutation.

## Evidence and next boundary

`docs/notes/free-list-traversal-probe.lean` proves one-step elimination, head
bounds, strict separation from the sentinel, header containment, variant
decrease, `u64` field bounds, adjacency detection, aligned remainder geometry,
and rejection of tiny remainders.

The next compiler slice should implement one checked traversal step before a
full search loop. Given the safe root length, current key, and matching
allocator authority, it should expose the size and next values only after the
existing header operations establish the local invariant. Full first-fit
policy, mutation of predecessor links, and randomized allocator testing remain
subsequent work.
