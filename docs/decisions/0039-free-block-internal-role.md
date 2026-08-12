# ADR 0039 — Free blocks are allocator-internal split authority

**Decided 2026-08-12.** ADR 0038 established the aggregate/client boundary,
but its initial whole-root entry can only move directly to `BlockLease`. An
in-band allocator must first remove a free extent, inspect or rewrite its
header, split an allocation from it, and reinsert any remainder. Giving those
operations to `BlockLease` would let client code reshape the identity that
`free` is meant to validate.

## Decision

Introduce a distinct mandatory internal role:

```text
FreeBlockView = {
    allocator : AllocatorId,
    key       : BlockKey,
    span      : SpanView
}
```

`FreeBlock` and `BlockLease` deliberately have isomorphic views but different
sealed operation sets. An allocator aggregate takes and puts `FreeBlock` while
manipulating its free structure. Only `FreeBlock` may split or join. An
explicit consuming role change turns the allocated block into `BlockLease`;
the inverse role change begins client deallocation but still leaves mandatory
internal authority that must be reinserted or joined.

Block keys are offsets within the root allocation. A well-formed free block
has `key = span.off`. Splitting at `n` leaves the prefix key unchanged and gives
the suffix key `key + n`. Joining adjacent blocks keeps the left key. This makes
keys stable for in-band lookup and gives the compiler a local equation for the
new remainder entry instead of requiring a fresh existential identity.

The split precondition is `0 < n < len` when both results must remain free
blocks. Exact-fit allocation does not split: it changes the whole block's role
to `BlockLease`. Coalescing joins only blocks with the same allocator and raw
allocation, adjacent spans, and the expected offset-derived right key.

## Proof evidence

`docs/notes/free-block-probe.lean` proves:

- aggregate take followed by internal put restores the original view;
- positive prefix/suffix pieces retain `key = span.off`;
- split lengths cover the original, keys differ, and byte intervals are
  disjoint;
- the pieces are joinable by allocator, allocation, adjacency, and key;
- joining them restores allocator/key, root extent, and every byte; and
- conversion to `BlockLease` preserves allocator, key, and span exactly.

The proof is intentionally ahead of syntax. The next compiler slice adds the
mandatory `FreeBlock` type and sealed take/put, split/join, and lease/free role
changes. Header typing comes afterward and must preserve the same internal
identity just as `LeasedPointsTo<u64>` preserves client identity.
