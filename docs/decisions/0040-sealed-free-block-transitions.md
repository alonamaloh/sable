# ADR 0040 — Free-block geometry is exposed only by sealed transitions

**Decided 2026-08-12.** ADR 0039 separated allocator-internal `FreeBlock`
authority from client `BlockLease` authority and proved the algebra ahead of
syntax. This decision implements that boundary as the second allocator vertical
slice.

## Decision

The compiler recognizes six sealed transformations:

```sable
resource FreeBlock block = allocator_take_free(&mut state, key);
allocator_put_free(&mut state, block);

resource FreeBlock suffix = free_block_split(&mut prefix, n);
resource FreeBlock whole = free_block_join(prefix, suffix);

resource BlockLease lease = free_block_lease(block);
resource FreeBlock block = block_lease_free(lease);
```

`allocator_take_free` requires a present, well-formed free entry and removes it
from the aggregate. `allocator_put_free` requires the matching allocator
identity and a well-formed offset-derived key. Absence and non-overlap remain
part of the compiler-sealed aggregate authority; user code is not asked to
reconstruct a global heap predicate from the visible map.

Splitting mutates the borrowed block into its positive prefix and returns the
positive suffix. The VC is exactly `0 < n < len`. Joining consumes two blocks
and requires equal allocator identity and raw allocation, span adjacency, and
the offset-derived right key. The result retains the left identity. There is no
implicit conversion between internal and client roles: the explicit consuming
role changes preserve allocator, key, and exact extent.

All four allocator roles remain mandatory and compiler-terminal:
`AllocatorState`, `FreeBlock`, `BlockLease`, and `LeasedPointsTo<u64>`. In
particular, a client lease has no split operation and neither role can cross an
extern ABI boundary as consumed authority.

## Root and typed-use conditions

The initial free-map key is zero, so `allocator_create` now proves that its root
starts at offset zero and has positive length. This makes the initial
`FreeBlock` well-formed rather than treating key zero as an unexplained axiom.

The vertical subject takes a 16-byte root, splits it into two 8-byte blocks,
leases the prefix to a client, uses it as `LeasedPointsTo<u64>`, returns and
rejoins the exact lease, coalesces the blocks, destroys the aggregate, and
releases the system root. A dedicated Lean normalization theorem proves that
typed initialization and cleanup preserve the block identity needed by the
coalescing transition.

## Evidence and boundary

`corpus/verifies/free_blocks.sable` proves 15/15 obligations with zero
`assume` and zero `defer`; `corpus/tests/test_free_blocks.sable` executes the
typed round trip and observes the value 37. Eight negative subjects pin
mandatory consumption, zero/full splits, reversed and nonadjacent joins,
cross-allocator insertion, the nonsplittable client role, and the extern ABI
boundary.

This slice supplies the authority geometry, not yet an allocator algorithm.
It has no in-band header representation, free-list traversal, size-class
policy, allocation search, or randomized reference comparison. The next slice
must give a free block an identity-preserving typed header role; only then can
the allocator link and walk blocks without exposing raw internal authority to
clients.
