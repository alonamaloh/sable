# ADR 0049 — First-fit allocation replaces one exact stored node

**Decided 2026-08-12.** ADR 0048 made selection read-only and returned the
predecessor, selected key, actual size, and successor. The remaining question
was how to turn that witness into a client lease without weakening the stored
chain during head removal, predecessor relinking, or splitting.

## Decision

Selection and authority change remain separate. Given a proved
`FirstFitLocation`, `free_list_allocate_found` uses its runtime fields and
dispatches over two independent choices:

1. whether the selected node is the runtime head or follows a rejected prefix;
2. whether `need + freeHeaderBytes <= size`, so the suffix can hold another
   complete two-word header.

The client always receives a nonsplittable mandatory `BlockLease`. If the
suffix is smaller than one header, the whole selected extent is leased. If it
is large enough, the lease is exactly the `need`-byte prefix and a new stored
header covers the exact suffix at `current + need`. The executable test uses
the subtraction form `need <= size - 16`; proved range obligations establish
its equivalence to the specification without an overflowing addition.

Removing the head advances the ordinary `FreeListState.head`. Removing a
non-head node leaves the head unchanged and rebuilds the exact predecessor
extent with a link either to the selected node's former successor (whole
allocation) or to the new remainder (split allocation). The predecessor is
read from its real header; caller-supplied values cannot choose an unrelated
size or link.

`StoredChain` now includes exact header extent and `clearInterior`: no free or
header-map entry may begin strictly inside a stored block. This is the spatial
vacancy needed to park a split remainder without claiming a fact merely from
sorted link order. `FirstFitLocation.unlinkAfter` proves whole non-head
removal. `FirstFitLocation.splitAfter` proves the combined non-head split:
take selected and predecessor headers, park the remainder, rebuild the
predecessor, and then splice the untouched rejected prefix back onto the
rebuilt tail using `AgreesBelow`.

The combined theorem is intentional. Between parking only one of the two new
headers and relinking the other, the allocator view need not form a complete
list from the original head. Ordinary Sable code may pass through that affine
intermediate state, while the public postcondition exposes only the restored
chain.

## Evidence and boundary

The head path proves exact removal, whole-block leasing, and conditional split
allocation. The non-head path proves exact predecessor lookup, whole unlink,
and split replacement. `free_list_allocate_found.sable` verifies all four
branches from one read-only location witness. Every allocator subject has zero
`assume` and zero `defer`.

Dynamic regressions cover a two-node head removal, head whole allocation, head
split allocation, search followed by non-head whole removal, and search
followed by non-head split allocation. Each fixture clears the remaining
headers, rejoins the exact original system extent, destroys the allocator, and
releases the root. The full corpus is run with one worker so these checks never
fan out concurrent Lean processes; the final checkpoint run passed in 167.70
seconds.

This decision completes allocation from a proved first-fit result. It does not
yet insert a returned client lease into the sorted list, coalesce adjacent free
blocks, or provide a search-plus-not-found convenience API. Free and
coalescing are the next authority-changing slice; they must preserve the same
exact-extent accounting and reject wrong-owner or duplicate returns locally.
