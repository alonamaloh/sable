# ADR 0037 — Block leases refine byte authority

**Decided 2026-08-12.** A free-list allocator needs to hand client code both
permission to access a block and an identity that only the originating
allocator may accept on `free`. Keeping a `BlockLease` marker beside an
ordinary `RawSpan` would be the wrong factoring: the two affine values could
travel separately, and converting the span to `PointsTo<u64>` would lose the
allocator identity exactly while the client is using the block.

## Decision

`BlockLease` is the byte authority, not a receipt accompanying byte authority.
Its view is:

```text
BlockLeaseView = {
    allocator : AllocatorId,
    key       : BlockKey,
    span      : SpanView
}
```

Raw access projects `span`. A role change to typed storage produces a leased
typed resource whose view retains `allocator` and `key` beside the
`PointsToView`; changing back reconstructs the same lease. A plain
`PointsTo<u64>` is therefore not the result of typing leased bytes.

The allocator's dynamic permissions are represented by one affine aggregate
resource plus a pure map from block keys to span views. Its sealed `take`
transition removes one map entry and returns the corresponding `BlockLease`;
its sealed `put` transition consumes a matching lease and restores the entry.
The pure map describes the view, but does not by itself justify disjointness:
the aggregate resource is the authority, and the sealed transitions preserve
its hidden valid composition invariant.

`BlockLease` and its typed refinements are mandatory resources. Their only
terminal path is back into the matching allocator aggregate; an extern cannot
promise them away.

## Why identity belongs in every role

Affinity prevents duplicating one resource value. It does not connect two
separately represented values, so a detached marker plus span would permit the
marker and memory authority to become unsynchronised. Nor can the allocator
infer its identity merely from system allocation provenance: distinct
allocators may manage disjoint regions of one root, and allocator identity is
the fact needed to reject a cross-allocator free.

Preserving identity in typed roles also makes a subregion error structural.
There is no operation that splits a client lease into a smaller lease and then
passes that off as the original block. Internal free-region transformations
will use allocator-owned roles, separate from client leases.

## Proof probe

`docs/notes/free-list-probe.lean` models the authority algebra independently of
surface syntax. It proves that:

- taking an entry partitions all capabilities between the residual aggregate
  and exactly one lease;
- the residual aggregate and lease are disjoint when the input entries are;
- putting the lease after taking it restores the original aggregate view; and
- converting an exact eight-byte lease to a leased `u64` cell preserves both
  its capabilities and allocator/key identity.

The probe is intentionally smaller than the allocator. It settles the
resource shape before compiler work and does not claim that in-band headers,
splitting, coalescing, or allocator destruction are implemented.

## Consequences for the next slice

The compiler surface must not expose standalone `lease(span, id)` and
`unlease(lease, id)` operations: the latter would let code discharge a
mandatory lease without actually returning it to an allocator. Lease creation
and consumption occur only through sealed aggregate transitions.

The first compiler slice will establish allocator identities, the aggregate
take/put path, mandatory lease flow, and role-preserving raw/typed access. The
following slice will add allocator-owned free-block roles and the in-band list
algorithm over those transitions.
