# ADR 0041 — In-band free blocks use a two-word identity-preserving header

**Decided 2026-08-12.** ADR 0040 supplied the internal block geometry needed
to split, lease, return, and coalesce allocator authority. The next forcing
question is how a free block carries runtime metadata without losing the
allocator identity and extent tracked by its erased resource view.

## Decision

A free-list node begins with two aligned `u64` cells:

```text
offset + 0:  size
offset + 8:  next block key (or the list sentinel)
offset + 16: raw free payload
```

The corresponding mandatory internal role is a composite view:

```text
FreeHeaderView = {
    allocator,
    key,
    sizeCell : PointsToView<u64>,
    nextCell : PointsToView<u64>,
    payload  : SpanView
}
```

Typing a header consumes a `FreeBlock` whose start is `u64`-aligned and whose
length is at least 16 bytes. The size and next cells are disjoint, and both are
disjoint from the payload. Updating either typed cell preserves allocator,
key, the other cell, and payload exactly. Clearing both cells and returning to
`FreeBlock` restores the original allocation, offset, and length; allocator
coverage is geometric and therefore does not pretend the old header bytes were
unchanged.

The size field stores the whole block length, not merely payload length. Link
ordering and the representation of the end-of-list sentinel are deliberately
left to the traversal slice. Both values must satisfy the ordinary `u64`
range, so the eventual sentinel must be chosen inside that range.

## Why not one word

The first probe used only a next link. Its identity algebra worked, but it was
not an executable allocator design: `SpanView.len` is ghost state and erases,
so runtime code could not know a candidate block's size or compute a split.
Keeping size in a safe side table would evade the in-band allocator benchmark.
Two words are therefore the smallest honest header for a singly linked
first-fit implementation.

## Evidence and next boundary

`docs/notes/free-header-probe.lean` proves header well-formedness from alignment
and the 16-byte minimum, pairwise disjointness of both cells and payload,
carrier preservation for each update, typed-state and `u64` range facts,
clearing preservation, and whole-block round-trip identity/well-formedness.

This decision does not yet choose a sorted-list invariant, sentinel, traversal
contract, split policy, or coalescing algorithm. The compiler slice should add
only the `FreeHeader` role and sealed type/init/read-or-take/clear transitions.
A subsequent one-step traversal probe must choose the link policy before any
full allocator loop is written.
