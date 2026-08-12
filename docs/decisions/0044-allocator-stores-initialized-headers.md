# ADR 0044 — AllocatorState may store initialized header authority

**Decided 2026-08-12.** ADR 0043 chose the sorted traversal policy. The first
compiler step exposed a representation gap: converting `FreeHeader` back to
`FreeBlock` clears both typed cells, so an initialized list node could not be
left in the allocator while another node was inspected.

## Decision

`AllocatorView` now has disjoint maps for raw free spans and initialized
`FreeHeaderView` entries. A key may be present in at most one role. The sealed
static operations

```sable
resource FreeHeader h = allocator_take_header(&mut state, key);
allocator_put_header(&mut state, h);
```

temporarily transfer one stored header between the aggregate and an affine
handle. They have no runtime representation: the header's two typed cells stay
in place and retain their values. The ordinary `u64` key controls which entry
is extracted; existing raw header reads then use `raw_offset(root, key)`.

The aggregate's completion condition now also requires the header map to be
empty. Raw/client/free insertion requires the same key to be absent from that
map, preventing two static roles from claiming one extent. Header insertion
requires matching allocator identity, a well-formed header, and absence from
both maps. Kernel-checked lemmas prove insertion/extraction availability,
round-trip restoration, and the complete initial-root lifecycle through a
stored initialized header.

## Evidence and next boundary

`corpus/verifies/free_list_step.sable` initializes the root header, parks it,
extracts it using the ordinary runtime head, reads size and next at the derived
pointer, establishes the local 16-byte/order/bound facts, reinserts it, then
extracts, clears, restores, and deallocates the root. It proves 20/20
obligations with zero assumptions or deferrals and executes to 64. Negative
subjects reject extraction of a missing header and insertion into an allocator
whose ownership cannot be established. The complete one-worker corpus passes
in 354.31 seconds, followed by grind-budget, LSP, SVM, doc, and library suites.

This is an authority-transfer checkpoint, not yet the full U8f traversal
contract. `AllocatorView` still does not state that all stored headers form the
sorted chain from ADR 0043. Consequently the positive subject proves ordering
from its concrete initialized values. The next slice must lift the finite
chain invariant into the aggregate so extracting a node supplies its local
ordering facts and reinsertion preserves the chain. Only then should a search
loop be attempted.
