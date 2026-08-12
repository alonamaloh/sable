# ADR 0051 — Returned leases carry their sorted insertion gap

**Decided 2026-08-12.** ADR 0050 established collision-free front insertion,
but `returnable` alone cannot justify arbitrary sorted insertion: absence of an
entry at or inside a lease does not identify its predecessor or prove where
that predecessor ends.

## Decision

Allocation returns `AllocatorView.returnableIn state limit head lease`. It
pairs the exact `returnable` frame with an existential `InsertionLocation`:

- an address-ordered `BeforePath` from the runtime head to concrete
  predecessor/current cursors;
- `predecessor + predecessorSize <= lease.key`; and
- `lease.key + lease.span.len <= current`.

The executable `free_list_locate_insert` independently walks real in-band
links while each inspected header is restored. Its result is specified by a
deterministic `InsertionSearch`. A kernel-checked uniqueness theorem proves
that the runtime cursors equal the existential gap carried by
`returnableIn`; the implementation never trusts caller-supplied predecessor
data.

`free_list_insert` dispatches on those proved cursors. At the head it uses the
ADR 0050 primitive. Otherwise `free_list_insert_after` consumes the mandatory
lease, materializes its two-word header pointing at the current node, extracts
and reads the real predecessor header, rebuilds that exact extent to point at
the returned block, and splices the untouched prefix back over the rebuilt
suffix. These remain ordinary verified Sable functions over the existing
sealed authority transitions.

First-fit allocation now establishes `returnableIn` in all four authority
cases. Whole removal records the gap left by unlinking. Split removal records
the gap before its parked suffix. A shared `replacementInsertionLocation`
lemma transports the untouched first-fit prefix across either rebuilt
allocator view.

## Evidence and boundary

The locator, non-head insertion, and public dispatcher verify with zero
assumptions and zero deferrals. Dynamic fixtures cover head/non-head crossed
with whole/split allocation and return the same mandatory lease through the
public dispatcher before rejoining and releasing the exact system root.

This is sorted insertion without coalescing. It deliberately writes a header
for the returned block even when one or both neighbors are adjacent. The next
slice may now coalesce locally: extract adjacent headers, clear their typed
cells, use proved `FreeBlock.joinable` geometry, and rebuild only the final
combined header and affected predecessor link.
