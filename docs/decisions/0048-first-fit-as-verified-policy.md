# ADR 0048 — Keep first-fit search in ordinary verified Sable

**Decided 2026-08-12.** ADR 0047 proved that a sorted stored-header chain can
be traversed without changing allocator state. The next question was whether
first-fit selection required another sealed allocator primitive or could stay
in ordinary verified code.

## Decision

First-fit search is ordinary Sable code. Its policy-bearing form,
`free_list_locate_first_fit`, receives the raw allocation base, erased
allocator authority, the root-length sentinel, the runtime head, and an
aligned request of at least one header. Each iteration extracts the current
header with `allocator_step_header`, reads its real size and next fields,
reinserts the exact header, and then either returns a location or advances.
Its frame postcondition is equality with the entry allocator view.

The returned `FreeListLocation` contains the predecessor, current key, actual
size, and actual successor. A compatibility wrapper, `free_list_first_fit`,
projects only the current key. Remembering the predecessor is still a
read-only search result; it does not grant authority to mutate either header.

The executable loop invariant uses
`AllocatorView.RejectedPath state limit need head previous current`; each step
records both the last rejected node and the cursor reached from its real link.
It projects to `RejectedPrefix`, the predecessor-free minimality witness from
the initial decision. Each step records the exact stored header and initialized
fields, proves that its size is below the request, and proves that the step is
not at the sentinel. Combined with the original `StoredChain`, header-map
functionality makes every recorded link a genuine chain edge. Prefix/path tail
lemmas therefore prove that the endpoint is a suffix head of the original
chain, while `FirstFitLocation` exposes the predecessor and selected fields to
later authority-changing policy.

The sentinel is part of the prefix predicate rather than merely of
`FirstFit`. Without the non-sentinel premise, a logically unrelated header
stored at the sentinel could extend a purported prefix beyond the list even
though the executable loop would never take that step. Public specifications
must exclude that model, not rely on control flow hidden inside one proof.

## Evidence and boundary

`corpus/verifies/free_list_first_fit.sable` proves all 22 obligations across
the location search and key-only wrapper, with zero assumptions and zero
deferrals. It reads both physical header words through `base + current`; the
stored-chain root-provenance fact licenses those raw names, and the header is
restored before either branch.

`corpus/tests/test_free_list_first_fit.sable` constructs a real two-node list.
It dynamically checks a head hit and a full two-node miss, then clears both
headers, rejoins the original extent, and releases the system allocation.
Clauses outside the monitor fragment are explicitly fenced; their static
counterparts remain kernel-checked.

The complete corpus passes with one worker in 208.84 seconds. The grind-budget,
LSP, SVM differential, Rust library/documentation, and single-process Lean
library checks also pass.

This decision does not mutate a predecessor link, remove the selected header,
split a candidate, or manufacture a client lease. Search remains reusable
policy code; authority-changing transitions are a separate slice even though
they consume the richer location witness.
