# ADR 0048 — Keep first-fit search in ordinary verified Sable

**Decided 2026-08-12.** ADR 0047 proved that a sorted stored-header chain can
be traversed without changing allocator state. The next question was whether
first-fit selection required another sealed allocator primitive or could stay
in ordinary verified code.

## Decision

First-fit search is an ordinary Sable function. It receives the raw allocation
base, erased allocator authority, the root-length sentinel, the runtime head,
and an aligned request of at least one header. Each iteration extracts the
current header with `allocator_step_header`, reads its real size and next
fields, reinserts the exact header, and then either returns the current key or
advances. Its frame postcondition is equality with the entry allocator view.

Minimality is represented by
`AllocatorView.RejectedPrefix state limit need head result`. Each step records
the exact stored header and initialized fields, proves that its size is below
the request, and proves that the step is not at the sentinel. Combined with
the original `StoredChain`, header-map functionality makes every recorded link
a genuine chain edge. `RejectedPrefix.tail` therefore proves that the endpoint
is a suffix head of the original chain; `FirstFit.resultChain` exposes that
fact to removal and split policy.

The sentinel is part of the prefix predicate rather than merely of
`FirstFit`. Without the non-sentinel premise, a logically unrelated header
stored at the sentinel could extend a purported prefix beyond the list even
though the executable loop would never take that step. Public specifications
must exclude that model, not rely on control flow hidden inside one proof.

## Evidence and boundary

`corpus/verifies/free_list_first_fit.sable` proves all 15 obligations with zero
assumptions and zero deferrals. It reads both physical header words through
`base + current`; the stored-chain root-provenance fact licenses those raw
names, and the header is restored before either branch.

`corpus/tests/test_free_list_first_fit.sable` constructs a real two-node list.
It dynamically checks a head hit and a full two-node miss, then clears both
headers, rejoins the original extent, and releases the system allocation.
Clauses outside the monitor fragment are explicitly fenced; their static
counterparts remain kernel-checked.

The complete corpus passes with one worker in 208.84 seconds. The grind-budget,
LSP, SVM differential, Rust library/documentation, and single-process Lean
library checks also pass.

This decision does not mutate a predecessor link, remove the selected header,
split a candidate, or manufacture a client lease. Those are the next slice.
Search remains reusable policy code; only authority-changing transitions
belong behind sealed operations.
