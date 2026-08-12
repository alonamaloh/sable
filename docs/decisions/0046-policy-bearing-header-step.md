# ADR 0046 — Traversal uses a policy-bearing header step

**Decided 2026-08-12.** ADR 0044 supplied low-level header authority transfer;
ADR 0045 proved the stored-chain witness needed to distinguish a valid list
walk from arbitrary header access.

## Decision

The sealed traversal operation is:

```sable
resource FreeHeader node =
    allocator_step_header(&mut state, limit, current);
```

`limit` and `current` are ordinary runtime `u64` offsets. The generated
obligation requires both `current != limit` and
`StoredChain state limit current`. On success the operation transfers the same
header authority as `allocator_take_header`; it adds no runtime instruction.
The two-argument take remains the lower-level lifecycle operation used to
clear a known header during allocator destruction.

`StoredChain.step` relates the returned header to initialized size/next
witnesses and supplies `16 <= size`, `current + size <= next`,
`next <= limit`, the tail chain, and the decreasing traversal variant.
Reinserting the exact header restores the aggregate by equality.

## Evidence and boundary

`corpus/verifies/free_list_step.sable` now constructs the initial one-node
chain, enters through `allocator_step_header`, and discharges all three runtime
size/order/bound assertions from `StoredChain.step` and the values read from
the returned header. It remains 20/20 with zero assumptions or deferrals and
executes to 64. `allocator_step_sentinel.sable` rejects attempting to traverse
the root-length sentinel at the named policy obligation.

The complete one-worker corpus passes in 352.58 seconds, followed by
grind-budget, LSP, SVM, doc, and library regressions. The final proof-script
tightening was rechecked directly on the 20-obligation subject.

The next slice is a real loop over an unchanged list: extract, read, reinsert,
advance to `next`, and carry the tail `StoredChain` plus variant across the
backedge. Do not mutate predecessor links or allocate yet; first verify that
ordinary loop havoc and resource-shape checks can preserve this paired runtime
head/erased-chain invariant without `assume` or `defer`.
