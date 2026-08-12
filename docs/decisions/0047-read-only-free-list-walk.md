# ADR 0047 — Traverse an unchanged free list before mutating it

**Decided 2026-08-12.** ADR 0046 exposed one policy-bearing header step. The
next risk was whether ordinary loop values, affine header transfer, and the
structural chain witness could survive a real backedge without weakening the
allocator model.

## Decision

The first traversal loop is deliberately read-only with respect to list
structure. Each iteration:

1. calls `allocator_step_header(&mut state, limit, current)`;
2. reads the returned header's runtime `next` field;
3. reinserts that exact header before changing `current`; and
4. advances to `next`.

The loop carries both
`StoredChain state limit 0` and `StoredChain state limit current`. The first
states that reinsertion preserves the complete list; the second supplies the
current node, its tail, the successor bound, and strict decrease of
`limit - current`. Reinserting the extracted header restores the allocator
view by equality, so loop havoc does not require a custom resource exception.

`AllocatorView.storesHeader` also records that the header's size cell has the
same allocation identity as the allocator root. Allocator identity alone is
not pointer provenance: without this extra fact, a generic chain witness could
not justify that `base + current` names the returned header even though the
concrete two-node example happened to do so. The root-provenance fact is part
of the structural chain, while low-level header parking remains usable outside
the traversal policy.

## Evidence and boundary

`corpus/verifies/free_list_walk.sable` constructs two adjacent 32-byte nodes
inside one 64-byte system root and verifies the full walk and cleanup lifecycle:
30/30 obligations, zero `assume`, zero `defer`. The dynamic test visits both
nodes and returns the sentinel value 64. Its only monitor skips are narrowly
fenced custom `StoredChain` clauses, which remain kernel-checked and are not in
the runtime monitor's expression language.

The complete corpus passes with one worker in 211.20 seconds. The grind-budget,
LSP, SVM differential, library, documentation, and Lean library regressions
also pass serially.

The lifecycle proof uses reusable framing lemmas for taking or putting a
different header and a two-header split/clear/rejoin normalization theorem.
Cleanup returns the exact original extent before `system_dealloc`; traversal
does not gain a special destruction path.

This slice does not choose a block, mutate a predecessor link, split an
allocation candidate, or issue a client lease. The next slice proves first-fit
selection while restoring rejected nodes; removal and split/whole-block policy
follow only after the search result has a structural minimality witness.
