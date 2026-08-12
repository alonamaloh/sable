# ADR 0055 — An arena-backed intrusive list validates aggregate authority

**Decided 2026-08-12.** U9 was designed to falsify the resource architecture,
not merely to add a container. Its acceptance subject had to store ordinary
nullable raw links in typed nodes, relate them to an abstract sequence, and
move node permissions through a reusable aggregate without exposing heap
predicates or separation logic in Sable.

## Decision

The first intrusive-list instance uses one live system allocation. A node
pointer is `(arena provenance, byte offset)`, and the aggregate key is that
offset. This is a deliberate semantic restriction, not an integer-pointer
encoding: runtime links remain `option<raw<IntrusiveNode>>`, and every access
still requires the matching `PointsTo<IntrusiveNode>` extracted from
`ResourceMap<u64, PointsTo<IntrusiveNode>>`.

The visible invariant is ordinary functional mathematics. `IntrusiveList`
relates the optional head and tail, a no-duplicate key sequence, and a recursive
`Linked` predicate. For each key, `Linked` finds an initialized cell in the
map, ties its allocation and offset to the arena and key, and equates its stored
previous/next fields with the neighboring sequence entries. Hidden aggregate
validity supplies ownership agreement and separation; it does not appear in
the invariant.

Traversal and mutation use sealed take–operate–put. Unlinking the head extracts
both affected node permissions, takes their values, constructs the rewritten
remaining node, initializes its cell, and reinserts exactly that permission.
No specialized list authority operation is added. Pointer comparison across
allocations remains unspecified because the subject needs only provenance
agreement plus offset identity inside one arena.

## Evidence

`corpus/verifies/intrusive_list.sable` constructs a concrete two-node list in a
48-byte root, proves the abstract sequence `[0, 24]`, traverses through the
stored forward link, unlinks offset 0, proves `[24]`, converts both empty typed
cells back to raw spans, joins them, and consumes the exact release authority.
It verifies 34/34 obligations with no `assume` and no `defer`. Its dynamic test
observes payloads through the stored nodes and returns 50.

The proof scripts mention `IntrusiveList`, `Linked`, the map operations, and
typed-cell state transitions. They do not rearrange a global heap or state a
separating conjunction. All U9 exit criteria are therefore met: the generic
aggregate survived its intended recursive, pointer-bearing client.

## Consequence

U10 may build on the resource API; the list gives no reason to replace it with
a user-visible separation logic. The next action is nevertheless a hardening
gate, not MMIO implementation: record-tagged typed cells must be added to the
relational SVM, its proved functional evaluator, direct outcome guards, and the
differential harness. Today the Rust interpreter executes them and generated
Lean verifies their views, but the third executable semantics still covers
only byte and `u64` cells. Recording that boundary prevents U9's successful
proof from being mistaken for complete semantic triangulation.
