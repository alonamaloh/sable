# ADR 0053 — Resource-map authority is generic and entry mutation is derived

**Decided 2026-08-12.** The allocator aggregate demonstrated a specialized
map of free blocks and headers. U9 asks whether the same ownership architecture
works for a dynamic number of arbitrary resource permissions, without exposing
separation logic or adding one sealed rule per container.

## Decision

The pure view of `ResourceMap<K, R>` is a partial map:

```text
ResourceMapView<K, View<R>> = K -> option<View<R>>
```

One affine aggregate token carries the hidden valid composition of every
resource in that domain. The visible map being a function prevents duplicate
keys; it does not establish resource disjointness. That fact remains in the
resource-context interpretation, exactly where ADR 0022 placed it.

Two sealed rules suffice for authority transfer:

- `take(key)` requires a present entry and replaces the aggregate with the map
  minus that key while returning the exact contained resource;
- `put(key, resource)` requires an absent entry and consumes the resource into
  the aggregate.

The generic context proof shows that both rules preserve agreement with the
world, pairwise separation inside the map, and framing against every unrelated
resource. No global nonoverlap premise becomes a source-level VC.

A tracked mutable entry borrow is not a third authority primitive. Its hidden
meaning is `take`, a resource-specific mutation that preserves the entry's
footprint, then `put`. The probe proves this composition generically. A future
borrow surface may make common code concise, but it will elaborate to already
proved authority rules rather than expanding the trusted resource algebra.

## Intrusive-list proof shape

The acceptance instance is
`ResourceMap<Int, PointsToView<IntrusiveNode>>`. Each initialized node contains
ordinary runtime `previous` and `next` raw pointers. `IntrusiveList` relates
those map entries to an abstract sequence using a recursive `Linked` predicate;
the statement contains no heap, capability predicate, separating conjunction,
or explicit rearrangement of the rest of the map.

The first implementation restricts nodes to one live arena. Map keys are
arena-relative offsets and runtime pointers are `(arena provenance, offset)`.
Under that invariant, pointer equality is equivalent to offset equality and
ordering is offset ordering. The node permissions establish that the pointers
are live. U9 therefore does not need to choose semantics for comparing live
pointers from different allocations; that remains deliberately deferred until
a benchmark actually requires it.

## Evidence and consequence

`docs/notes/resource-map-probe.lean` proves exact take/put view round trips,
generic context preservation, derived mutable-entry update, same-footprint
typed-node writes, the one-arena pointer lemmas, and a concrete two-node doubly
linked shape. It elaborates warning-free with no `sorry`; the printed axiom sets
contain only Lean's standard `propext`/quotient principles where applicable.

The probe also prevents a tempting shortcut. Today's compiler exposes only
`raw<u8>`, `PointsTo<u64>`, and integer options. A real intrusive node requires
an explicitly laid-out typed record, raw pointers to that record, and
`option<raw<Node>>`. Reusing integer links or growing another specialized
`FreeHeader` would avoid precisely the type-generic aggregate and pointer rules
U9 is meant to test.

The next slice should implement the smallest honest `ResourceMap` surface and
exercise it first with the existing `PointsTo<u64>` role. That isolates parser,
checker, VC-generation, and monitor plumbing. Typed records and raw-pointer
options then extend the same surface before the intrusive-list algorithm is
attempted.
