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

## First compiler instance

The smallest honest compiler surface is now implemented:

```sable
mut resource ResourceMap<u64, PointsTo<u64>> cells = resource_map_empty();
resource_map_put(&mut cells, key, cell);
resource PointsTo<u64> cell = resource_map_take(&mut cells, key);
```

The spelling is parameterized, while this first slice deliberately admits only
`ResourceMap<u64, PointsTo<u64>>`; every other instantiation gets the stable
`resource.map_type` diagnostic. The map is affine rather than mandatory:
abandoning contained cells leaks authority but cannot duplicate it. `put`
consumes the cell and requires an absent key; `take` requires a present key,
removes it, and returns the exact stored view. The compiler carries map
well-formedness at every binding without exposing the hidden separation
interpretation as a VC.

`corpus/verifies/resource_map.sable` exercises the operations through public
contracted wrappers, not only at one local expression site. Two initialized
cells enter a map, leave in reverse order, retain their pointer identity and
values, return to raw spans, rejoin, and satisfy exact system deallocation: 22
obligations across three functions, all proved automatically. Static guards
cover missing take, duplicate put, repeated take, use after put, and an
unsupported instantiation. The dynamic sanitizer maintains only an erased
key-membership shadow, including across ordinary Sable calls, and independently
catches missing take and duplicate put; no authority value reaches the machine.

The complete corpus passes with one worker in 261.79 seconds.

The next slice is therefore no longer generic-map plumbing. It is the honest
typed-node prerequisite already identified by the probe: one explicitly laid
out record, `raw<Node>`, and pointer-valued options. Those extend this same map
surface before the intrusive-list algorithm is attempted.
