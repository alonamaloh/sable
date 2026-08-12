# ADR 0038 — Allocator aggregates are the sealed lease boundary

**Decided 2026-08-12.** ADR 0037 fixed the authority shape and proved its
algebra independently of compiler syntax. This decision implements the first
vertical slice: a whole raw root can enter an allocator aggregate, make one
client round trip (including typed use), and return to the existing U8b system
release path.

## Decision

The first aggregate surface consists of four compiler-sealed resource
transformations:

```sable
mut resource AllocatorState state = allocator_create(root);
resource BlockLease lease = allocator_take(&mut state, key);
allocator_put(&mut state, lease);
resource RawSpan root = allocator_destroy(state);
```

`allocator_create` consumes, rather than borrows, the complete `RawSpan` and
assigns a fresh erased allocator identity. `AllocatorState` owns a pure free-map
view behind one affine aggregate token. The initial slice places the complete
root at key zero.

`allocator_take` proves the key is present, removes the entry through the
mutable aggregate borrow, and returns a mandatory `BlockLease` containing the
same allocator identity, key, and span. `allocator_put` consumes a lease only
after proving that its allocator matches and its key is absent. `allocator_destroy`
consumes the aggregate only when its map again contains exactly one span with
the root allocation, offset, and length; it returns that current span, including
the client's current byte-state view. The separate mandatory `SystemDealloc`
then follows ADR 0036 unchanged.

The release token deliberately remains a sibling resource rather than being
folded into `AllocatorState`. In the eventual allocator class both are fields,
so the allocator owns both lifetimes, while keeping them separate avoids a
product-return operation and preserves `system_dealloc` as the only machine
release primitive.

## Typed client use preserves the lease

The existing raw typed-cell operations are overloaded on their resource role.
For leased bytes:

```sable
resource LeasedPointsTo<u64> cell = raw_into_cell_u64(ptr, lease);
resource BlockLease lease = raw_from_cell_u64(ptr, cell);
```

The leased typed view carries `allocator` and `key` beside its ordinary
`PointsToView`. Init, read, take, and drop update only the cell component.
Consequently the return obligation survives the entire typed role change, and
the checker rejects binding the result as plain `PointsTo<u64>`.

`AllocatorState`, `BlockLease`, and `LeasedPointsTo<u64>` are mandatory and
compiler-terminal. An audited extern cannot mark any of them `#[consumes]`:
resource erasure cannot perform an aggregate transition.

## Completeness is geometric, not byte equality

An early implementation attempt required the final free span to equal the
original root view byte-for-byte. The typed round-trip exposed why that is
wrong: client writes are allowed to change initialization/content state.
Completeness instead requires the current key-zero span to have the same
allocation identity, offset, and length as the root, with no other free-map
entries. Destruction returns that current span. This preserves byte-state facts
without confusing allocator coverage with immutable contents.

## Evidence and boundary

The positive subject performs system allocation, aggregate take, a leased
`u64` init/take/raw round trip, matching put, aggregate destruction, and system
release. It proves 9/9 obligations with zero `assume` and zero `defer`, and its
dynamic test returns 91.

Negative subjects pin duplicate take, cross-allocator put, double put,
abandoned raw and typed leases, identity loss to plain `PointsTo<u64>`, an
extern sink, and an extern aggregate borrow. The complete single-job suite
passes: cold corpus 231.07 seconds, followed by grind-budget, LSP, SVM
differential, and doc tests. A final warm corpus rerun after sealing borrowed
extern authority passed in 162.51 seconds.

This is not yet a free-list allocator. The aggregate has only the initial whole
root entry; there are no allocator-owned free-block roles, block splitting,
in-band headers, traversal, or coalescing. Client byte load/store/copy over a
lease is also deferred; the typed `u64` path is the forcing identity test for
this slice. The next step is an allocator-owned `FreeBlock` role with sealed
split/reinsert transitions, because the in-band list must manipulate metadata
without manufacturing client leases prematurely.
