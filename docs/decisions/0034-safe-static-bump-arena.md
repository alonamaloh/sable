# ADR 0034 — The static bump arena is a safe owner of its unused suffix

**Decided 2026-08-12.** The program-lifetime root from ADR 0033 provides a
pointer and one affine `RawSpan`.  The first allocator should demonstrate that
suballocation is ordinary verified ownership bookkeeping, not another unsafe
authority-producing operation.

## Decision

`BumpArena` is a source-level library class.  It owns the root's unallocated
suffix and records its original capacity plus an aligned cursor:

```text
cursor ≤ cap
cursor % u64.layout.align = 0
free.off = cursor
free.len = cap - cursor
```

The initial slice allocates one canonical `u64` extent at a time.  Its safe
`alloc_u64` method moves the suffix out of the resource field, applies the
sealed safe `split_off` transformation, restores the remainder, and advances
the cursor by `u64.layout.size`.  Its contract explicitly frames capacity and
allocation provenance; this is necessary because an `&mut self` call havocs
the receiver and callers must be able to allocate again and relate every
returned span to the root pointer.

Sable has no product return and resource authority erases at runtime.  The
arena therefore uses a paired API: `next_offset(&self)` observes the cursor,
then `alloc_u64(&mut self)` returns the corresponding owned `RawSpan`.  The
caller derives the runtime pointer with `raw_offset(root, offset)`.  Calling
another allocation between those operations merely makes the stale
pointer/span relation unprovable; it cannot duplicate authority.

## Safety boundary

The arena contains no unsafe region.  Root acquisition remains unsafe because
it creates authority.  Converting the returned raw extent to a typed role and
accessing it remain unsafe because those operations reinterpret or touch raw
storage.  Splitting an already-owned extent and updating value-level
bookkeeping are safe.

The arena has no release operation and owns no `SystemDealloc`.  Dropping it or
abandoning returned spans leaks parts of a program-lifetime allocation, exactly
as ADR 0033 specifies.  This avoids weakening the entry gate for U8.

## Scope and evidence

This rung is intentionally fixed-width.  A generic aligned allocator needs
generic typed-storage support beyond `PointsTo<u64>` and an align-up policy;
neither is hidden behind a literal runtime layout value here.  The explicit
POD-record layout probe remains kernel-checked in
`docs/notes/layout-record-probe.lean`; source-level POD values remain deferred
until their runtime semantics are represented rather than borrowed from class
semantics accidentally.

`corpus/verifies/bump_arena.sable` allocates two live disjoint extents, converts
both to typed cells, and proves the resulting computation.  Its dynamic test
executes the path, while `bump_arena_exhausted.sable` pins the local third-
allocation capacity failure.

The next stage is not deallocation itself.  Before U8 introduces
`SystemDealloc`, mandatory consumption must become a resource-type property
that follows owned parameters and can be discharged only by an explicitly
declared consuming operation.
