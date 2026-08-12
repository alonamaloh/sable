# ADR 0033 — Program-lifetime static roots have no deallocation authority

**Decided 2026-08-12.** Typed cells and layouts need a root source before a
bump arena can be written. U8's `SystemDealloc` token is still blocked on the
stronger mandatory-consumption rule, so this rung must not introduce a hidden
or weakly tracked right to free memory.

## Decision

The first root source is a dedicated unsafe statement:

```sable
unsafe static_alloc(4096) as (p, resource mem);
```

It binds:

- `p : raw<u8>`, the start of a fresh allocation;
- `mem : resource RawSpan`, affine authority over its full extent.

The bindings belong to the enclosing function, like locals declared in a plain
`unsafe {}` marker. This is not a lexical loan: the allocation remains live for
the rest of program execution, and neither binding carries a loan brand.
Returning or moving the resource is therefore meaningful. The source returns
no `SystemDealloc`, lease, or other release capability. Abandoning `mem` is an
explicit leak, permitted by affine ownership and intended for this rung.

The size must be a positive compile-time integer literal within the current
execution profile's 50,000,000-byte allocation cap. This keeps verification
free of an allocation-success branch: accepted static roots fit the profile.
The machine still retains its ordinary OOM outcome when run under a smaller
external capacity.

Each execution creates fresh provenance. Calling a function containing the
statement twice creates two disjoint program-lifetime roots; this is a leaking
allocation source, not a singleton global declaration. A later freestanding
profile may add named linker regions, but their once-only acquisition discipline
is a separate whole-program question.

## Layer interpretation

- The checker creates exactly one pointer binding and one owned `RawSpan` and
  applies ordinary affinity from that point onward.
- The VC generator binds `SpanView.uninit alloc N` and its start pointer. The
  bytes exist but are uninitialized; no reconstructibility fact is invented.
- The interpreter creates a fresh live raw allocation and never releases it.
- SVM lowering is exactly `.rawAlloc p N`; resource authority erases. The
  existing allocation semantics already supply fresh provenance and
  uninitialized bytes.

The direct lowering is deliberate. Adding a source-level wrapper class solely
to return `(pointer, resource)` would pull aggregate runtime values into the SVM
before class semantics are formalized. The multi-binding statement expresses
the one atomic authority-producing event without inventing tuple values.

## Safety boundary

Acquisition is unsafe because it creates root authority. Once acquired,
`split_off`, `join`, and future bump-arena bookkeeping remain safe resource
transformations. Raw accesses and typed role changes remain unsafe under their
existing rules.

This ADR does not add deallocation, global mutable state, named static regions,
fallible allocation in verified source, or a byte representation.
