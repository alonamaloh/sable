# ADR 0036 — System roots carry sealed mandatory release authority

**Decided 2026-08-12.** ADR 0035 made mandatory consumption strong enough for
release authority. Before a free-list allocator can own such authority, the
root acquisition and terminal release path must work vertically through every
enforcement layer.

## Decision

A releasable root is acquired atomically:

```sable
unsafe system_alloc(4096) as
    (base, resource bytes, resource release);
```

The statement binds a fresh `raw<u8>` base, one `RawSpan` over the complete
uninitialized allocation, and one `SystemDealloc`. As with `static_alloc`, the
size is a positive compile-time literal within the 50,000,000-byte execution
profile, so verified source does not branch on allocation failure. The SVM
still reports OOM when executed under a smaller external capacity.

`SystemDealloc` is compiler-defined and mandatory. Its pure view records the
allocation identity and original length; the authority itself is affine and
checker-only. It may travel through verified owned parameters, returns, and
class fields under ADR 0035, but it may terminate only here:

```sable
unsafe system_dealloc(base, bytes, release);
```

Release consumes both resources and proves locally that the pointer is the
base and `bytes` is the complete raw extent with the same allocation identity
and length as `release`. Carved extents must be rejoined first. An abstract
typed cell must be emptied and converted back to `RawSpan`; passing a
`PointsTo<T>` is not the required type. The operation then lowers to the SVM's
existing `rawFree` instruction.

## The terminal boundary is sealed

An audited extern may consume `OpenFile`, because closing a foreign descriptor
is an environmental operation and the audit states what C does. It may not
accept owned `SystemDealloc`, even with `#[consumes]`. Resource arguments erase
at the ABI, so such a declaration could only promise away the checker token;
it would not perform the Sable machine's allocation release or establish
pointer/extent agreement. `resource.release_sealed` rejects this boundary.

This distinction is why “mandatory” and “terminal” are separate properties.
The type says authority cannot be abandoned; the compiler says which operation
has semantics strong enough to terminate it.

## Layer interpretation

- The checker creates one ordinary affine raw span and one mandatory release
  place. `system_dealloc` is the only sealed sink and consumes both.
- VC generation binds `SpanView.uninit alloc N` and
  `SystemDeallocView { alloc, len := N }`; release emits one local agreement
  obligation.
- The interpreter creates a fresh live allocation and marks it dead only from
  a live base pointer.
- SVM lowering is `rawAlloc` followed eventually by `rawFree`. The relational
  and executable SVM semantics already define OOM, invalid free, double free,
  and use-after-free.

## Evidence and scope

The positive subject performs a complete raw → typed `u64` → raw round trip,
releases it, and separately carves/rejoins a root before release (9/9
obligations). Dynamic execution covers both. A source-level differential
subject raises the Rust/Lean agreement corpus to 48 programs. Negative subjects
pin abandoned release authority, partial extent, interior pointer, wrong
allocation token, double release, forbidden extern discharge, and invalid
sizes; the direct SVM suite already pins invalid/double/interior free and
use-after-free outcomes.

This slice does not yet introduce allocator identities distinct from raw
allocation provenance, `BlockLease`, in-band headers, client free, or
coalescing. Those belong to the next allocator slice, now built over a root
whose lifetime rule is no longer provisional.
