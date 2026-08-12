# ADR 0054 — Raw-storable records have explicit checked layout

**Decided 2026-08-12.** U9's generic resource map is in the compiler, but its
acceptance instance cannot be expressed honestly with the existing scalar
typed cell. An intrusive node needs a structured value containing nullable raw
pointers. Ordinary classes are the wrong abstraction: they are affine,
invariant-bearing, may own resources, and have destruction semantics, while a
raw typed extent needs a plain runtime value with fixed storage geometry.

## Decision

Sable will add a distinct POD record category. A raw-storable record declares
one complete size and alignment and an offset for every field. The compiler
accepts the declaration only when:

- its size is positive and its alignment is a nonzero power of two;
- its alignment is a multiple of every field's alignment, so an aligned
  record base also aligns every field base;
- every field begins at an offset satisfying that field's alignment;
- every field extent is wholly inside the record extent;
- field extents are pairwise disjoint; and
- every field is itself in the initial `RawStorable` set.

The initial set is deliberately small: fixed-width integers, `raw<Record>`, and
`option<raw<Record>>`. Records have no methods, invariants, owned resources,
destructor, union cases, packing, or implicit class identity. Their constructor
is a direct value construction in declaration order, and record values are
copied as abstract values by the language semantics. This is not permission to
copy an occupied typed extent byte-for-byte.

The first target profile gives raw pointers and nullable raw pointers size 8,
alignment 8. `option<raw<T>>` is an abstract nullable pointer with that layout;
the logic and machine retain an `Option RawPtr` value and do not identify
`none` with a byte pattern. This commits to storage geometry, not a serialized
representation.

`raw<T>` remains provenance plus byte offset and carries no authority. The
pointee type is a static tag used to prevent type confusion. A
`PointsTo<T>` token is still required for every typed access, and an occupied
record extent excludes byte operations exactly as an occupied `u64` extent
does.

## Surface direction

The intended declaration form keeps layout review beside the source type:

```sable
record IntrusiveNode #[layout(size := 24, align := 8)] {
    #[offset(0)] option<raw<IntrusiveNode>> previous;
    #[offset(8)] option<raw<IntrusiveNode>> next;
    #[offset(16)] u64 payload;
}
```

Construction is a direct record operation, not a class initializer. Generic
typed-memory operations carry the record type explicitly so their static tag
cannot be inferred from an unrelated expected type. The existing
`raw_*_u64` spellings remain available while this vertical slice lands.

## No byte representation

The declaration does not establish `BitwiseRepr`, `FromBytes`, `Zeroable`,
`CRepr`, or bytewise copying. Conversion from a complete aligned raw span
creates an uninitialized abstract `PointsTo<IntrusiveNode>` extent. `init`
places an already valid record value in it; `take` returns that value and makes
the extent uninitialized. Converting the empty extent back to raw storage may
zero-fill as explicit cleanup without claiming those bytes encode a node.

`docs/notes/layout-record-probe.lean` checks the concrete node geometry and
shows that generic `PointsToView` state transitions preserve it. The existing
resource-map probe supplies the abstract intrusive-list relation over those
node permissions.

## Consequence

The compiler work is a real type-system and runtime slice: distinct record
types, typed raw pointers, pointer-valued options, record-tagged typed extents,
and the matching ResourceMap instance must agree in VC generation and dynamic
execution. An integer-link encoding or another specialized allocator header is
not an acceptable substitute. Cross-allocation pointer comparison, arbitrary
classes in raw memory, packed records, and byte representation remain deferred.

## Implementation evidence

The slice is implemented. `corpus/verifies/typed_records.sable` covers direct
construction and projection plus record-cell conversion, initialization,
read/take, aggregate take/put, conversion back to raw bytes, span join, and
exact system release: 19/19 obligations. Layout and type diagnostics have
static must-fail subjects, while the interpreter rejects repeated record-cell
initialization dynamically.

`corpus/verifies/intrusive_list.sable` is the non-synthetic client: its node is
exactly the three-field layout above, and both nullable links remain ordinary
runtime values throughout traversal and unlink. The 34-obligation proof
completes without assumptions or deferrals. ADR 0056 closes the subsequent
semantic hardening gate: record values and cells are now abstract instructions
of the relational SVM and proved evaluator, with per-byte extent exclusion and
Rust/Lean differential subjects. This still does not grant records a byte
representation.

A later static audit found that checking only each relative field offset was
insufficient: a record declared with alignment 1 could contain a `u64` field at
offset 0 even though a valid record base need not be `u64`-aligned. The checker
now also requires the record alignment to be a multiple of every field
alignment, and `Layout.fieldFits` states the same invariant. The
`record_field_underaligned` must-fail subject guards the rejected declaration.
