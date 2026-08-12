# ADR 0031 — Typed cells without byte reinterpretation

**Decided 2026-08-12.** The byte heap and lexical exposure establish raw
storage and authority over it (ADRs 0025–0026). This decides the first typed
storage slice: one `u64` cell, complete through the checker, logic, monitor,
and SVM, before an allocator or a general layout mechanism is added.

## The boundary being tested

`PointsTo<u64>` is affine authority over one abstract typed extent. Its proof
view records provenance, offset, and initialization state:

```text
CellState<T> = uninit | init(T)

PointsToView<T> = {
    alloc : int,
    off   : int,
    state : CellState<T>
}
```

The machine stores a typed extent as a type tag and a value state. This slice's
instruction fixes its size and alignment to eight. It does **not** serialize
the value into bytes. Byte access to an extent while it is typed is undefined;
this is what keeps `RawStorable` apart from the later and stronger
`BitwiseRepr` capability.

## Decision

### One explicit authority round trip

The first surface supports `PointsTo<u64>` only. Authority enters and leaves
the typed world through two unsafe sealed operations:

```sable
raw_into_cell_u64(raw<u8> p, resource RawSpan bytes)
    -> resource PointsTo<u64>;

raw_from_cell_u64(raw<u8> p, resource PointsTo<u64> cell)
    -> resource RawSpan;
```

`raw_into_cell_u64` requires the pointer and span to name the same start and an
eight-byte aligned extent. It consumes the span, discards its byte contents,
and returns an uninitialized typed cell. Discarding is not decoding: no `u64`
is produced from those bytes.

`raw_from_cell_u64` requires the pointer and cell to name the same extent and
the cell to be uninitialized. It consumes the cell, removes the type tag, and
returns eight raw bytes explicitly cleared to zero. An initialized cell cannot
be converted to bytes: doing so would silently decide a representation. The
zero fill is a defined cleanup write after the typed value is gone, not the byte
representation of that value.

This round trip is deliberately expressible inside an exposure. After taking
or dropping the typed value, conversion back yields a reconstructible zeroed
span and the exposure can close. The bridge therefore needs no allocation
source and no representation rule.

### Four typed operations

The cell operations are unsafe and sealed:

```sable
raw_cell_init_u64(raw<u8> p, u64 value,
                  resource &mut PointsTo<u64> cell);
raw_cell_read_u64(raw<u8> p, resource &PointsTo<u64> cell) -> u64;
raw_cell_take_u64(raw<u8> p,
                  resource &mut PointsTo<u64> cell) -> u64;
raw_cell_drop_u64(raw<u8> p,
                  resource &mut PointsTo<u64> cell);
```

All four require `p` to name the cell. `init` requires `uninit` and changes it
to `init(value)`. `read` requires `init(value)`, returns a copy, and preserves
the state. `take` requires `init(value)`, returns the value, and changes the
state to `uninit`. `drop` requires an initialized value and changes the state
to `uninit`; for `u64` it has no runtime destructor effect, but the transition
is the one destructor-bearing typed values will later refine.

Double initialization, reading or taking uninitialized storage, byte access
while the type tag is present, wrong provenance, and wrong offset are undefined
machine operations and failed verification obligations in checked source.
The exact resource extent and alignment are additionally verifier obligations;
the erased machine checks alignment and that eight live raw bytes exist at the
runtime pointer.

### Layout is compiler-established for this slice

The layout is exactly size 8, alignment 8. There is no user-constructible
`Layout<T>` value yet: one fixed instance would test syntax rather than the
concept. The general `Layout<T>` capability lands only after the complete
`u64` transition works through every layer. Alignment is nevertheless real in
this slice: allocation bases are defined to be at least eight-byte aligned and
the conversion checks that the cell offset is divisible by eight.

### Resources stay erased

The pointer is the runtime locator; `PointsTo<u64>` is erased authority just as
`RawSpan` is. The checker prevents duplication and the VC sees only the pure
view. The SVM independently enforces the typed tag and state so the dynamic
oracle can catch a bad lowering or an unsound checker assumption.

## Testing and exit criterion

The slice is complete only when all four layers agree:

- a verifying subject performs the raw-span → cell → raw-span round trip with
  short value-level contracts and no heap predicate;
- negative subjects reject wrong state, wrong extent, and reuse after a
  resource conversion;
- dynamic tests exercise init/read/take/drop and invalid state transitions;
- direct SVM guards and differential subjects agree with the interpreter;
- the Lean relational rules and functional evaluator prove agreement in both
  directions, determinism, totality, and progress as before.

## Deliberately not decided

- General `Layout<T>`, `size_of<T>`, or `align_of<T>` surface vocabulary.
- Byte representations, typed byte copies, `FromBytes`, or zeroing as typed
  initialization.
- Classes, options, pointers, or destructor-bearing values in typed storage.
- Partial typed extents, arrays of cells, or multiple cells in one span.
- Root allocation and `SystemDealloc`; the next source is a non-deallocating
  program-lifetime static region.
