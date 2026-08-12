# ADR 0056 — Formal SVM record cells remain abstract and extent-tagged

**Decided 2026-08-12.** U9 completed at the source, VC, and interpreter layers,
but POD record storage was still outside the formal SVM differential oracle.
That boundary was safe to state temporarily and unsafe to forget: prototype
criterion 7 requires the relational rules, their executable evaluator, and the
Rust interpreter to agree on raw-memory examples before U10 adds another
machine profile.

## Decision

The SVM value plane gains two abstract forms:

- `ptrOpt (Option (allocation × offset))` for nullable raw pointers; and
- `record tag fields` for a POD value, with fields retained in declaration
  order under their source names.

Pointer-option construction, someness, value extraction, arena-relative offset
observation, and record projection are pure expressions. Record construction is
an A-normal statement using the existing left-to-right argument evaluator, so
an abnormal field expression wins before anything to its right and a field/
value arity mismatch is `undef`.

Each allocation carries record cells keyed by their starting offsets. A cell
stores the compiler-supplied record tag, size, alignment, and optional abstract
value. A second per-byte owner map marks the entire half-open extent. This is
intentional duplication: byte access and `u64` conversion must decide locally
whether an interior address is occupied, without searching an unbounded
partial map or checking only the record start.

The six instructions mirror typed `u64` storage: convert raw extent into an
empty record cell, convert an empty matching cell back, initialize, copy-read,
take, and drop. Conversion checks positive geometry, alignment, complete live
raw extent, and role exclusion. Initialization and access require matching
record tags. Removal requires the empty state, clears both maps, and explicitly
zero-fills the recorded extent as cleanup. Record values are never decoded from
or encoded into those bytes.

## Agreement and lowering

Every new operation has relational `Step` rules and a matching functional
`stepF` case. Pure forms have matching `Eval` rules and `evalE` cases. Both
directions of agreement are re-proved, so expression determinism/totality and
machine-step determinism/progress remain kernel-checked.

Compiler lowering now receives the checked `Program` as explicit context.
Record indices are validated against that same table; construction emits field
order, and conversion emits the checked size and alignment. Authority arguments
remain erased. Unsupported syntax remains a hard lowering error rather than a
skipped comparison.

## Evidence and consequence

`Sable/SVMRawTests.lean` now has 47 direct guards. The record additions pin a
complete lifecycle, projection and pointer-option behavior, zero fill,
uninitialized access, repeated initialization, mismatched value/access tags,
conversion from an occupied cell, misalignment, use after free, interior-byte
exclusion, and record/`u64` overlap in both directions.

The cross-engine corpus now has 59 subjects. Its record files cover a successful
nullable-link round trip, scalar projection, returned record and pointer-option
outcomes, uninitialized read, double initialization, and premature conversion
back to raw storage. All agree between the Rust interpreter and Lean evaluator.

This closes the pre-U10 semantic gate without choosing a byte representation,
cross-allocation pointer comparison, packed records, or arbitrary classes in
raw storage. Those remain separate decisions rather than accidental
consequences of formalizing POD cells.
