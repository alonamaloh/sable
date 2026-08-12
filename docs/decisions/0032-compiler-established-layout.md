# ADR 0032 — Layout is compiler-established proof vocabulary

**Decided 2026-08-12.** ADR 0031 deliberately fixed the first typed cell to
eight-byte `u64` geometry. This decision extracts that geometry before adding
another stored type or any allocation source.

## Decision

`Layout` is a pure specification structure:

```lean
structure Layout where
  size  : Int
  align : Int

Layout.wf l :=
  0 < l.size ∧ 0 < l.align ∧ ∃ k : Nat, l.align = 2^k
```

It is **compiler-established**, not a program value. A Sable program cannot
construct, copy, mutate, or pass a layout. Clause text may inspect the canonical
layout of a concrete integer as `u64.layout.size` / `u64.layout.align`. A
generic integer type model carries the same field, so template contracts use
`T.layout` verbatim and instantiation substitutes the concrete canonical
layout.

The eight fixed-width integer types receive the target profile used by the
current SVM: sizes 1, 2, 4, and 8 with equal alignment for their signed and
unsigned forms. Each instance has a kernel-checked `Layout.wf` theorem and
explicit simplification lemmas for both projections. The projection lemmas are
part of the interface: automation must see layout facts without unfolding an
implementation definition.

`PointsToView<T>` now records its `Layout`. The `PointsTo<u64>` well-formedness
fact pins that field to `u64.layout`; raw-to-typed conversion sets it, typed
state transitions preserve it, and conversion back sizes the returned span
from it. The compiler VC, interpreter, and SVM obtain size and alignment from
their canonical `IntTy` layout mapping rather than spelling `8` in each
operation.

## What this does not grant

Layout says only where an abstract value may live. It does not define:

- a byte encoding or decoding relation;
- bytewise copying, equality, hashing, or zero initialization;
- a C ABI guarantee;
- user-defined or target-dependent layout declarations;
- permission to place every type in raw storage.

Those powers remain separate (`RawStorable`, `BitwiseRepr`,
`BitwiseCopyable`, `FromBytes`, `Zeroable`, and `CRepr` in the staging note).
In particular, the zero fill performed after an empty cell returns to raw
storage remains cleanup, not evidence that zero bytes represent a typed value.

## Why there is no `Layout<T>` runtime token

A token would be forgeable unless it were another sealed resource, and a
resource would wrongly suggest consumable authority. Layout is a static fact
attached to a compiler-known type. Keeping it in the type model also preserves
the verbatim clause rule: `T.layout.size` elaborates directly in the same way
as `T.min` and `T.max`.

## Exit criterion and next boundary

This slice is complete when:

- generic and concrete source clauses can use canonical layouts;
- typed-cell VCs mention layout projections rather than numeric duplicates;
- the interpreter and SVM use the same per-type geometry;
- the original typed-cell proofs and differential subjects still pass.

The next probe is one explicitly laid-out POD record. It requires a decision
about record surface syntax and field-offset laws, but still must not introduce
a byte representation. Only after that probe should the program-lifetime
static root and bump arena land.
