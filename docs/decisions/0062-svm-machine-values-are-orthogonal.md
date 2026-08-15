# ADR 0062 — SVM machine values are shapes over ordinary values

**Decided 2026-08-15.**

## Context

The formal SVM's `Val` carried two hand-specialized forms that duplicated
constructors already present, orthogonally, in the same file:

- `arr (a : ArrayVal)` with `ArrayVal := ints (Seq Int) | bools (Seq Bool)` and
  a companion scalar type `ArrayElem := int Int | bool Bool`. Every array
  operation — length, read, store, allocation — was a match with one arm per
  admitted payload, so admitting another payload meant another arm in each,
  plus another arm in `ArrayElem`, plus another arm in the element renderer.
- `ptrOpt (o : Option (Int × Int))` for nullable raw pointers, a flattened copy
  of `opt (o : Option Val)` whose payload is exactly `ptr`'s. It came with a
  parallel expression family (`ptrSomeE`, `ptrNoneE`, `ptrIsSome`, `ptrValue`),
  a parallel binder (`EOut.bindPtrOpt`), a parallel scaffolding lemma, and an
  extra arm in every exhaustive `cases v` block in the agreement proofs.

`Val.opt : Option Val` was already recursive and the two-directional agreement
proofs survived it, so the shape was known to work.

## Decision

**An array is a payload tag beside a sequence of ordinary machine values.**

```lean
inductive ValTag where | int | bool
inductive Val where
  | ...
  | arr (elem : ValTag) (a : Seq Val)
```

`ValTag` is a *name* for an element domain, not a second copy of its values.
Keeping it beside the elements rather than inside their representation is what
makes an empty integer array and an empty Boolean array distinguishable — they
accept different stores — which is load-bearing and unchanged. `Val.tag?` is
the single admission gate: a value has a tag exactly when an array may carry
it. `Val.arrSet?` is one implementation, `if w.tag? = some elem`, and
filling a fresh array is `Seq.replicate`. Reading an element is `Seq.get`;
there is no `ArrayElem` type and no `ArrayElem.toVal` round trip.

The alternative — a `Seq Val` with no tag, recovering the domain from the
elements — loses exactly the empty-array observation, and a `Seq (Σ tag, …)`
per element would let one array hold two domains. The tag belongs to the array.

**A nullable raw pointer is an ordinary option carrying a pointer.** `ptrOpt`
is deleted, and with it `ptrSomeE`/`ptrNoneE`/`ptrIsSome`/`ptrValue`: the
machine has one option family. `Val.opt`'s documented contract already is that
`some(e)` accepts whatever `e` produces and only the accessors check shape, so
folding the pointer case in changes no rule, it removes a duplicate of one.

Which payloads may occupy an option in a given source position remains a
checker question. `compiler/src/svm.rs` still classifies the option
representation to decide what it admits; it no longer uses that classification
to pick a machine constructor.

## Wire format

Array spellings are unchanged: `arr [1, 2]`, `arr [true, false]`, `arr []`.
Option spellings for value payloads are unchanged: `opt none`, `opt some 7`,
`opt some false`. Scalars nested inside an aggregate are spelled bare, and one
definition (`Val.renderInner`, mirrored by `render_inner` in `svm.rs`) now
serves both array elements and option payloads, so those two positions cannot
drift apart.

The nullable-pointer spelling **changes**, deliberately and necessarily:

| before | after |
|---|---|
| `ptrOpt none` | `opt none` |
| `ptrOpt some 3+8` | `opt some ptr 3+8` |

It cannot be preserved: after the fold there is no value that distinguishes an
absent pointer option from any other absent option, so a distinct spelling
would have to be invented from context the value no longer carries. The
conflation is not new on this wire — `RtVal::AffineOptBoolArray(None)` already
rendered as `opt none`. Both sides of the differential move together
(`Val.render` and `render_rt_val`), and `corpus/svm-diff/` stores no expected
strings, so the harness still compares two independently derived answers.

## Consequences

`Val` drops from eight constructors to seven and `ArrayElem` disappears, which
removes an arm from each of the eleven exhaustive `cases v` blocks in the
agreement proofs and deletes one scaffolding theorem outright. Two scaffolds —
`eval_bindArrayElem` and `step_stepArrayElem` — no longer case on `Val`'s
constructors at all: they split on the operand's *domain*, one admitted case
and one rejected case, whatever payloads `Val.tag?` admits. Admitting a new
array payload is now one arm of `ValTag`, one arm of `Val.tag?`, and nothing
else in the machine.

Trap precedence, `undef` corners for well-typed programs, and every pinned
outcome in `SVMArrayTests`/`SVMOptionTests` are unchanged. `SVMRawTests`'s
record guard changes only where it prints the new pointer-option spelling.
