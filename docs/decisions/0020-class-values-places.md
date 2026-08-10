# ADR 0020 — Class values slice B: fields, moves, and borrowing places

**Decided 2026-08-11.** Implements the part of ADR 0010's deferred
slice B that two forcing benchmarks demand: `Integer` (sign +
magnitude, which needs a class-valued `Nat` field) and the unsafe
design's resource carving (`docs/notes/unsafe-sketch.md`, whose
`class Box<T> { raw<T> ptr; … }` examples are written in a Sable that
did not exist).

## What forced it

ADR 0010 shipped the bignum-sufficient surface: shared class borrows,
class returns, field reads. It deliberately deferred moves, `&mut C`,
and class-valued fields "until a forcing benchmark." Two arrived at
once, and they want the *same* underlying thing:

> Ownership must mature from **locals** to **places** — sub-parts of
> owned things, with their own ownership, borrowable and transferable
> independently.

`Integer` needs a `Nat` inside a class. Resource carving needs a byte
range inside an allocation. Same notion, different granularity.

## Decision

Three additions, chosen as the minimum that makes places real:

- **Class-valued fields.** `class Outer { Inner inner; u64 tag; }`.
  In Lean this is a nested structure; the inner class's field facts and
  **its invariant** are pushed one level down, so an outer method
  reasons about `o.inner` exactly as a borrow of `Inner` would.
- **By-value class parameters — moves.** `init wrap(Inner k, u64 t)`.
  Classes are affine, so passing one by value consumes the local. A
  moved-from name is dead: reading it is `class.use_after_move`.
- **Borrowing a field.** `&o.inner`, `&self.inner` — the borrowed place
  is the *field*, not the base object. This is what makes a field a
  first-class subject rather than data you can only read out.

`&mut C` remains deferred (nothing forces it yet — `Integer`'s
arithmetic returns fresh values, like `Nat`'s), as do local-to-local
moves outside argument position.

## The verification model, and why it was cheap

**A move and a borrow are the same thing to the logic.** A by-value
class parameter binds exactly what `&C` binds — the structure value,
its field facts, its invariant. They differ in the affine discipline
(checker) and in what happens at runtime (transfer vs. share), not in
what is proven. That is why this slice cost one arm in `vcgen`'s
parameter setup rather than a new verification concept.

**Affinity is a checker property.** `check.rs` already ran a
flow-sensitive `VarInfo { ty, initialized, mutable }` state machine for
definite initialization; moves added one field (`moved`) and one rule
(a by-value class argument consumes the named local). The diagnostic is
a typechecker error with a span, not a failed proof — which is exactly
the architecture the unsafe sketch bets on for resources, now
demonstrated one level up. Where nothing new was needed at all:
`Val::Obj` (symbolic class values), `push_class_state_facts`, and
`push_invariant_hyps` already existed and simply recurse.

## Known gaps, honestly

- **Direct nested reads are not surface syntax.** `self.inner.v` does
  not parse; today's spelling borrows the field and calls an accessor
  (`read_inner(&self.inner)`), which the corpus demonstrates. The
  parser's field-access path is single-level; generalizing it to paths
  is a contained follow-up, not a model question — clause text already
  writes `self.inner.v` freely, because Lean projections nest.
- `&mut C`, local-to-local moves, class-valued fields *of generic*
  classes, and drop-order interactions beyond reverse-declaration are
  untouched.
- The interpreter shares `Rc`s for both borrows and moves; since no
  construct can mutate through a class borrow yet, the distinction is
  not yet observable at runtime.

## Guards

`corpus/verifies/class_fields.sable` (nested field, move-in, field
borrow, method through a borrowed field — 15 obligations),
`corpus/must-fail/use_after_move.sable` (`class.use_after_move`), and
dynamic coverage in `corpus/tests/test_class_values.sable`.
