# ADR 0021 — `Integer`: signed arithmetic on `Nat`, and the two places it forced

**Decided 2026-08-11.** `corpus/verifies/integer.sable` is a signed
integer library — sign plus magnitude over bignum's `Nat`, the first
Sable type built *on* a verified class rather than on arrays. Finishing
it forced two extensions to ADR 0020's notion of a place, both small and
both in the same direction.

## The library

`class Integer { Nat mag; u64 neg; }` with three invariants: `neg ≤ 1`,
`0 ≤ natVal mag.limbs`, and `neg = 0 ∨ natVal mag.limbs ≥ 1` — the last
one banning negative zero, so the representation is unique.

The whole specification is one ghost function:

```
def intVal (neg : int) (m : Sable.Seq Int) : int :=
  if neg = 1 then 0 - natVal m else natVal m
```

and one clause per operation: `intVal result = intVal a ⊕ intVal b` for
`+ - * / %`, full iff posts for `cmp`. Everything is `pub` and bound
through operators, which are keyed by `(symbol, class)` (ADR 0012) and
so coexist with the `Nat` bindings the same program imports.

Two design points earn their keep:

- **Nonnegativity is an invariant, not a lemma.** `0 ≤ natVal mag.limbs`
  is discharged once, at `Integer::make`, from the limb bounds. Every
  borrow of an `Integer` then gets the fact for free. Without it, the
  sign case analysis in `int_add`/`int_cmp` re-derives it from
  `valIn_nonneg` at every branch.
- **No negative zero pays for itself immediately.** Because a negative
  operand has magnitude at least one, like-sign addition needs no zero
  check at all — the sum cannot be zero, so the sign is simply carried
  over. The check is needed only where a zero really can appear:
  cancelling addition, a zero factor, a zero quotient.

**Division is the operation, not a model of it.** ADR 0004 chose
Euclidean `/` and `%` precisely because they are Lean's on `Int`, and
that pays off here: `intVal result = intVal a / intVal b` is a contract
about the same function the program computes. Magnitude division gives
`A = Q·B + R` with `0 ≤ R < B`; four ghost facts turn that into the
signed pair. A negative divisor only flips the quotient's sign
(`Int.ediv_neg`, `Int.emod_neg`); a negative dividend with a non-zero
remainder is the single case that rounds away from zero, costing one
more in magnitude — which is also why that branch needs no zero check,
since `Q+1 ≥ 1` always.

Totals: **233 obligations across 27 functions, 17 discharges**, 9 ghost
theorems, zero deferred or assumed. Dynamic coverage in
`corpus/tests/test_integer.sable` pins the Euclidean convention on all
four sign combinations of ±7 ÷ ±2 and ±6 ÷ ±3, at zero skipped clauses.

## What it forced, and why both were one-liners

**Array-valued fields are borrowable places.** ADR 0020 made `&x.f` work
for class-valued fields only. But `Nat` is affine and `negate` holds
only a *borrow* of its operand, so it must duplicate the magnitude
before moving it into a new `Integer` — and the cheapest copy is to
re-run the prefix constructor over the existing limbs,
`Nat::from_prefix(&a.limbs, a.limbs.len)`, with the class invariant
supplying its nonzero-top precondition and no arithmetic involved. That
needs `&a.limbs`. The checker now returns `&[T]` for an array field
instead of a diagnostic, and vcgen picks `Val::Arr` over `Val::Obj`
using the type the checker already recorded on the expression; the
interpreter needed nothing, because sharing the field's `Rc` was already
what a field borrow did. `type.not_a_class` on this path became
`type.not_a_place`, which is what it was always saying.

**Affinity is per path.** `check.rs` joined `initialized` across an `if`
correctly — a branch that returns contributes nothing to the
fall-through state — but tracked `moved` monotonically beside it, so a
move on a returning branch killed the local for the code after the
branch. `int_mul` and `int_rem` are both written the natural way (test
for the special case, return, then move the value in the common case)
and both tripped it. The two facts now join together: initialized iff
every reaching branch initialized it, moved iff any reaching branch
moved it.

Both changes are the same maturation ADR 0020 described — ownership
moving from locals to places — reaching the two things that were still
whole-local: which fields count as places, and how precisely the affine
state follows control flow.

## Known gaps, honestly

- **Operator operands must be named locals.** `a.mag + b.mag` does not
  elaborate; the implementation calls `add(&a.mag, &b.mag)` directly.
  Extending the operator rewrite from names to places is contained (the
  borrow it would build is now legal), but nothing forces it — inside
  the implementation the explicit call is arguably clearer, and clients
  use the operators on locals, which do work.
- **No unary minus on class values.** `negate(&x)` is a call; `-x` is
  not bound because `operator` covers binary symbols only.
- `&mut C` and local-to-local moves remain deferred, unchanged from ADR
  0020.
- `Integer` has no parsing, formatting, or conversion to and from the
  machine integer types; magnitudes are built through `Nat`.

## Guards

`corpus/verifies/integer.sable` (the library),
`corpus/tests/test_integer.sable` (11 dynamic tests),
`corpus/verifies/class_fields.sable` (`Buf`, an array-valued field
borrowed through a free function and a method; `move_on_returning_branch`
for the affine join), `corpus/must-fail/borrow_scalar_field.sable`
(`type.not_a_place`), and `corpus/tests/test_class_values.sable` for the
dynamic side of both.
