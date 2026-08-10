# Operator overloading — design sketch (for discussion)

Motivation (Alvaro, 2026-08-10): `q = add(&q, &m)` should be `q = q + m`,
and operators are what would make templates genuinely useful beyond the
integer types.

There are two features hiding in "operator overloading", with very
different costs:

## 1. Operator sugar for concrete classes (cheap, high value)

`a + b` where `a`, `b` are class values (or borrows) desugars, at
check-time, to a call of a *declared* operator function. Explicit
declaration, not name magic:

```sable
class Nat {
    ...
}

/// operator +  = add
/// operator -  = sub
/// operator *  = mul
/// operator /  = div
/// operator %  = rem
```

- The declaration binds an operator to an existing contracted `fn
  (&C, &C) -> C` (same-class, borrow-taking, value-returning — exactly
  the bignum shape). Everything downstream is unchanged: the desugared
  call carries the callee's pres as obligations and posts as
  hypotheses; diagnostics can even name both the operator and the
  function.
- **Clause language impact: none.** Contracts already speak about class
  values through ghost functions (`natVal a.limbs + natVal b.limbs`),
  and the `+` in clause text is Lean's own `+` on `Int` — nothing to
  overload on the proof side. This is the key reason the sugar is
  cheap: the program-language `+` and the proof-language `+` never
  meet.
- Comparison operators could bind to `cmp`-shaped functions
  (`a < b` ⇒ `cmp(&a,&b) == -1`), though the iff-post pattern means
  the desugaring must pick a result convention; worth deciding
  separately.
- Open choices: declaration syntax and placement (module-level `///
  operator` clause vs. inside the class body), whether `&`-insertion is
  implicit at the operands (probably yes — the operator declaration
  fixes the signature), and whether mixed-type operators are allowed
  (defer).

## 2. Operators in templates (the real prize, much bigger)

For `T: Addable`-style bounds to mean anything, type parameters must
range over **class types**, not just the eight integer types (ADR
0006/0009 currently model a parameter as an `IntModel` — two bounds).
That is a design milestone of its own:

- The concept model of a class-type parameter is its **spec-function
  vocabulary** (ADR 0007's law-carrying traits generalized to classes):
  a bound `T: Addable` would contribute an abstract value-map (e.g.
  `T_val : T → int`) plus the operator laws as hypotheses
  (`T_val (a + b) = T_val a + T_val b` — the homomorphism shape the
  bignum posts already have).
- Monomorphization, the interpreter, and the SVM never see a type
  variable today; class-typed parameters keep that invariant (mono
  expands as usual), but template *verification* needs the abstract
  model above.
- Recommendation: do sugar (§1) when convenient; treat §2 as its own
  ADR gated on a forcing benchmark (a generic algorithm someone
  actually wants over `Nat` — e.g. a generic `pow`/fold — the same way
  bignum forced class values).

## Suggested path

1. `/// operator` declarations + desugaring for concrete classes
   (parser/check sugar; zero vcgen/Lean changes). Bignum's `div`/`gcd`
   become the showcase.
2. A later ADR: "type parameters over classes", with the trait-law
   model — operators in templates fall out of it.
