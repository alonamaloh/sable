# ADR 0012 — Operator bindings for concrete classes

Date: 2026-08-10. Status: accepted, implemented. Template operators
explicitly out of scope (future ADR).

## Context

With the bignum pillar verified, arithmetic on `Nat` reads as
`q = add(&q, &m)` where `q = q + m` says the same thing better
(Alvaro, 2026-08-10). The enabling observation: in Sable, **the
program-language `+` and the proof-language `+` never meet.** Contracts
about class values speak through ghost functions
(`natVal a.limbs + natVal b.limbs`), and that `+` is Lean's own —
there is nothing to overload on the proof side, so operator sugar is
purely front-end.

An earlier draft put the declaration on a `///` line; rejected —
operator binding changes how *program text* elaborates and has no
proof-language content. It is a program-language item.

## Decision

A top-level program declaration binds an operator to an existing
contracted function:

```sable
operator +   = add;
operator -   = sub;
operator *   = mul;
operator /   = div;
operator %   = rem;
operator cmp = cmp;
```

- **Arithmetic** (`+ - * / %`) binds `fn (&C, &C) -> C` — same class on
  both sides, value result. `a + b` rewrites, in the checker, to the
  bound call with borrows inserted at the operands; every downstream
  stage (vcgen, interpreter, monitor, Lean) sees the ordinary call, so
  pres flow to the use site and posts flow out exactly as with an
  explicit call. Obligation and hypothesis names are those of the call
  — the bignum corpus was rewritten to operators with **zero** discharge
  churn.
- **Comparisons** bind once through `operator cmp` to a
  `fn (&C, &C) -> i32` under the −1/0/1 convention: `a < b` rewrites to
  `cmp(&a,&b) < 0`, and the same shape serves all six relations
  (`==` ⇒ `= 0`, `!=` ⇒ `≠ 0`, …). One declaration, six operators;
  the meaning comes from the bound function's posts (bignum's `cmp`
  carries the three iffs plus a range post).
- **Resolution** is by operand class: several classes may each bind the
  same symbol. Operands must be *named* class values (locals or
  parameters) — nesting like `(a + b) + c` needs an intermediate `var`,
  because borrows take names. Mixed-class operands are diagnosed
  (`op.operand_mismatch`); unbound use, bad signatures, and duplicate
  bindings are named errors (`op.unbound`, `op.bad_signature`,
  `op.duplicate`), each with a must-fail guard.
- **No laws are implied.** For concrete classes the operator is syntax;
  semantics is entirely the bound function's contract. (In templates,
  operators *would* be law-carrying by construction — that is exactly
  why they are deferred to the type-parameters-over-classes ADR, gated
  on a forcing benchmark, per `docs/notes/operator-overloading-sketch.md`.)

## Consequences

- Class reassignment composes: `q = q + m;` checks the rewritten call
  against the move-in rule (the checker rewrites before validating the
  RHS kind).
- Conditions compose: `while (r >= b)` is the condition-call form with
  the comparison rewrite inside; posts bind to both path directions as
  established in M17.
- Diagnostics after the rewrite name the bound function; the operator
  form appears only in source spans.
