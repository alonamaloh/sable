# ADR 0010 — First-class class values, slice A: shared borrows and returns

Date: 2026-08-10. Status: accepted (slice A); moves/`&mut`/class fields deferred.

## Context

Since M5, class values are local-only: constructed with `var`, used via
method calls, dropped at scope end. Init/method parameters are integers
only; nothing takes or returns a class. Bignum's natural interface —

```
fn add(&Nat a, &Nat b) -> Nat
```

— needs exactly three things: **shared class borrows as parameters**,
**class returns**, and **field reads on borrowed class values**
(`a.limbs[i]`, `a.len`). It needs neither `&mut Nat` parameters (the
arithmetic functions return fresh values), nor moves, nor class-valued
fields. Slice A delivers the bignum-sufficient surface; the rest waits
for a forcing benchmark, like every other deferral in this project.

## Decision

**Surface.**
- `&C name` parameters — shared borrows of a class, syntactically
  parallel to `&[T]`. `&mut C` is diagnosed as deferred.
- `-> C` returns — the callee returns an owned class value (a local
  moving out). Callers bind it with `var`.
- Call sites borrow explicitly: `add(&a, &b)` — same rule as arrays.
- Field **reads** on class-typed names: `a.f`, `a.f.len`, `a.f[i]`.
  Writes remain `self`-only (there is nothing mutable to write through
  in slice A).
- Specs need no new surface at all: a borrowed class is a Lean
  structure value, so clauses write `a.limbs.get i`, `result.len`,
  and class invariants apply as always.

**Verification model** — entirely M5 machinery, re-aimed:
- A `&C` parameter binds `(a : C)` with field facts and the class
  invariant as hypotheses (the method-entry `_old_self` treatment).
- A class result at a call site binds a fresh post-state with field
  facts, the invariant, and the callee's posts (the `CtorCall` result
  treatment).
- Two new obligation kinds keep the bookkeeping kernel-checked rather
  than meta-argued:
  - `ret_inv`: at `return n;` of a class, the invariant holds of the
    returned state. Closes by assumption — local class states are
    init/method post-states, which carry the invariant — but it is an
    obligation, not a trust step.
  - `borrow_inv`: at a call site, each borrowed class argument
    satisfies its invariant. Same status.

**Runtime.** Borrows pass the reference; returns move the value out
(the callee's drop check skips it); RAII drop stays caller-side.

## Deferred (slice B, when forced)

Moves and copies (classes are affine; passing by value is a move),
`&mut C` parameters (requires field writes through borrows and the
fresh-state call-site treatment arrays get), class-valued fields (drop
order), methods taking/returning classes, borrows of generic class
instances.

**Slice B, partly landed — see ADR 0020**: class-valued fields, by-value class parameters (moves), and borrowing a class field. `&mut C`, local-to-local moves, and generic-class field borrows remain deferred.

**Landed since (forced by bignum division):** shared re-borrow of `&C`
parameters (passing a borrow along to a callee), and class-local
reassignment from call/constructor results — a move-in; the old value is
dropped with its RAII invariant check, and loop havoc assumes the class
invariant for reassigned locals (sound: every source carried `ret_inv`).
Local-to-local moves remain deferred (`class.move_deferred`).
