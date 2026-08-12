# ADR 0009 — Concepts: type preconditions and template-level verification

Date: 2026-08-10. Status: accepted (design); implementation staged.

## Context

Generics v1 (ADR 0006) verifies each monomorphized instance separately.
The cost is now measured: 8 duplicated discharges per `Vec` instance,
27 per `HashMap` instance — and the duplicated proofs are *identical*
modulo mangled names, because every hand proof we have ever written for
generic code is already type-generic (the probe files prove the hash-map
lemmas over an abstract `hm : Int → Int`; nothing in them mentions
`i32`). The duplication is a pipeline artifact: VCgen runs after
monomorphization, so it only ever sees instances.

Alvaro's framing (2026-08-09): C++-concepts done right — **preconditions
on the types entering a template**. Verify the templated code once,
against those preconditions; at instantiation, check only that the
concrete types satisfy them.

## Why Sable is better-positioned than C++

A Sable type parameter has almost no semantic content. Values are exact
Lean `Int`s everywhere; the entire meaning of an integer type is a pair
of bounds plus range facts at operations. So the abstract model of a
type parameter is two integers:

```lean
structure IntModel where
  min : Int
  max : Int
```

C++ concepts check *syntax* at instantiation. Sable concepts check
*lemmas* — and for integer types, satisfaction is `omega` on two
literals.

## Decision

1. **The type model.** A template type parameter `T` verifies against
   `(T : Sable.IntModel)` with the *universal facts* every Sable integer
   type satisfies, bundled as `IntModel.wf`:
   `T.min ≤ 0 ∧ 0 < T.max ∧ i64.min ≤ T.min ∧ T.max ≤ u64.max`.
   Clause text needs **no rewriting**: `T.min`/`T.max` elaborate as-is
   via field projection — the verbatim-splice invariant is preserved.

2. **Declared preconditions.** A generic declaration may add
   `/// requires <prop about T.min/T.max/...>` clauses. They become
   hypotheses of every template obligation, and per-instantiation
   obligations (`{instance}.requires.{slug}`) at each use — normally
   closed by `sable_norm`+omega, since they are numeric facts about
   literal bounds.

3. **Template verification.** Check + VCgen run on the *template*
   (pre-mono), with `TParam` rendered through the model: range facts
   use `T.min`/`T.max`, obligations bind `(T : Sable.IntModel)`
   `(h_T_wf : T.wf)` plus the `requires` hypotheses. Discharges are
   written once, against template obligation names.

4. **Monomorphization is unchanged for code** (ADR 0006 stands: the
   interpreter, emitter, and SVM never see a type variable). Instances
   of template-verified declarations skip their own obligation
   generation; they keep their substituted contracts for call sites,
   and owe only the `requires` obligations.

5. **Trait bounds fold in.** A bound `K: Hashable` contributes, at the
   template level, an abstract spec function `(K_hash : Int → Int)`
   plus the trait's method contracts as hypotheses — exactly the shape
   the hand-written probe lemmas already use. ADR 0007's per-impl law
   verification is unchanged; it is what licenses the instantiation.

## Soundness note

The trusted step is that monomorphic substitution commutes with VC
generation: the instance's would-be VCs are the template's VCs with the
concrete model substituted. This is a Stage-1-trust argument (the VCgen
is already the trusted base, design §10.1); the per-type `wf` lemmas
are proven once in the prelude, and the `requires` residue is
kernel-checked per instantiation.

## Staging

- **Slice 1**: template verification for generic *functions* without
  trait bounds; `requires` clauses; instance skip + requires
  obligations. Acceptance: a generic corpus function verified once.
- **Slice 2**: generic *classes* (`Vec<T>` — acceptance: its 8-per-
  instance discharges collapse to one template set).
- **Slice 3**: trait-bounded templates (`HashMap<K, V>` — acceptance:
  the 27-per-instance discharges collapse).

## Consequences

- Template-level discharges (the ADR 0006 deferred cost) cease to
  exist as a separate feature — they are just discharges.
- `widen`/`narrow` touching a type parameter demand `requires` bounds
  relating `T` to the concrete target (slice 1 forbids them; a later
  slice adds the requires-driven rule).
- Literals used at type `T` (e.g. `alloc_array<T>(n, 0)`) generate
  range obligations against `T.min`/`T.max`, dischargeable from `wf`
  or `requires`.

## G1.0 amendment: explicit proof provenance (closed 2026-08-12)

The original implementation represented a declaration type parameter through
`IntTy::TParam` and carried template proof reuse as an optional template name.
That was adequate while every legal instantiation was an integer, but it was
not an adequate boundary for G1: a future Boolean or POD instance must not look
integer-valued by representation or inherit a theorem proved only over
`Sable.IntModel`.

G1.0 therefore makes both facts explicit:

1. Declaration positions use `Ty::Param(TypeParamId)`; array and option
   payloads use `ValueTy::{Int, Bool, Record, Param}`. The legacy
   `IntTy::TParam` remains only where integer syntax still requires it, such as
   conversion targets, and may not stand in for a declaration parameter.
2. A concrete instance may reuse a template proof only through
   `ProofReuse::Adr0009IntModel` with an opaque authorization payload. The
   payload fields are private and its constructor is crate-private: an external
   AST caller can inspect the authorization but cannot forge it.
   Monomorphization rejects any pre-populated marker and is the only pipeline
   pass that authors this capability. VC generation skips instance obligations
   only for that exact variant. Preparation and VC-generation entry points are
   crate-private, closing the corresponding external direct-call path.
3. Before substitution, monomorphization validates every declaration parameter
   id and rejects out-of-bounds or noncanonical forms. After expansion it checks
   exhaustively that every ordinary declaration is concrete; only retained
   templates may contain `Param`.
4. Boolean and POD payloads have representation but no semantics at this
   checkpoint. The checker and VC generator reject them independently; the
   interpreter and SVM repeat the fail-closed guard at their execution and
   lowering boundaries. Module visibility still descends through nominal
   record payloads.

This amendment narrows the authorization described in decision 4; it does not
widen ADR 0009's proof domain. Existing integer instances retain their behavior.
The next semantic slice is `option<bool>`.

G1.0 is closed by
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`. The run
passed 101/101 library tests; all 368 corpus subjects (79 verifies, 228
must-fail, 44 dynamic, 17 dynamic-fail) in 382.78s; LLVM CLI 6/6; the exact
`VerifiedProgram` interpreter↔Clang differential at `-O0` and `-O2` 1/1; and
SVM differential 69/69. The randomized allocator, grind-budget, LSP, and
documentation gates were green.
