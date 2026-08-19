# ADR 0091 — checked control plans travel with the program

**Decided 2026-08-19.** A production consumer may not rebuild lexical-control
identity from a typed AST after checking. The exact `ControlOutline` drives
Lean-free checking; the `ControlProgram` sealed for that AST then travels beside
it through VC generation, Lean verification, interpretation, formal-machine
lowering, and native lowering.

**Follow-on:** ADR 0092 moves structural planning before the checker, retains
typed block/branch/loop/exposure plans, and adds direct VC/SVM/trap/assignment/
class-drop consumers. The carrier and provenance rule decided here are
unchanged.

## Context

ADR 0089 introduced `BodyPlan`, but the interpreter and LLVM backend each
built their own instance. VC generation and SVM lowering still had no retained
plan at all. Even a deterministic rebuild left an architectural hole: a later
stage could accept a same-named or mutated body, assign different scope/drop
identities, and still appear to consume the same checked program.

The formal SVM also had a flat environment. Falling out of a machine frame
discarded it, but branch arms, loop iterations, and exposure bodies had no
operation that ended a lexical binding. Passing a `BodyPlan` to that lowerer
without changing the machine would therefore have been metadata plumbing, not
shared cleanup semantics.

## Decision

`ControlProgram` is the flavor-preserving table of callable `BodyPlan`s. Its
key is `CallOwner`, so an initializer and method with the same source spelling
remain distinct. It covers executable functions, retained function templates,
and concrete/template class initializers, methods, and deinits. Duplicate and
missing semantic owners are named internal refusals; there is no production
fallback that rebuilds a body plan.

The checker now constructs a total `ControlOutline` before its flow-sensitive
walk, then seals the `ControlProgram` only after the typed, monomorphized AST has
passed checking (ADR 0092). `CheckedProgram`, artifact preparation, and
`VerifiedProgram` retain that same table beside the exact AST. Production
interpreter, SVM, VC, and LLVM entry points resolve their canonical callable
through it. Focused unit lowerers and the raw interpreter helper remain compiled
only for library unit tests. Integration-level operational trap probes render a
separate source, pass it through the Lean-free checker, and execute the resulting
`CheckedProgram`; no normal public entry point rebuilds control from a raw AST.

`BodyPlan` now records every source local whose lexical lifetime ends on a
route, in addition to runtime drop candidates. It also owns compiler-only SVM
temporary identities:

- Boolean-literal element temporaries close with their lexical scope;
- exposure loan/index/byte scratch survives the exposure body, then closes
  after normal copyback and raw release;
- an explicit return result slot lives outside the unwound source scopes.

The names use a source-inexpressible namespace and structural scope/source
anchors. Repeated lowering of the same checked exposure is byte-identical.

The Lean SVM gains three explicit statements and corresponding inductive and
executable semantics:

- `scopeExit` removes the plan's lexical bindings;
- `moveLocal` atomically moves an owned result to a fresh compiler slot;
- `retUnit` represents an early `return;` rather than confusing it with
  falling off an outer continuation.

`SVMEval.stepF` remains proved equivalent to `Step` for all three. Valued and
unit returns execute their lexical route before returning. They do not emit
the frame route first: `ret`/`retUnit` must read callee parameters to restore
unique loans, then the machine return rule discards the frame. Thus frame
cleanup is fused with formal return, while interpreter and LLVM retain their
existing postcondition-aware route phases.

Traps still do not unwind. Result evaluation or an earlier exposure operation
that traps prevents every later `scopeExit`, copyback, release, or return step.

## Evidence

Structural tests pin exact typed-owner lookup, duplicate/missing refusal,
inner-to-outer return and backedge order, empty trap cleanup, compiler temporary
lifetimes, and deterministic reconstruction scratch. The SVM integration test
inspects emitted terms for branch fallthrough, loop backedge, exposure close,
return, and trap ordering. A source regression returns early from a nested arm
of a function with a unique Boolean-array loan; all 148 SVM differential
subjects agree with the checked interpreter. `lake build` checks the new
machine rules, evaluator agreement, and focused guards.

## Boundary

This tranche did **not** close ADR 0086 criterion 3. Its missing VC structured
edges and exact trap/assignment/destruction actions are supplied by ADR 0092:
production consumers now use retained block flow, branches, loops, exposures,
routes, and direct trap sites, and the interpreter/LLVM consume concrete class
drop plans. Exact local/field replacement and discarded-class temporary actions
link to the checker ownership plan, and SVM directly consumes the admitted trap
and assignment subset before lowering or named refusal. ADR 0092 therefore
closes criterion 3 and C0.

Dynamic arming, moved-field presence, native null/neutral storage, and concrete
value representation remain consumer state rather than duplicated policy.
`BodyPlan` is a structured typed control/action plan, not a full expression CFG
or a mechanized translation proof.
