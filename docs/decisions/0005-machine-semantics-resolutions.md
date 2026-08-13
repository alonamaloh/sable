# ADR 0005 — Machine-semantics resolutions from the first SVM formalization audit

**Decided 2026-08-09 (Alvaro, from the 11 findings in `docs/notes/svm-draft.md`).**

Writing the first 73 rules of the SVM (`lean/Sable/SVM.lean`) forced eleven decisions the design prose had left open. Resolutions:

1. **⊥-reads get a third terminal outcome, `undef`** — alongside `done` and `trapped`. The machine is total, so pillar 1 holds literally (an `undef` outcome *is* a defined meaning); it costs nothing at runtime; and the soundness theorem sharpens to "verified programs never reach `undef`". Definite initialization remains a static-only check (not deferrable — a runtime ⊥-check would require shadow state native compilation shouldn't pay for).
2. **`wrap()` / `checked()` / `sat()` are operator modifiers with whole-subexpression scope.** They cannot be functions (their argument would trap while being evaluated). Every arithmetic operator lexically inside the form is modular/checked/saturating in its operand type's width — not crossing into called functions or index computations. Signed `wrap` is two's-complement.
3. **The normative machine is the structured (AST-level) small-step semantics.** §10's "typed stack machine" language is retired: no instruction set was ever specified, and the honest rule count is ~2× the prose estimate once trap propagation is explicit. A lower-level machine may appear later as a *compilation target with a refinement proof*, not as the language's meaning.
4. **Calls are A-normalized in the machine**: they exist only as statement-level `x = f(args)`; the compiler desugars nested calls (surface syntax unchanged). Expressions stay pure and big-step; frames and divergence live only in the statement layer.
5. **Evaluation order is left-to-right, normatively** — trap identity depends on it (`a[bad] = 1/0` traps on the index, evaluated first: index → value → bounds check for stores).
6. **`&&` / `||` short-circuit, normatively** — the guarded-VC idiom (`i < a.len && a[i] > 0`) requires it.
7. **Allocation is capacity-parameterized**: `Step`/`Eval` take a capacity `cap`; OOM is the defined trap when it is exceeded; soundness statements quantify over `cap`. This reconciles "deterministic machine" with "allocation may fail".
8. **Procedures are blessed**: functions without a return type exist; falling off the end returns unit; posts are proven at the implicit return.
9. **Ghost-state transitions are deferred** to the erasure-metatheorem design (the `ghost` configuration component stays, unpopulated, with a scheduled-work note).
10. **Trap payloads**: machine traps carry structural data (index, length, operand); which of it is *observable* is deferred to the FFI/native story. `defer`'s obligation names must survive into machine syntax (`check name` statements).
11. **Minor batch**: out-of-range literals are checker duty; unary minus on unsigned is a type error; `alloc_array` lengths are `u64` (nonnegative by typing); `bool ==` and mixed-width comparisons are checker restrictions, the machine compares on ℤ; `a.len` is `u64`-typed with `len ≤ u64.max` as a machine axiom.

Next SVM-track steps (unchanged): determinism proof, functional evaluator + agreement proof (the differential-testing oracle), then calls/frames under resolution 4. The formalization must be updated to add the `undef` outcome.

## G1.2 amendment: ordinary option shape and failure outcomes (2026-08-13)

The formal SVM now represents an ordinary option as
`Val.opt : Option Val`, rather than `Option Int`. Its `someE` and `noneE`
constructors and `optIsSome`/`optValue` accessors are generic over machine
values in both the relational semantics and the proved functional evaluator.
This fixes two outcome choices under resolutions 1 and 10:

1. Applying an ordinary-option accessor to a value with the wrong outer shape
   is type confusion and therefore reaches `undef`.
2. Applying `.value` to a well-shaped absent option reaches the observable
   language trap `Trap.optionNone`, not `undef`.

Ordinary options and nullable raw-pointer options remain distinct value forms,
so crossing those accessor domains is also shape confusion. Rendering remains
compatible for existing integer observations (`opt none`, `opt some 7`) and
adds compact Boolean observations (`opt some false`, `opt some true`).

The recursive formal value does not widen the checked source or ABI surface.
Rust lowering accepts only concrete integer/Boolean options in G1.1's
ordinary-function return/local intersection, including contextual
construction, assignment, A-normal call transport, and access. Option
parameters and fields, trait returns, record/nested payloads, Boolean arrays,
residual or Boolean generic arguments, classes/method calls, and audited
externs remain fail closed. The preclosure focused evidence was green: one-job Lake build,
`cargo check`, 123/123 Rust library tests, 13/13 focused SVM units, and exact
Rust↔Lean differential agreement on 76/76 subjects.

G1.2 closed together with G1.3 under
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`. The run
passed 129/129 library tests; all 374 corpus subjects (80 verifies, 231
must-fail, 45 dynamic, 18 dynamic-fail) in 414.80s; LLVM CLI 6/6; the
exact-`VerifiedProgram` interpreter↔Clang differential over four subjects at
both `-O0` and `-O2`; SVM differential 76/76; and the randomized allocator,
grind-budget, LSP, and documentation gates. G1.2 is closed.

## G1.4b boundary note: no Boolean-array machine value yet (2026-08-13)

G1.4b adds a checked, verified, interpreted, and dynamically monitored
owned-local `[bool]` slice without changing the normative SVM. The Rust SVM
lowerer rejects every Boolean-array declaration before machine syntax is
produced, and the Lean value/rule/evaluator layers acquire no Boolean sequence
value, allocation rule, index rule, store rule, or observation spelling. The
existing 76/76 differential remaining green therefore demonstrates boundary
preservation, not formal-machine coverage of the new source feature.

This stage still gives out-of-bounds indexing defined language behavior: the
Rust interpreter uses the established array trap. That executable behavior is
not yet a claim that the formal SVM models Boolean-array allocation or traps.
A dedicated formal-machine stage must add the value representation, relational
and executable rules, their two-directional agreement proof, direct guards,
and Rust↔Lean differential subjects before the lowerer may accept `[bool]`.
That stage is G1.5; LLVM array lowering remains independently deferred.
