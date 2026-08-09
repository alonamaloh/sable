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
