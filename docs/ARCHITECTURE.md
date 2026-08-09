# Architecture

One sentence: **the Rust compiler owns the program language; Lean owns the proof language; verification is Lean-file generation.**

## Division of labor

The Rust compiler never understands proof expressions. It tokenizes `///` content only enough to find block boundaries and clause keywords (`pre`, `post`, …). Everything else about the proof language — elaboration, typing, semantics — belongs to Lean: proof-language text is spliced nearly verbatim into generated Lean files and elaborated against the `Sable` prelude (`lean/Sable/`). The proof language *is* Lean; there is no second implementation of it to drift.

There is **no external SMT solver**. Routine obligations are discharged by an automation portfolio inside Lean (`sable_auto`: `assumption`/`omega`/`simp_all`/`grind`, see `lean/Sable/Auto.lean`); every proof, automated or hand-written, is checked by the Lean kernel. Stage-1 trust (design §10.1) = the Rust VCgen/emitter; nothing else.

## Pipeline

```
foo.sable
  │  scan: split proof lines (///) from program text; group into blocks;
  │        attach blocks positionally (doc-comment rule)
  ▼
parse (compiler/src/parser.rs)        handwritten recursive descent, error recovery
  ▼
typecheck (compiler/src/check.rs)     types, definite initialization, call graph
  ▼
vcgen (compiler/src/vcgen.rs)         forward symbolic execution over the AST;
  │                                   values are Lean `Int` expression strings;
  │                                   path-splitting at `if`; per-operation VCs;
  │                                   call sites: callee pres become obligations,
  │                                   callee posts become hypotheses on a fresh symbol
  ▼
emit (compiler/src/lean.rs)           one Lean theorem per obligation:
  │                                     binders = params + intermediate symbols,
  │                                     hypotheses = range facts + pres + path conditions,
  │                                     proof = `by sable_auto` (or spliced discharge, M1);
  │                                   records a source map: lean lines → obligation
  │                                   (name, .sable span, goal text, context)
  ▼
check                                 `lake env lean --json` on the generated file
  ▼                                   (prelude oleans built once by `lake build`)
diagnose (compiler/src/diag.rs)       lean JSON messages → source map lookup →
                                      rendered error: obligation name, goal,
                                      .sable span, context, lean excerpt
```

Generated Lean goes to `.sable-out/` (gitignored), one file per module, `import Sable` / `open Sable` at the top.

## Key invariants

- **Verbatim splice.** Contract clauses appear in generated Lean exactly as written (module call-site substitution of parameter names by argument expressions). Generated theorems bind program variables under their source names so clauses elaborate unchanged. If a clause doesn't elaborate, the error must point at the `.sable` clause, not at generated code.
- **Every obligation is named** and the name is stable across unrelated edits (M0: expression-slug anchors; the design's content-anchoring scheme replaces this). Lean theorem names are sanitized versions; user-facing names live in the source map.
- **Values are exact integers.** Program integers are represented in Lean as `Int`; per-operation VCs guarantee representability, so symbolic values never wrap. `wrap()` etc. (later) get explicit `mod 2^n` semantics.
- **The prelude depends on Lean core only** — no mathlib. Cold-start and toolchain churn stay controlled; the multiset library (M2) is written in-repo.

## `sable test` (dynamic checking)

A separate, Lean-free path (design §9): `interp.rs` is a tree-walking
interpreter with trap semantics (overflow/bounds/division checked exactly
where the verifier emits VCs), and `speceval.rs` evaluates the
*monitorable fragment* of the proof language (arithmetic, logic, sequence
access, `old`, guard-bounded quantifiers, ghost-def expansion, option
match, `perm` as multiset equality). Pres/posts/invariants/variants are
checked dynamically; anything outside the fragment is reported as
skipped, never guessed — this is best-effort dev tooling, not a second
checker of record. `test_*` functions are its entry points and are never
verified. Escape hatches: `defer` skips an obligation's theorem but keeps
its downstream assumption (trap semantics); `assume` does the same as an
audited axiom; both are tallied in the build report.

## Repo layout

```
docs/design/       normative language design + roadmap
docs/PLAN.md       milestones and exit criteria (kept current)
docs/decisions/    ADRs — one settled decision each, with the why
compiler/          Rust package `sable` (single crate until it hurts; split when it does)
lean/              Lake package: Sable prelude; pinned via lean-toolchain
corpus/verifies/   programs that must verify
corpus/must-fail/  programs annotated with the exact diagnostic that must fire
.sable-out/        generated Lean (gitignored)
```

## Toolchain pins

Lean is pinned by `lean/lean-toolchain` (elan resolves it). Upgrades are deliberate, tested against the corpus, and get a commit of their own. Rust: whatever stable cargo is current; no nightly features.
