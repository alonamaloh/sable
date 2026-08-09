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
mono (compiler/src/mono.rs)           monomorphization (ADR 0006/0007): expands
  │                                   every generic instantiation (mangled names,
  │                                   bare-token clause substitution, T.max → i32.max);
  │                                   consumes traits/impls — impl bodies become
  │                                   plain contracted fns, impl spec defs become
  │                                   module ghost defs, K::m resolves to the impl;
  │                                   bounds checked here (mono.unsatisfied_bound).
  │                                   No later stage sees a type variable.
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
  ▼                                   (prelude oleans built once by `lake build`);
  │                                   or, when `sable daemon` is running
  │                                   (socket at .sable-out/daemon.sock), a warm
  │                                   Lean LSP server checks it without the
  │                                   per-invocation cold start (compiler/src/daemon.rs);
  │                                   any daemon problem falls back to the batch path
diagnose (compiler/src/diag.rs)       lean JSON messages → source map lookup →
                                      rendered error: obligation name, goal,
                                      .sable span, context, lean excerpt
```

Generated Lean goes to `.sable-out/` (gitignored), one file per module, `import Sable` / `open Sable` at the top.

## Key invariants

- **Verbatim splice.** Contract clauses appear in generated Lean exactly as written (module call-site substitution of parameter names by argument expressions). Generated theorems bind program variables under their source names so clauses elaborate unchanged. If a clause doesn't elaborate, the error must point at the `.sable` clause, not at generated code.
- **Every obligation and every hypothesis is named by content.** Hypothesis names are content-anchored slugs (`h_pre_sorted_a`, `h_inv_<slug>`, `h_path_<slug>`, `h_<callee>_post_<slug>`, `h_cinv_<slug>`; same-slug collisions get `_2` suffixes rather than shadowing) — discharge scripts survive unrelated edits. Obligation names are `fn.kind.<expression-slug>`; the design's `#[label]` refinement is still open. Lean theorem names are sanitized versions; user-facing names live in the source map.
- **Binders carry source names.** A call/alloc/ctor result bound to a local binds under the local's name (`u64 p = probe_step(...)` → binder `p`, hypothesis `h_p_range`), not a positional `_r16`; a `&mut` method call rebinds the receiver's name (`m_2`); the mid-loop self state is `_self_loop`. Same motivation as content-anchored hypotheses: discharge scripts must survive unrelated edits.
- **Havoc is SSA-style versioning.** At a loop head, binders holding havocked names are renamed to stale versions (`_oldN_x`) and surviving hypotheses are *rewritten* to the stale names under `h_stale_*` — facts about pre-loop values (e.g. alloc facts) stay available instead of being dropped; fresh loop-invariant hypotheses keep the content-anchored names. Mid-method `self` havoc keeps *only* the loop invariants (the class invariant is not in force mid-method, design §7): a self-mutating loop states its full working payload — lengths, element facts, and a frame invariant against `old self` — as loop invariants. Record-field projections through update chains are reduced at generation time (`{ x with vals := v }.occ` → `x.occ`), so goals stay over stable atoms omega can use.
- **Values are exact integers.** Program integers are represented in Lean as `Int`; per-operation VCs guarantee representability, so symbolic values never wrap. `wrap()` etc. (later) get explicit `mod 2^n` semantics.
- **The prelude depends on Lean core only** — no mathlib. Cold-start and toolchain churn stay controlled; the multiset library (M2) is written in-repo.
- **The specification vocabulary lives in the prelude** (`lean/Sable/Specs.lean`): `sorted`, `sortedRange`, `perm`, `contains`, `count` — reducible abbrevs (discharge scripts apply their hypotheses directly), `@[simp]` where unfolding helps automation (`perm` stays opaque behind its lemma library), each with a native evaluator in the monitorable fragment. Program identifiers may shadow these names; the program binding wins in clauses.

## `sable test` (dynamic checking)

A separate, Lean-free path (design §9): `interp.rs` is a tree-walking
interpreter with trap semantics (overflow/bounds/division checked exactly
where the verifier emits VCs), and `speceval.rs` evaluates the
*monitorable fragment* of the proof language (arithmetic, logic, sequence
access, `old` — including `(old obj).field` chains, guard-bounded ∀/∃,
ghost-def expansion with `if … then … else`, option match, `perm` as
multiset equality). Pres/posts/invariants/variants are
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
corpus/verifies/   programs that must verify (status: fully verified)
corpus/must-fail/  programs annotated with the exact diagnostic that must fire
corpus/tests/      dynamic-test programs: sable test must pass, zero skipped clauses
corpus/test-fails/ dynamic tests that must be caught, annotated with the message
docs/notes/        probe files and audit notes (SVM draft findings, class encoding)
editors/           Neovim setup + VS Code extension
.sable-out/        generated Lean + daemon socket (gitignored)
```

## Toolchain pins

Lean is pinned by `lean/lean-toolchain` (elan resolves it). Upgrades are deliberate, tested against the corpus, and get a commit of their own. Rust: whatever stable cargo is current; no nightly features.
