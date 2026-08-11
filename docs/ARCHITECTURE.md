# Architecture

One sentence: **the Rust compiler owns the program language; Lean owns the proof language; verification is Lean-file generation.**

## Division of labor

The Rust compiler never understands proof expressions. It tokenizes `///` content only enough to find block boundaries and clause keywords (`pre`, `post`, …). Everything else about the proof language — elaboration, typing, semantics — belongs to Lean: proof-language text is spliced nearly verbatim into generated Lean files and elaborated against the `Sable` prelude (`lean/Sable/`). The proof language *is* Lean; there is no second implementation of it to drift.

There is **no external SMT solver**. Routine obligations are discharged by an automation portfolio inside Lean (`sable_auto`: `assumption`/`omega`/`simp_all`/budgeted `grind`, see `lean/Sable/Auto.lean`); every proof, automated or hand-written, is checked by the Lean kernel. The grind tier runs under a heartbeat budget (`sable.grindHeartbeats`, ADR 0011): exceeding it fails the obligation promptly instead of churning, and a success spending ≥ 1/5 of the budget is reported as a warning diagnostic — obligation name, clause span, and a minimized `discharge` suggestion from `grind?` — with the corpus held warning-clean by the harness. Stage-1 trust (design §10.1) = the Rust VCgen/emitter; nothing else.

## Pipeline

```
foo.sable
  │  load (compiler/src/modules.rs)   resolve `use` imports (ADR 0013): DFS over the
  │                                   module DAG (cycle-checked, canonical-path dedup),
  │                                   each file scanned/lexed in place within a
  │                                   combined source string; imported class names
  │                                   seed dependent parses; flat merge → ONE Program.
  │                                   Every later stage is module-oblivious;
  │                                   ModuleSet.locate maps any span back to its
  │                                   (file, line, col) for rendering.
  │  scan: split proof lines (///) from program text; group into blocks;
  │        attach blocks positionally (doc-comment rule)
  ▼
parse (compiler/src/parser.rs)        handwritten recursive descent, error recovery;
  │                                   bare string literals desugar here to a hidden
  │                                   [u8] temp + String::from_bytes(&temp) (ADR 0015)
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
typecheck (compiler/src/check.rs)     types, call graph, and one flow-sensitive
  │                                   pass carrying definite initialization and
  │                                   affinity together (ADR 0020/0021: initialized
  │                                   iff every reaching branch initialized it,
  │                                   moved iff any reaching branch moved it —
  │                                   a branch that returns reaches nothing);
  │                                   ownership is keyed by `Place` (root + field
  │                                   path) with `contains`/`overlaps`, so a field
  │                                   is a place in its own right and a mutable
  │                                   borrow overlapping another in one call is
  │                                   rejected (ADR 0022/0023); the same engine
  │                                   tracks resources — authority the checker
  │                                   keeps affine, whose *view* is all the logic
  │                                   sees and which the runtime never sees at
  │                                   all (ADR 0024);
  │                                   operator-binding rewrite (ADR 0012: `a + b`
  │                                   on class values becomes the bound
  │                                   contracted call)
  ▼
vcgen (compiler/src/vcgen.rs)         forward symbolic execution over the AST;
  │                                   values are Lean `Int` expression strings;
  │                                   path-splitting at `if`; per-operation VCs;
  │                                   call sites: callee pres become obligations,
  │                                   callee posts become hypotheses on a fresh symbol;
  │                                   `&mut` arguments (arrays, classes, `&mut self`)
  │                                   are havocked at the call and at every loop
  │                                   head, with the entry state kept for `old p`
  │                                   (ADR 0023)
  ▼
emit (compiler/src/lean.rs)           one Lean theorem per obligation:
  │                                     binders = params + intermediate symbols,
  │                                     hypotheses = range facts + pres + path conditions,
  │                                     proof = `by sable_auto` (or spliced discharge, M1);
  │                                   per-module (compiler/src/artifacts.rs, ADR 0018):
  │                                   imports name dep artifacts, name subtraction
  │                                   keeps one declaration per DAG;
  │                                   records a source map: lean lines → obligation
  │                                   (name, .sable span, goal text, context)
  ▼
check                                 `lean --json` on the generated file, LEAN_PATH =
  ▼                                   workspace + .sable-out/modules
  │                                   (prelude oleans built once by `lake build`);
  │                                   or, when `sable daemon` is running
  │                                   (socket at .sable-out/daemon.sock), a warm
  │                                   Lean LSP server checks it without the
  │                                   per-invocation cold start (compiler/src/daemon.rs);
  │                                   any daemon problem falls back to the batch path;
  │                                   a client killed mid-check cancels the check
  │                                   (didClose terminates the file's worker — no
  │                                   orphaned lean processes grinding on dead work)
diagnose (compiler/src/diag.rs)       lean JSON messages → source map lookup →
                                      rendered error: obligation name, goal,
                                      .sable span, context, lean excerpt
```

Generated Lean goes to `.sable-out/` (gitignored): one stable file per checked root, plus one **content-addressed artifact per module** under `.sable-out/modules/` (`<stem>_<hash>.{lean,olean,ok}`, ADR 0018). Verification is separate: an imported module's obligations verify once into its artifact and importers `import` it — the hash covers the generated content and the prelude, dep names pin transitively, and `.ok` exists only for kernel-checked successes, so cache validity is mere existence. Roots re-verify their own file every check.

## Key invariants

- **Verbatim splice.** Contract clauses appear in generated Lean exactly as written (module call-site substitution of parameter names by argument expressions). Generated theorems bind program variables under their source names so clauses elaborate unchanged. If a clause doesn't elaborate, the error must point at the `.sable` clause, not at generated code.
- **Every obligation and every hypothesis is named by content.** Hypothesis names are content-anchored slugs (`h_pre_sorted_a`, `h_inv_<slug>`, `h_path_<slug>`, `h_<callee>_post_<slug>`, `h_cinv_<slug>`; same-slug collisions get `_2` suffixes rather than shadowing) — discharge scripts survive unrelated edits. Obligation names are `fn.kind.<expression-slug>`, or `fn.kind.<label>` where the clause carries `#[label(name)]` (stable semantic names; hypotheses become `h_inv_<label>` etc.). Lean theorem names are sanitized versions; user-facing names live in the source map.
- **Class structures are emitted under mangled names** (`SableC_<name>`) so user class names can never collide with Lean root-namespace names (`class Nat` vs core `Nat`). Clauses never name the class — only values — so the verbatim-splice invariant is untouched; the prefix appears only in compiler-built binder types and `.mk` literals.
- **Binders carry source names.** A call/alloc/ctor result bound to a local binds under the local's name (`u64 p = probe_step(...)` → binder `p`, hypothesis `h_p_range`), not a positional `_r16`; a `&mut` method call rebinds the receiver's name (`m_2`); the mid-loop self state is `_self_loop`. Same motivation as content-anchored hypotheses: discharge scripts must survive unrelated edits.
- **Havoc is SSA-style versioning.** At a loop head, binders holding havocked names are renamed to stale versions (`_oldN_x`) and surviving hypotheses are *rewritten* to the stale names under `h_stale_*` — facts about pre-loop values (e.g. alloc facts) stay available instead of being dropped; fresh loop-invariant hypotheses keep the content-anchored names. Mid-method `self` havoc keeps *only* the loop invariants (the class invariant is not in force mid-method, design §7): a self-mutating loop states its full working payload — lengths, element facts, and a frame invariant against `old self` — as loop invariants. Record-field projections through update chains are reduced at generation time (`{ x with vals := v }.occ` → `x.occ`), so goals stay over stable atoms omega can use.
- **The machine has a raw heap, and every safe rule preserves it unchanged** (ADR 0025). `lean/Sable/SVM.lean`'s configuration carries a `RawHeap` — fresh-provenance counter plus allocations of `RawByte` where uninitialized is a distinct state — and `Val.ptr alloc off` is provenance plus an offset, never an address. Pointer arithmetic is an *expression* because it is pure; everything that touches the heap is an A-normalized *statement*, which is why `Eval` needed no change at all. Rule side conditions are decidable (`loadByte`, `freeable`, `inBounds`), since they are what the machine must compute to tell a store from `undef`. Invalid raw operations reach `undef`; exhausting the cap is `Trap.oom`. `lean/Sable/SVMRawTests.lean` pins the outcomes as `#guard`s — a second layer under the agreement proofs, because a rule and evaluator changed together consistently can be wrong and still agree.
- **A resource is authority, and only its *view* reaches Lean.** `resource RawSpan` / `resource &RawSpan` / `resource &mut RawSpan` are affine in the checker and erased from runtime signatures; vcgen binds a `Sable.SpanView` and nothing else, so no generated VC mentions a heap, a capability, or disjointness (ADR 0022/0024). The split is enforced by the two languages disagreeing: a clause may read `s.len`, program code may not (`resource.view_is_ghost`) — a program that could read the view would need it at runtime, and a runtime view is forgeable. `resource &mut R` reuses the `&mut` array machinery unchanged: entry state as the binder, current state in the env, `old s` resolving to the binder.
- **Values are exact integers.** Program integers are represented in Lean as `Int`; per-operation VCs guarantee representability, so symbolic values never wrap. `wrap()` etc. (later) get explicit `mod 2^n` semantics.
- **The prelude depends on Lean core only** — no mathlib. Cold-start and toolchain churn stay controlled; the multiset library (M2) is written in-repo.
- **The specification vocabulary lives in the prelude** (`lean/Sable/Specs.lean`): `sorted`, `sortedRange`, `perm`, `contains`, `count` — reducible abbrevs (discharge scripts apply their hypotheses directly), `@[simp]` where unfolding helps automation (`perm` stays opaque behind its lemma library), each with a native evaluator in the monitorable fragment. Program identifiers may shadow these names; the program binding wins in clauses.

## `sable test` (dynamic checking)

A separate, Lean-free path (design §9): `interp.rs` is a tree-walking
interpreter with trap semantics (overflow/bounds/division checked exactly
where the verifier emits VCs), and `speceval.rs` evaluates the
*monitorable fragment* of the proof language (arithmetic, logic — with
`↔` at Lean's exact precedence, pinned by a witness clause in the test
corpus — sequence access, `old` — including `(old obj).field` chains,
guard-bounded ∀/∃, ghost-def expansion — recursive defs included,
depth-capped, in exact i128 arithmetic (an overflow reports the clause
as unmonitorable rather than guessing) — with `if … then … else`, option
match and the `.is_some`/`.value` accessors, `perm` as multiset
equality). Pres/posts/invariants/variants are
checked dynamically; anything outside the fragment is reported as
skipped, never guessed — this is best-effort dev tooling, not a second
checker of record. `test_*` functions are its entry points and are never
verified. Escape hatches: `defer` skips an obligation's theorem but keeps
its downstream assumption (trap semantics); `assume` does the same as an
audited axiom; both are tallied in the build report.

## The SVM differential oracle

The machine semantics (`lean/Sable/SVM.lean`, design §10) is executable:
`lean/Sable/SVMEval.lean` defines a functional evaluator/stepper proven to
agree with the inductive rules in both directions — determinism, totality,
and progress are kernel-checked corollaries. The harness
(`compiler/tests/svm_diff.rs`, ADR 0017) lowers every function in
`corpus/svm-diff/` to Lean terms (`compiler/src/svm.rs`), runs each on both
`interp.rs` and the Lean evaluator, and compares canonical outcomes exactly
— a divergence is a bug in one of two artifacts that are otherwise trusted
independently. Lowering is strict: a subject outside the machine's core
subset is a hard failure, never a skip.

## Repo layout

```
docs/design/       normative language design + roadmap
docs/PLAN.md       milestones and exit criteria (kept current)
docs/decisions/    ADRs — one settled decision each, with the why
compiler/          Rust package `sable` (single crate until it hurts; split when it does)
lean/              Lake package: Sable prelude; pinned via lean-toolchain
corpus/verifies/   programs that must verify (status: fully verified)
corpus/must-fail/  programs annotated with the exact diagnostic that must fire
corpus/tests/      dynamic-test programs (import subjects from corpus/verifies via
                   `sable test -M corpus/verifies …`): must pass, zero skipped clauses
                   (known-unmonitorable subject clauses fenced by `// expect-skip:`;
                   a fence matching no skip is itself a failure)
corpus/test-fails/ dynamic tests that must be caught, annotated with the message
corpus/svm-diff/   differential subjects: every function runs on interp.rs and on
                   the Lean SVM evaluator; outcomes must agree exactly (traps are
                   expected outcomes here, so this dir is never verified)
docs/notes/        probe files and audit notes (SVM draft findings, class encoding)
editors/           Neovim setup + VS Code extension
.sable-out/        generated Lean + daemon socket (gitignored)
```

## Toolchain pins

Lean is pinned by `lean/lean-toolchain` (elan resolves it). Upgrades are deliberate, tested against the corpus, and get a commit of their own. Rust: whatever stable cargo is current; no nightly features.
