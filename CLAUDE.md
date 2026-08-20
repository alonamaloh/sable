# Sable — agent instructions

Sable is a verified programming language: C-flavored program language, Lean 4 proof language on `///` lines. Read `docs/ARCHITECTURE.md` before touching the compiler; `docs/PLAN.md` records current priorities and what's deliberately out of scope. The language design in `docs/design/sable-language-design.md` is normative; `docs/design/sable-goals-and-roadmap.md` records the original research ambitions and is historical rather than a current plan. If implementation forces a design deviation, flag it and record it—don't silently drift. PLAN priority zero is an active release block: no work may claim axiom-clean `fully verified` status until user proof ingress and transitive axiom dependencies fail closed.

## Build and test

```sh
test ! -e .sable-out/daemon.sock && test ! -L .sable-out/daemon.sock
(cd compiler && CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 cargo build --locked -j1)
(cd compiler && CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 \
  LEAN_NUM_THREADS=0 LEAN_IMPORT_WORKERS=1 SABLE_TEST_JOBS=1 \
  cargo test --locked -j1 -- --test-threads=1)
(cd lean && LEAN_NUM_THREADS=0 LEAN_IMPORT_WORKERS=1 lake --quiet build Sable)
LEAN_NUM_THREADS=0 LEAN_IMPORT_WORKERS=1 compiler/target/debug/sable check corpus/verifies/div_round_up.sable
compiler/target/debug/sable test -M corpus/verifies corpus/tests/test_sorting.sable   # dynamic checks, no Lean; -M resolves `use` imports
LEAN_NUM_THREADS=0 LEAN_IMPORT_WORKERS=1 compiler/target/debug/sable daemon &   # optional: warm checker (~10x faster sable check)
```

Lean is pinned by `lean/lean-toolchain`; elan fetches it automatically. Never upgrade the pin casually — it gets its own commit, tested against the corpus.

## Invariants (violating these is a bug even if tests pass)

- Proof-language text is spliced into generated Lean **verbatim**; the Rust side never interprets it beyond block/clause structure. One proof-language semantics: Lean's.
- Every obligation has a name; every user-facing diagnostic carries: obligation name, goal, `.sable` span, context. Errors about clause text point at the `.sable` file, never at generated Lean.
- Program integer values are Lean `Int`s kept exact by per-operation VCs. No silent wrapping anywhere.
- The Lean prelude (`lean/Sable/`) depends on Lean core only — no mathlib.
- No external SMT solver. Automation is in-Lean (`sable_auto`); all proofs kernel-checked.

## Conventions

- Every new diagnostic gets a `corpus/must-fail/` program with an `// expect-error: <name>` first line; every new feature gets `corpus/verifies/` programs, and dynamic behavior gets `corpus/tests/` (must pass with zero skipped clauses; a deliberately-unmonitorable subject clause needs an `// expect-skip: <substr>` fence, and stale fences are failures) or `corpus/test-fails/` (`// expect-test-failure: <substr>`). Two spellings of one program get a `corpus/pairs/` pair (`<stem>.a.sable`/`<stem>.b.sable`, first line `// pair: same-lean` or `// pair: same-run`), compared Lean-free by `cargo test --test pairs`: diagnostic-name sets, α-normalized obligation sets, or interpreter outcomes must agree. The corpus is executable documentation.
- Machine-semantics changes extend the rules, the functional evaluator, and the agreement proofs together (`lean/Sable/SVM.lean` + `SVMEval.lean` — the build fails otherwise) and get `corpus/svm-diff/` subjects: zero-arg functions, traps are expected outcomes, compared against `interp.rs` by `cargo test` (ADR 0017).
- Commit early and often; push after each commit. Substantive decisions get an ADR in `docs/decisions/`.
- **No development-history references in code, corpus, or diagnostics.** Comments, diagnostic names, and user-facing messages describe the present design — never milestones ("M6"), slices, layers, tiers, or "found by X" stories; that history lives in git, while settled reasoning lives in ADRs. Citing an ADR or a design-doc section is fine (those are normative documents); citing when or in what order something landed is not.
- Keep `docs/PLAN.md` priorities and `docs/ARCHITECTURE.md` current when the code moves under them.
- Dependencies: don't add Rust crates or Lean packages without a reason worth writing down (ADR 0003).
