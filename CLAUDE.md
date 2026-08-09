# Sable — agent instructions

Sable is a verified programming language: C-flavored program language, Lean 4 proof language on `///` lines. Read `docs/ARCHITECTURE.md` before touching the compiler; `docs/PLAN.md` says what milestone we're in and what's deliberately out of scope. The design docs in `docs/design/` are normative — if implementation forces a deviation, flag it and record it, don't silently drift.

## Build and test

```sh
cd compiler && cargo build            # build the compiler
cd compiler && cargo test             # unit tests + full corpus (runs Lean; slow-ish)
cd lean && lake build                 # build the Sable prelude (needed once; cached)
compiler/target/debug/sable check corpus/verifies/div_round_up.sable
compiler/target/debug/sable test corpus/tests/test_sorting.sable   # dynamic contract checks, no Lean
compiler/target/debug/sable daemon &   # optional: warm checker (~10x faster sable check)
```

Lean is pinned by `lean/lean-toolchain`; elan fetches it automatically. Never upgrade the pin casually — it gets its own commit, tested against the corpus.

## Invariants (violating these is a bug even if tests pass)

- Proof-language text is spliced into generated Lean **verbatim**; the Rust side never interprets it beyond block/clause structure. One proof-language semantics: Lean's.
- Every obligation has a name; every user-facing diagnostic carries: obligation name, goal, `.sable` span, context. Errors about clause text point at the `.sable` file, never at generated Lean.
- Program integer values are Lean `Int`s kept exact by per-operation VCs. No silent wrapping anywhere.
- The Lean prelude (`lean/Sable/`) depends on Lean core only — no mathlib.
- No external SMT solver. Automation is in-Lean (`sable_auto`); all proofs kernel-checked.

## Conventions

- Every new diagnostic gets a `corpus/must-fail/` program with an `// expect-error: <name>` first line; every new feature gets `corpus/verifies/` programs, and dynamic behavior gets `corpus/tests/` (must pass with zero skipped clauses) or `corpus/test-fails/` (`// expect-test-failure: <substr>`). The corpus is executable documentation.
- Commit early and often; push after each commit (repo is private). Substantive decisions get an ADR in `docs/decisions/`.
- Keep `docs/PLAN.md` status and `docs/ARCHITECTURE.md` current when the code moves under them.
- Dependencies: don't add Rust crates or Lean packages without a reason worth writing down (ADR 0003).
