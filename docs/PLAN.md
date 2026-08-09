# Implementation plan

North star for v0.1: **verify `binary_search` and insertion sort end-to-end from a `.sable` file, with no hand-waving.** Everything not needed for that is out of scope until it is.

Standing decisions (see `decisions/`): compiler in Rust; Lean is the elaborator and checker of record for the proof language from day 1 (no interim SMT dialect); error-message quality and early LSP are priorities because LLMs write most Sable code; repo private until there is something to show.

## Milestones

### M0 — the pipeline exists *(complete, 2026-08-08)*

Scope: straight-line functions with `if`/`else`. Types `u8..u64`, `i8..i64`, `bool`. Contracts: `pre`/`post`. Calls to non-recursive, earlier-checked functions (pre obligations at call sites, post assumptions after). Definite-initialization checking. Per-operation VCs (overflow, div-by-zero, narrowing excluded — no narrowing yet).

Pipeline: parse (program language + `///` block attachment) → typecheck → VCgen (symbolic execution, path-splitting) → emit one Lean theorem per obligation → `lake env lean --json` → map diagnostics back to `.sable` spans → render.

Exit criteria — all met:
- `corpus/verifies/div_round_up.sable` verifies via the automation portfolio (~2.4s cold; 4 obligations, kernel-checked).
- A wrong contract produces an error that names the obligation, quotes the goal, and points at the right `.sable` line (see the outputs on `corpus/must-fail/`).
- `corpus/must-fail/` failures are asserted by obligation name in `cargo test` (full corpus ~4.6s).

Milestone souvenir: implementing per-operation VCs immediately found a real bug in the design doc's §3 `div_round_up` example (its pre admits `a + b = 2^32`); kept verbatim as `corpus/must-fail/overflow_design_doc.sable`. The design doc's example should be corrected when §3 is next revised.

Known M0 simplifications (each has a scheduled fix): signed division/modulo rejected (Lean `/` on `Int` must be pinned to C truncation semantics first — M1); one clause per `///` line; call-site contract instantiation by token substitution; obligation-name anchors are expression slugs, not the final content-anchoring scheme.

### M1 — loops, arrays, `option` *(complete, 2026-08-08)*

`while` with `invariant`/`variant` (havoc decomposition; every proven VC is assumed downstream, which is what lets e.g. gcd's descent close by `assumption`), borrowed `&[T]` with index VCs, `option<T>` returns, `widen`, self-recursion with measures, multi-line clauses, and `discharge NAME by <tactics>` splicing with orphan detection. Division is Euclidean (ADR 0004); signed `/` additionally requires `¬(MIN ∧ -1)`.

Exit met: `binary_search` (design §6, all-Int spec style) verifies — 19 obligations, 17 automatic, 2 hand discharges (the sortedness-instantiation preservation goals; automation got `post.none`, which the design doc had expected to need one).

Known M1 simplifications, scheduled fixes: discharge scripts reference generated hypothesis names (`h_inv7_2`) read from failure output — content-anchored hypothesis naming is the M2 refinement; obligation names are path-dependent for repeated clauses (`.2` suffixes); invariant/variant clauses must not bind variables shadowing program variable names (token substitution cannot see binders); bool locals mentioned in loop clauses are unsupported; array parameters cannot yet be passed to callees (M2, with `&mut [T]` and stores); `sable test`/`defer`/`assume` are M3.

### M2 — ghost definitions and the seq/multiset prelude

`ghost def`, free-floating proof blocks, `seq<T>` lifting of arrays, a multiset library in the Lean prelude (this is the known trap — expect iteration). Exit: insertion sort with the full `sorted ∧ multiset-equal` spec.

### M3 — escape hatches and dynamic checking

`defer` (trap compilation, incl. bounded-quantifier checking loops), `assume` with `#[audit]`, per-package build-report tallies, and the `sable test` tree-walking interpreter with dynamic contract checks.

### M4 — LSP

Diagnostics, hover-shows-contract, folding ranges for evidence blocks, semantic tokens for dimming. The parser is written with error recovery from day 1 to make this possible.

### M5 — classes/RAII and the rest of Tier 0

`class`, invariants, `init`/`deinit`, borrow checking beyond call-site borrows. Exit: `BoundedStack` from the design doc, then merge/quicksort and the codec benchmarks.

## Parallel track (low intensity)

The SVM step relation in Lean — started early not because anything depends on it, but because writing the ~40 rules is the cheapest way to find semantic holes in the design. The `sable test` interpreter (M3) is structured for later differential testing against it.

## Testing strategy

`corpus/verifies/` must verify; `corpus/must-fail/` programs carry an `// expect-error:` annotation naming the obligation or diagnostic that must fire. The must-fail corpus is what keeps a trusted VCgen honest (stage-1 trust posture, design §10.1) and doubles as executable documentation of every diagnostic.
