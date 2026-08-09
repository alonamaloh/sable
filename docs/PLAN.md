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

Also in M1: `for (T i : range(lo, hi))` sugar (Alvaro's proposal) — bounds invariant, variant, and increment synthesized in the parser; extra invariants attach as usual (design §4).

Known M1 simplifications, scheduled fixes: discharge scripts reference generated hypothesis names (`h_inv7_2`) read from failure output — content-anchored hypothesis naming is the M2 refinement; obligation names are path-dependent for repeated clauses (`.2` suffixes); invariant/variant clauses must not bind variables shadowing program variable names (token substitution cannot see binders); bool locals mentioned in loop clauses are unsupported; array parameters cannot yet be passed to callees (M2, with `&mut [T]` and stores); `sable test`/`defer`/`assume` are M3.

### M2 — ghost definitions and the seq/multiset prelude *(complete, 2026-08-09)*

Ghost `def`/`theorem` in free-floating blocks (emitted verbatim; non-recursive defs get `@[simp]` so contracts naming them unfold); `&mut [T]` with element stores (functional `Seq.set` chains; length and element-range preservation assumed at havoc, sound because stores are the only mutation); `old a` in posts and invariants (entry-state binders `_old_a`); procedures (no return type, implicit return proves posts); the prelude multiset library (`countUpto`, `perm`, `perm_swap` — core-only induction proofs).

Exit met: **in-place insertion sort verifies with the full `sorted ∧ perm (old a)` spec** — 27 obligations, 24 automatic, 3 hand discharges (swap preserves sorted-except-moving-element, swap is a permutation via `perm_trans ∘ perm_swap`, loop exit sorts the prefix). The known trap cost exactly what it should: a ~90-line prelude library plus three ~10-line discharges.

Hard-won empirical notes: ghost-type aliases must be *notation*, not `abbrev` (type-synonym residue silently defeats omega's atom recognition — the goal displays identically and automation dies); `subst` on `q = j` eliminates `j` and breaks later references (use `simp`/`rw` with the equation in discharge scripts); `simp_all`'s orientation of variable equations is unstable, so scripts should not depend on it.

Known M2 simplifications: `old x` only for `&mut` array params; array arguments in calls still rejected (passing borrows is M3, with scalar `&mut i32` refs); bool locals in loop clauses unsupported; `for` bounds may not mention the mutated array (workaround: `u64 n = a.len;` first); discharge scripts still cite generated hypothesis names.

### M3 — escape hatches and dynamic checking *(complete, 2026-08-09)*

**Escape hatches**: `/// defer NAME` (obligation becomes a runtime trap; sound — its goal was already assumed downstream, which is exactly trap semantics; rejected for quantified goals) and `/// assume #[audit(reason := "...")] NAME` (audited axiom; payload mandatory). Orphans, conflicts, and missing audits are errors. The build report tallies proved/deferred/assumed and prints `status: fully verified` only at zero escapes — the §9 assurance ladder.

**`sable test`**: tree-walking interpreter with trap semantics (overflow/bounds/division checked exactly where VCs would be; Euclidean division; fuel-bounded), plus a monitorable-fragment evaluator for the proof language (`speceval`): ℤ arithmetic, logic, `a.len`/`a.get`, `old a`, guard-bounded quantifiers (capped), non-recursive ghost-def expansion, `match result` on options, and `Seq.perm` as multiset equality. Pres, posts, loop invariants, and variant decrease/nonnegativity are all checked dynamically; unmonitorable clauses are reported as skipped, never guessed. **The entire current contract corpus is inside the fragment (zero skips)** — asserted by the harness so the fragment can't silently shrink. `test_*` functions (contract-free procedures) may build owned array literals and pass `&a`/`&mut a`; they are never verified (design §9: sanitizer category).

Deviations/simplifications recorded: escape hatches are name-based module-level clauses (not the design's statement-attached `kind(expr)` form); statement-level `assert` not yet; bounded-quantifier `defer` compilation deferred (the interpreter checks everything anyway); owned arrays/borrow args are test-only until verified array-passing (M4+); the spec evaluator is explicitly best-effort tooling, not a second checker of record (ADR 0002 note).

### M4 — LSP *(complete, 2026-08-09)*

`sable lsp` (stdio, `lsp-server`/`lsp-types`): diagnostics (fast front-end pass on every edit, full Lean verification on open/save) with Sable diagnostic codes and UTF-16-correct positions; hover on a function name shows its contract — signature + `pre`/`post`/`variant`, never the body ("no reader may be shown a function without its contract"); folding ranges for proof blocks; semantic tokens typing evidence lines as `comment` (dimmed in every theme) and interface lines as `property` ("a reader may ignore proofs"). Integration-tested with a real stdio handshake (`tests/lsp.rs`). Editor wiring in `editors/`: zero-plugin Neovim config and a minimal VS Code client extension.

Known simplifications: single-diagnostic parsing (no multi-error recovery yet); full verification blocks the server loop for its ~2s (fine single-user; async later); hover resolves by name only (no scope analysis).

### M5 — classes with invariants and RAII *(complete, 2026-08-09)*

Classes per design §7: fields (ints, owned arrays), the class invariant as an interface block (obligation at the exit of every `init` and `&mut self` method, assumption at every entry, not in force mid-method), named constructors, `&self`/`&mut self` methods, empty `deinit` with RAII drop order, `alloc_array<T>(n, v)` with OOM-trap semantics, `var` bindings, method calls, bool-valued functions (`result` is Prop in the logic).

Encoding (probe-validated in `docs/notes/class-encoding-probe.lean` before implementation): a Lean `structure` per class; methods bind the entry state as `_old_self` and track the current state as an update-chain (`{ s with f := v }`); inits track fields individually and exit through a record literal; callers get fresh post-state binders carrying the invariant plus the member's posts. Bare field names in invariant clauses substitute onto the state (`len ≤ buf.len` works as the design doc writes it).

Exit met: **`BoundedStack` (design §7, near-verbatim) verifies — 23/23 obligations automatic on the first run**, including the structure-equality post `¬result → self = old self` and `old self.len`. Dynamic side: the interpreter constructs objects, checks the invariant at init/method exits *and at RAII drop*, and the stack posts (including structure equality and option results) are fully monitorable — zero skips.

Known M5 simplifications: class values are locals only (no params/returns/moves/copies); one class per value chain (no class-typed fields); `deinit` bodies must be empty; init/method params are ints; methods cannot call sibling methods through `self`; field names must not collide with parameter names in clauses (token substitution).

### M6 — the rest of Tier 0

Merge/quicksort on the sorting infrastructure; the round-trip codec benchmarks (Base64/hex/varint); `partial fn`; whatever the codecs force (`narrow<T>`, byte types in earnest).

## Parallel track (low intensity)

The SVM step relation in Lean — started early not because anything depends on it, but because writing the ~40 rules is the cheapest way to find semantic holes in the design. The `sable test` interpreter (M3) is structured for later differential testing against it.

## Testing strategy

`corpus/verifies/` must verify; `corpus/must-fail/` programs carry an `// expect-error:` annotation naming the obligation or diagnostic that must fire. The must-fail corpus is what keeps a trusted VCgen honest (stage-1 trust posture, design §10.1) and doubles as executable documentation of every diagnostic.
