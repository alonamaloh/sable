# Implementation plan

Original north star for v0.1 — **verify `binary_search` and insertion sort end-to-end, with no hand-waving** — was reached 2026-08-08/09; the corpus now also carries fully-specified quicksort, the merge kernel, and round-trip codecs. Current north star: **Tier 2 of the roadmap** (goals doc) — Tier 1 is complete (`Vec`/generics M7, traits/hash map M8) and the UTF-8 codec opened Tier 2 (M9); next: buffer-level UTF-8 validation, then the JSON tokenizer (which wants the hash map), with the remaining M6 odds and ends as filler.

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

### M6 — the rest of Tier 0 *(benchmarks complete, 2026-08-09; ultracode session)*

**Enablers**: verified array-passing (`f(&src, &mut dst)`; callee pres on the argument's symbolic state, &mut args return as fresh states carrying length preservation + element ranges + the callee's posts) and content-anchored hypothesis names (design §6 — discharge scripts now survive unrelated edits).

**Benchmarks** (agent-authored under ultracode orchestration, all `status: fully verified`, all with dynamic tests at zero skipped clauses):
- **quicksort** — 74 obligations: in-place recursive quicksort over index ranges with contracted `partition`; full `sorted ∧ perm (old a)` top-level spec with frame posts ("unchanged outside [lo,hi)") and bound-preservation posts composing across the recursion; 15 discharges.
- **merge_sorted** — 74 obligations: the merge kernel with `sorted out` AND the count-based multiset post `∀ v, count out v = count xs v + count ys v`; 15 discharges + an in-file counting lemma.
- **hex_codec** — 44 obligations: pointwise encode/decode posts via *branchless arithmetic ghost maps* (`48 + d + 39*(d/10)` — simultaneously inside omega's and the dynamic checker's fragments), plus kernel-checked in-file round-trip theorems; 2 discharges.
- **varint** — 64 obligations: LEB128 encode with the full byte-count bound (`result ≤ 10`, proven via a 10-way unrolled division chain — no `pow` needed), decode fully automatic.

**Milestone souvenir (the big one)**: the quicksort agent caught a *genuine soundness bug* — the &mut-argument havoc block had been silently lost in a failed patch application, so callee posts were asserted over pre-call states and some VCs were provable from `False`. Fixed the same session; regression guard `must-fail/stale_state_after_call`; all benchmarks re-verified under the corrected encoding. Lesson recorded: a failed multi-part patch application must be re-verified part by part, and adversarial-review agents earn their keep.

**Parallel tracks landed the same session**: the SVM step-relation draft (`lean/Sable/SVM.lean`, 73 rules, builds clean; `docs/notes/svm-draft.md` lists 11 design ambiguities the formalization forced out — OOM vs determinism, ⊥-reads vs pillar 1, `wrap()` as operator-modifier, unstated evaluation order/short-circuiting, ghost state without transitions, and more) and the **warm-check daemon** (`sable daemon`: persistent Lean server behind a unix socket; 2.4s → ~0.25s per check, ~10×; silent fallback to the batch path).

Remaining M6 items: Base64 (nothing new technically after hex); `partial fn`; `narrow<T>` when something forces it; known warts — repeated `h_<arr>_len` facts across a call chain shadow (recover by type), `count`'s Lean form (`countUpto`+`toNat`) is clumsy in hand proofs.

### M7 — generics v1 and `Vec<T>` *(complete, 2026-08-09)*

**Generics** per ADR 0006: explicit instantiation only (`Vec<i32>::with_capacity(4)`, `id<u8>(x)`), parameters range over the eight integer types, and a monomorphization pass (`compiler/src/mono.rs`) expands every instantiation between parse and typecheck — no downstream stage (checker, VCgen, interpreter, spec evaluator) ever sees a type variable. Clause text substitutes parameters bare, so `T.max` becomes `i32.max` and the existing clause pipeline just works. Instances verify independently under mangled names (`Vec_i32`); the per-instance duplication of hand discharges is the accepted v1 cost. Diagnostics: `mono.missing_type_args`, `mono.arity`, `mono.not_generic`, plus recursion caps.

**`Vec<T>`** (`corpus/verifies/vec.sable`): growable vector with amortized-doubling `push` — capacity invariant `buf.len ≤ 2^62` makes the doubling overflow-free by construction; `push` carries the full frame post `∀ k < old self.len → self.buf.get k = (old self).buf.get k` across the reallocation-and-copy path. Two instances (`Vec<i32>`, `Vec<u8>`) verify at 151 obligations with 8 discharges (the copy-loop invariant and frame post, per growth path, per instance); dynamic tests exercise growth, set/pop, and both instances at zero skipped clauses.

**Soundness fixes forced along the way** (each with a must-fail regression guard):
- Owned local arrays mutated inside a loop were never havocked at the loop head — the pre-loop allocation's symbolic value survived the loop (`must-fail/owned_loop_stale`). Fresh binders now carry length preservation (only when the prior chain mentions no havocked name) plus element ranges.
- Loop well-formedness definitions inside class methods lacked `self`/`_old_self` binders, breaking any invariant mentioning fields.
- The runtime monitor's spec fragment gained `(old obj).field` projections and chained postfix (`(old self).buf.get k`), so `Vec`'s frame posts are *monitored*, not skipped — guarded by `test-fails/wrong_frame_dynamic`, which proves a violated frame post is caught rather than vacuously passed.

Deferred to the hash map (next): law-carrying trait bounds (`T: Hashable` with equations the proofs can use), non-integer type arguments, template-level discharges instantiated by mono.

### M8 — traits v1 and the verified hash map *(complete, 2026-08-09)*

**Traits** per ADR 0007: a trait pairs, per method, a *spec-level function* (`/// spec hash : int → int`, referenced as `Self::hash` / `K::hash`) with a program method contracted against it (`post result = Self::hash x`). That equation is the law that restores what opaque call-results can't give: hash **determinism across calls**, which the hash map's class invariant cannot live without. Impls provide the spec function as an ordinary ghost def plus bodies; mono consumes traits/impls entirely — impl bodies become plain contracted fns (a lying impl is a failed obligation, guarded by `must-fail/impl_lies`), bounds are checked at instantiation (`mono.unsatisfied_bound`), and `K::hash` resolves to the impl's fn in program text and its spec def in clause text. Probe-first again: `docs/notes/hashmap-probe.lean` validated the whole proof core before any compiler work (3 probes, 3 hits).

**`HashMap<K: Hashable, V>`** (`corpus/verifies/hashmap.sable`): open addressing with linear probing, fully verified at 110 obligations / 27 discharges. The class invariant is the linear-probing contract — every occupied slot reachable from its key's home bucket through occupied slots, plus no-duplicate-keys — which is exactly what makes stopping at the first empty slot sound (`hash_absent`, proven in-file from core Lean). Two techniques kept the proofs inside omega's fragment: cyclic arithmetic by *subtraction* (`probe`/`dist` ghost defs — no variable modulus anywhere; the only `%` is `hash k % cap`, an opaque atom with emod bounds) and the wraparound branch contained in a *contracted helper* (`probe_step`, post `result = probe h j cap`) so no path split leaks into the map's loops. `get`'s posts are the real spec: `some v` ⇒ the key is present with value `v`; `none` ⇒ the key is nowhere in the table. `insert` carries presence and frame posts. Dynamic tests monitor everything — probe-path invariant, ∃ posts, trait laws — at zero skips. v1 scope: no deletion (tombstones), and insert may report failure after a full sweep (ruling that out needs a counting/pigeonhole invariant — deferred).

**Also landed, forced by the map**: `narrow<T>(e)` (any-to-any integer conversion under a `narrow.range` VC — the long-anticipated primitive, forced by i32→u64 hash values); `if…then…else` and `(old obj).field`-chains in the runtime spec monitor; `old self` in loop-invariant position (the frame invariant a self-havocking loop needs); deduped `h_cinv_*`/`h_inv_*` hypothesis names (same-slug invariants no longer shadow); `::` accepted in discharge/defer/assume obligation names.

Traits v1 limits (ADR 0007): bounds over integer types only, one bound per parameter, no trait inheritance or default bodies, laws live in method contracts.

### M9 — Tier 2 opener: the UTF-8 codec *(complete, 2026-08-09)*

`corpus/verifies/utf8.sable`: RFC 3629 encoder and validating decoder, fully verified at 143 obligations with **one** hand discharge (the roundtrip) — a direct measure of the consolidated automation. The spec architecture: ghost byte maps `utf8_b0..b3`/`utf8_len` (if-chains over division by constants — omega's fragment once split) for the encoder; the decoder's success post says `v = utf8_decode(bytes)` against a junk-tolerant ghost byte-level decoder, plus a **completeness post** — canonical bytes at `pos` never decode to `none` — proven automatically at all twelve rejection returns. Validation is table-accurate: continuation ranges, overlong forms (C0/C1, E0 A0, F0 90), the surrogate gap (ED A0+), the 0x10FFFF ceiling (F4 90+). The program-level `roundtrip` (`post result = some cp`) follows from one ghost theorem (`utf8_decode_encode2`, junk-tolerant form matching the encoder's guarded posts). Dynamic tests at zero skips: boundary roundtrips (0x7F/0x80, 0x7FF/0x800, surrogate edges, 0xFFFF/0x10000, 0x10FFFF) and reject wrappers whose `result = none` posts the monitor checks per call. Probe-first: 5-for-5 (`docs/notes/utf8-probe.lean`).

**Buffer-level validation** (same day): `utf8_step` (position classifier: 0 = invalid, else the sequence length, with an ∃-canonicity post — automation can't invent the witness, so its four discharges name `utf8_decode` of the bytes and hand the rest to the unfold/split/omega workhorse) and `validate_utf8`, whose post `result → validFrom b 0` is stated against the first **well-founded recursive ghost predicate** (`validFrom`: decomposable into canonical scalar encodings; `termination_by (b.len - pos).toNat` splices verbatim). The scanner carries the classic forward-scan invariant `validFrom b pos → validFrom b 0`, closed by two in-file lemmas (`validFrom_step`/`validFrom_end`). 205 obligations, 7 discharges file-total. Also: the M8 CI failure (local-vs-CI divergence in positional binder numbering — hash-order-dependent fresh assignment in havoc) is fixed by sorted havoc iteration on top of the source-named binders.

Next Tier 2 candidates: JSON tokenizer (wants the hash map), DEFLATE (wants bit-level ghosts), UTF-8 decode-iteration (yielding codepoints — wants a way to consume `option` results in program code, still an open surface-design gap).

### M10 — the JSON tokenizer *(complete, 2026-08-09)*

`corpus/verifies/json_lex.sable`: the RFC 8259 lexical grammar, fully verified — 175 obligations across 9 functions, 11 discharges. The grammar lives in ghost predicates: `strTail` (string bodies — recursive with *varying* escape widths: 1 for plain chars, 2 for short escapes, 6 for `\uXXXX`), `digits`/`jint`/`jfrac`/`jexp`/`jnumber` (numbers, an ∃-split over phase boundaries), `jtoken` (the kind disjunction over punctuation/literals/strings/numbers), and `lexable` (whole-buffer tokenizability — the recursion target is *guarded*, `if pos < e then e else pos + 1`, so the ∃-bound token end needs no termination side condition: the split hands the decreasing proof its hypothesis).

Two patterns matured here. **Phase functions**: every multi-path lexeme phase is a small contracted helper (`digit_run`, `hexd_ok`, `jint_scan`, `jfrac_scan`, `jexp_scan`), so path splits stay contained and `json_number_end`'s ∃-witnesses are stable call-result binders — its post needed exactly one discharge. **Spec strengthening beats discharge cleverness**: adding one nonemptiness post to `digit_run` (`i < b.len → digitc (b.get i) → i < result`) let four scan posts that needed atom-congruence gymnastics close automatically instead. Probe-first: 6-for-6 (`docs/notes/json-probe.lean`).

Scanner-side, `json_string_end` carries the ∀-quantified forward-scan invariant (`∀ e2, strTail b i e2 → strTail b (pos+1) e2` — quantified because the closing position isn't known mid-scan), chained through `strTail_char`/`strTail_esc`/`strTail_hex` plus the inversion lemma `strTail_lt`. The capstone `json_lex_ok` post `result → lexable b 0` is kernel-checked; dynamic tests run real JSON (nested objects, escapes incl. `\u`, signed exponents) and nine reject classes at zero skips.

Next: the JSON *parser* (token stream → structural validation — wants the hash map for object keys, and will force the option-consumption surface design); DEFLATE (bit-level ghosts).

### M11 — option consumption (ADR 0008) *(complete, 2026-08-09)*

The gap the JSON parser forces, resolved C++-`std::optional`-style — **no pattern matching in the program language, as a standing design principle** (a `match` statement was considered and rejected): option-typed locals, `.is_some` (bool), and `.value` (payload, under an `option.some` obligation — junk-on-none in the model like `Seq.get` off-range, trap in `sable test`). The prelude (`lean/Sable/OptionAcc.lean`) defines the same accessors over `Option Int`, so **the identical postfix syntax elaborates in clause text**: new contracts read `post result.is_some → result.value = x + 1` — the spec and the code converge on one accessor style, with no `match` in either. `corpus/verifies/option_access.sable` verifies fully automatically (20 obligations, someness VCs discharging from branch facts, unreachable-else vacuity included); guards: `must-fail/option_value_unguarded` (unguarded `.value` is a verification error) and `test-fails/option_value_trap` (dynamic trap). Known wart: the runtime monitor parses `↔` at `=`-precedence, so accessor-iff clauses need a parenthesized right side (`result.is_some ↔ (0 ≤ x)`).

## Parallel track (low intensity)

The SVM step relation in Lean — **started**: `lean/Sable/SVM.lean` (73 rules, builds clean) with the design-audit findings in `docs/notes/svm-draft.md` (11 ambiguities, cross-referenced from design §10). Next steps there: determinism proof, a functional evaluator + agreement proof (the differential-testing oracle against `interp.rs`), then calls/frames. The audit findings should be resolved into the design doc.

## Testing strategy

`corpus/verifies/` must verify; `corpus/must-fail/` programs carry an `// expect-error:` annotation naming the obligation or diagnostic that must fire. The must-fail corpus is what keeps a trusted VCgen honest (stage-1 trust posture, design §10.1) and doubles as executable documentation of every diagnostic.
