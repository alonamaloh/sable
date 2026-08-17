# Implementation plan

Original north star for v0.1 — **verify `binary_search` and insertion sort end-to-end, with no hand-waving** — was reached 2026-08-08/09; the corpus now also carries fully-specified quicksort, the merge kernel, and round-trip codecs. Current state: **Tier 1 complete** (`Vec`/generics M7, traits/hash map M8) and **the Tier 2 spine landed** — UTF-8 codec + buffer validation (M9), JSON tokenizer (M10), option accessors (M11, ADR 0008), and the JSON parser against the full recursive grammar (M12 layer 1, 270 obligations). The scaling work landed (concepts M13, class values M14, `#[label]`), and the **bignum arithmetic pillar is complete through division and gcd**: `Nat` cmp/add/sub, schoolbook multiplication, `div`/`rem`, and Euclid's `gcd` (proven against Lean's own `Int.gcd`) all verified against one-line `natVal` specs (M15–M16) — the first benchmark where the mathematics itself was the test, and it stayed pleasant. **The roadmap's boss fight is won (M24): `div` is Knuth's Algorithm D with the `qhat_bound` lemma discharged and load-bearing**, and `Integer` (M27) is the first type built on top of a verified class — signed arithmetic whose `/` and `%` are literally Lean's, which is what ADR 0004 bought. The SVM semantic-oracle track landed on the core subset: determinism, totality, and rule/evaluator agreement are kernel-checked theorems, and the differential harness (`interp.rs` vs the Lean evaluator) runs in `cargo test` (ADR 0017). Verification is separate per module (M23, ADR 0018): imports verify once into content-addressed artifacts instead of being re-proven per importer. Ownership is now keyed by places rather than by names (M28, ADR 0023), which brought local-to-local class moves and `&mut C` — and, on the way, three soundness bugs in the borrow and loop-havoc rules. On that engine, **resources are a real category in the compiler** (M29, ADR 0024): affine authority the checker tracks, a pure view the logic reads, and nothing at all at runtime. The raw-memory direction has passed its first go/no-go (M30, ADR 0026): a safe `copy_prefix` over raw pointers verifies from a three-line value-level contract, with no user-visible heap logic anywhere. Foreign contracts are audited rather than proved (M31, ADR 0027), and the build status says `verified relative to audited boundary` instead of pretending otherwise. Non-memory resources and an explicit `PosixWorld` follow (M32, ADR 0028): a foreign function that can reach outside has to say so in its signature. Destructors then run bodies and classes own authority (M33, ADR 0029), which invalidated two earlier arguments and closed the hole the second one left. Ownership transfer is then one operation used by every sink (M34, ADR 0030) — a move kills its source place and destroys what the destination held, wherever it is written — which is what made the remaining duplicate-authority and double-drop paths one fix instead of six.

The unsafe ladder is complete through M44, and **unsafe Sable v1 has reached a
defensible stopping point**. Typed POD records and an arena-backed intrusive
list sit on generic aggregate authority; the core SVM is triangulated against
the Rust interpreter; and the formal `uart-poll-v1` profile adds an affine UART
capability, checked device intrinsics, observable trace semantics, and a bounded
verified transmit driver. Broader U10 work—generic MMIO, production
provisioning, richer UART/ISA models, concurrency, DMA, and atomics—is
deliberately deferred rather than required before the usability roadmap.
On that boundary, M45's scalar LLVM v0 backend is also complete: lowering starts
from the exact Lean-authorized `VerifiedProgram`, preserves checked scalar
semantics under optimization, and has interpreter/native plus trap-ABI gates.
G1.1's verified/interpreted `option<bool>` slice is closed, G1.2/G1.3 carry its
ordinary-function intersection through the formal SVM and native LLVM, and
G1.4a closes ordinary Boolean argument transport plus verified, interpreted,
and natively lowered internal integer-field POD record calls. G1.4b closes
owned-local Boolean arrays through checking, verification, interpretation, and
dynamic monitoring. G1.5 is closed across the formal SVM and its owned-local
Rust differential bridge, and G1.6 closes the matching local LLVM storage and
cleanup slice. G1.7 admits borrowed Boolean-array parameters in the checker and
VC generation, G1.8 runs and monitors them (ADR 0068), G1.9 models one in
the formal SVM as a lending argument (ADR 0069), and G1.10 lowers one natively
as a lent descriptor (ADR 0070).
G2.0–G2.2 close affine-option representation, local semantics,
and atomic formal-machine take; G2.3 closes the exact local LLVM lowering. No
array, affine-option, or record ABI, and no generic-class widening, is claimed.
N0's exact local `[u32]` LLVM storage and internal borrowed-array call slice is
closed as the native `Nat` foundation. N1a closes the fixed-owner class slice
needed by the real imported `Nat::from_prefix` and `cmp`. N1b closes internal
destination-pointer returns and single-use named-owner moves for that exact
shape. N2 closes the real imported `add` closure, N3 closes the real imported
`sub` and schoolbook `mul` closures, and N4 closes the real imported `div`,
`rem`, and `gcd` closures through safe mutable-owner reassignment and existing
lexical loop cleanup. N5 closes the exact nested signed-`Integer` call closure
with owned-`Nat` take parameters, per-field construction, nested field borrows,
`&mut Integer`, the private `flip_sign` method, and recursive destruction;
broader class transport remains fenced.

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

The gap the JSON parser forces, resolved C++-`std::optional`-style — **no pattern matching in the program language, as a standing design principle** (a `match` statement was considered and rejected): option-typed locals, `.is_some` (bool), and `.value` (payload, under an `option.some` obligation — junk-on-none in the model like `Seq.get` off-range, trap in `sable test`). The prelude (`lean/Sable/OptionAcc.lean`) defines the same polymorphic accessors over `Option α` (originally exercised with `Option Int`), so **the identical postfix syntax elaborates in clause text**: new contracts read `post result.is_some → result.value = x + 1` — the spec and the code converge on one accessor style, with no `match` in either. `corpus/verifies/option_access.sable` verifies fully automatically (20 obligations, someness VCs discharging from branch facts, unreachable-else vacuity included); guards: `must-fail/option_value_unguarded` (unguarded `.value` is a verification error) and `test-fails/option_value_trap` (dynamic trap). (A wart found here — the monitor parsing `↔` at `=`-precedence — was fixed immediately after: the monitor now parses `↔` at Lean's exact precedence, loosest of all connectives, because the monitor evaluating a *differently-parenthesized* proposition than the one Lean verified would be a monitoring-soundness bug. `test_option_access.sable` carries a precedence-witness clause whose truth value differs under any tighter parse.)

### M12 — the JSON parser *(layer 1 complete, 2026-08-09)*

`corpus/verifies/json_parse.sable`: structural validation against the recursive RFC 8259 value grammar — **270 obligations across 10 functions**, the largest artifact yet; ~15 parser-side discharges plus the M10 lexer proofs carried verbatim. `json_valid` returning true is a kernel-checked proof the buffer is one JSON value in optional whitespace.

The grammar is **one mode-encoded well-founded ghost predicate** (`jgram`: value / object-interior / object-tail / array-interior / array-tail — ghost defs splice as single `def`s, so the mutual grammar is mode-dispatched), with every recursive call ite-guarded so the single span measure `(j - i).toNat` decreases on every edge; a top guard (`j ≤ i → False`) supplies `i < j` to every decreasing goal and doubles as the `jgram_lt` inversion lemma. The parser is one **self-recursive** `json_value_end` (mutual recursion doesn't exist in Sable) with `variant b.len - pos`; objects and arrays are interior loops carrying ∀-implication forward-scan invariants over the tail modes (`∀ e2, jgram b 4 cur e2 → jgram b 1 (p+1) e2`), chained through eleven step lemmas validated probe-first (9-for-9 now; `docs/notes/json-parse-probe.lean`). The lemma-application exercise caught a real grammar bug before any proof was attempted: object tails were missing the whitespace slot between `,` and the member name.

Layer 1 scope: acceptance soundness only (no completeness claim for rejections), and no duplicate-key detection — that is layer 2, where the verified hash map finally meets a client (per-object key sets via 64-bit span hashes, with the spec stated over hash equality).

### M13 — proof ergonomics: `#[label]` and concepts slice 1 *(2026-08-10)*

**`#[label(name)]`** (design §6's open refinement): a short stable name on a contract clause replaces the content slug in both the obligation name and the hypothesis name — `zero_all.inv_preserved.prefix_zeroed`, `h_inv_prefix_zeroed` — so discharges survive clause rewording, not just unrelated edits.

**Concepts (ADR 0009), slice 1**: Alvaro's design — C++ concepts done right, as *type preconditions*. A template type parameter verifies against an abstract `Sable.IntModel` (`min`/`max` — the entire semantic content of a Sable integer type, which is why this is tractable here and not in C++) satisfying `wf` plus declared `/// requires` clauses; clause text like `T.max ≥ 100` elaborates unchanged via field projection (verbatim splice preserved). **Generic functions without trait bounds are now verified once, at the template**; instantiations owe only the `requires` obligations (numeric facts, automatic), and literals at type `T` become fits-VCs discharged from `wf`/`requires` (`corpus/verifies/concepts.sable`, all-automatic; guards: an under-provisioned instantiation fails `roomy_id_u8.requires.u8_max_1000`, a requires-less literal fails the template's `lit` obligation). Monomorphization is unchanged for code — ADR 0006 stands.

**Slice 2 (same day): generic classes.** Class templates get their own Lean structure (type-identical across instances — everything is `Int`/`Seq Int`), members verify once against the model with the class invariant machinery unchanged, and instances skip member obligations. **Acceptance passed: `Vec<T>`'s discharges collapsed 8 → 4 (one template set), obligations 151 → 84.** Template restrictions (slices 1–2, diagnosed not silent): no `/`/`%` on `T` values, no `widen`/`narrow` touching `T`, no generic-to-generic calls, no other-class references inside class templates, no class-level `requires` yet.

**Slice 3 (same day): trait-bounded templates — concepts complete.** A bound `K: Hashable` contributes, at the template, an abstract spec-function binder (`K_hash : int → int`, typed by the trait's `spec` signature) — exactly the shape of the hand-written probe lemmas — and `K::m(...)` calls in template bodies become `TraitCall`s modeled against the trait's contracts (posts as hypotheses over `K_hash`, pres as obligations). Clause text rewrites `K::hash` → `K_hash` at template save; instances are untouched (mono still resolves them concretely, and ADR 0007's per-impl law verification is what licenses the instantiation). **Acceptance passed: `HashMap`'s 27 per-instance discharges are now one template set** (`HashMap::insert.…`), and `bucket64` verifies at the template too. Every generic declaration in the language is now verified once.

### M14 — first-class class values, slice A *(2026-08-10)*

ADR 0010, the bignum prerequisite: **shared class borrows** (`&Range r` — the class value binds with its field facts and invariant, i.e. the method-entry treatment re-aimed at parameters), **class returns** (`-> Range`; callers bind a fresh post-state with invariant and posts, the `CtorCall`-result treatment generalized), and **field reads on class-typed names** (`r.lo`, `a.limbs[i]`, `a.limbs.len` — `a.len` on a class receiver resolves to the *field* named `len` by checker rewrite). Specs needed zero new surface: a class value is its Lean structure, so contracts write `result.lo ≤ a.lo` directly. Two new obligation kinds keep the bookkeeping kernel-checked: `ret_inv` (returned value satisfies its invariant) and `borrow_inv` (each borrowed argument satisfies its invariant at the call) — both close by assumption, but they are obligations, not trust steps. `corpus/verifies/class_values.sable` (40 obligations, fully automatic — including disjunctive posts over result fields); guard: `&mut Box` parameters diagnose as deferred. Deferred to slice B, when forced: moves/copies, `&mut C` parameters, class-valued fields, methods on borrowed receivers, borrows of generic-class instances.

### M15 — the bignum pillar, first arithmetic: `Nat` cmp/add/sub *(2026-08-10)*

`corpus/verifies/bignum.sable`: **`Nat` over `[u32]` limbs, little-endian, with the normalization invariant (no leading zero limb) making equal values have equal representations** — the Tier 3 pillar's opening arithmetic, fully verified at **95 obligations across 6 functions, 31 discharges, zero escapes**. The whole specification is one abstraction function (`natVal`, by recursion over the limbs via `valIn a i n` + the weight function `pw`) and one line per operation: `cmp`'s three iff posts decide the `natVal` order (descending scan; first-difference and shorter-normalized-is-smaller closers), `add`/`sub` post `natVal result.limbs = natVal a.limbs ± natVal b.limbs` (base-2^32 carry/borrow chains, every program value exactly inside u64 — sub's borrow via `a[i] + 2^32 − y − borrow`). Loop invariants are weighted partial sums (`valIn out 0 i ± carry·pw i = …` with min-ites for mixed lengths); results normalize through a shared `trim_len` phase function and a `Nat::from_prefix` init copying a proven prefix. Probe-first: 11-for-11 now (`docs/notes/bignum-probe.lean` — including the schoolbook-mul step lemmas banked for the next slice; findings: `fun_induction` pre-unfolds the scrutinized call, `ac_rfl` carries the AC shuffles omega can't, omega natively knows literal-base `ediv`/`emod`).

**Surface and soundness work the pillar forced**: `&[T]` init parameters (the `from_prefix` shape; ctor call sites get the fn-call array-arg treatment); emitted class structures are name-mangled (`SableC_<name>` — `class Nat` collided with Lean core's `Nat`); borrowed-argument field facts dedupe instead of shadowing (`cmp(&Nat a, &Nat b)`); init loops version mutated fields at havoc with dotted-key clause substitution (the owned-loop-stale bug class, init edition — previously a loud elaboration failure, now correct); shared re-borrow of `&C` parameters (`add` passing its borrows on to `limb_or0`).

**Workflow note**: discharge iteration ran against the generated Lean directly — stub the portfolio with a cheap no-`grind` tier + `sorry` fallback to triage which obligations need scripts (31 of 95), develop the scripts in-place, transcribe to `discharge` blocks. Minutes per cycle instead of `grind`-on-failing-goals burn — and that burn is now bounded by construction: the grind tier runs under a heartbeat budget with an expensive-success warning that carries a minimized `discharge` suggestion (ADR 0011, landed the same day; the corpus is held warning-clean by the harness, and measured at budget 1 it currently closes every obligation before grind).

Dynamic side: `corpus/tests/test_bignum.sable` — cmp orderings, the full carry chain (`[2^64−1] + 1 = [0,0,1]`), add-zero, add/sub round-trip, sub-to-zero — zero skipped clauses; limb counts stay small because the monitor evaluates `pw`/`valIn` exactly in i128.

**Schoolbook `mul` landed the same day** — `post natVal result.limbs = natVal a.limbs * natVal b.limbs`, the first genuinely nonlinear verification: nested accumulator loops whose inner invariant carries `valIn out 0 n + carry·pw(i+j) = valIn a 0 i · valIn b 0 lb + a[i]·valIn b 0 j·pw i`, with the summation rearrangement (`a[i]·b[j]` entering at weight `pw i·pw j = pw(i+j)`) closed by the probe's `mul_inner_step`/`mul_outer_close` (`ac_rfl` + targeted `mul_comm`/`mul_assoc` rewrites — omega atomizes the products and the shapes align). The u64 product VCs (`x·y ≤ (2^32−1)^2`, variable×variable, outside omega) close through one `mul_bound` lemma. File totals: **133 obligations across 7 functions, 42 discharges, zero escapes**; `t = out[i+j] + a[i]·b[j] + carry` peaks at exactly `2^64 − 1` — the base-2^32 headroom claim, kernel-checked. Dynamic tests cover single-limb squares, cross-row carries (`(2^64−1)·2`, checked against `a+a` too), and both zero orientations, still at zero skips.

The pillar's remaining arithmetic (division, or comparison-driven algorithms like gcd) waits for the next forcing session.

### M16 — bignum division, by composition *(2026-08-10)*

`div`/`rem` complete the pillar's core arithmetic — and the proof rides almost entirely on the *contracts* of the earlier operations rather than new limb-level mathematics. The algorithm is double-and-subtract long division: `d = b·m` doubles (via the verified `add`) until it overshoots the remainder, then `q += m`, `r -= d`. The outer loop invariant **is** the specification (`natVal q·natVal b + natVal r = natVal a`, with the hoisted `cmp` result pinned by iff-invariants), every step is linear in the `natVal` atoms because the products live inside `add`/`sub`/`mul` posts, and one Euclidean-uniqueness lemma (`Int.ediv_emod_unique`) turns the exit facts into the one-line posts `natVal result.limbs = natVal a.limbs / natVal b.limbs` and `… % …`. `rem` is three composed calls (`a − (a/b)·b`) closed by `Int.emod_def`. The ghost variant `natVal r.limbs` — a recursive ghost function as a termination measure — is monitored dynamically like everything else. File totals now **220 obligations across 9 functions, 61 discharges, zero escapes**; the division slice's 19 discharges are value bridges (`valIn` of the zero/one arrays), the doubling/outer step identities, length-domination for call pres (`len_le_of_val_le` re-used from cmp), and the uniqueness closers.

**`gcd` landed on top, the stack's first client** — Euclid in fifteen lines riding entirely on `rem`/`cmp`/`add` contracts: the loop invariant carries `igcd (natVal x) (natVal y) = igcd (natVal a) (natVal b)` through the in-file Euclidean ghost `igcd` (which is *proven equal to Lean core's `Int.gcd`* on the naturals — the spec is honest by kernel-checked agreement, not by definition), the termination measure is the ghost value `natVal y.limbs` shrinking through `Int.emod_lt_of_pos`, and the twelve discharges are all value bridges and length domination — zero new limb mathematics. File totals: **255 obligations across 10 functions, 73 discharges, zero escapes**. The zero-skip harness also caught a real monitor gap here: well-founded ghost defs whose `decreasing_by` text falls outside the clause language (`:=` ascriptions) silently failed the monitor's def parse; the monitor now truncates ghost-def bodies at `termination_by`, which is all it ever needed.

**Surface forced**: class-local reassignment from call/ctor results (`q = add(&q, &m);` in a loop) — move-in semantics, the old value dropped with its RAII invariant check (dynamically enforced at the reassignment, and the loop-havoc treatment already carried the invariant soundly since reassignment sources are `ret_inv`-checked returns). Local-to-local moves stay deferred (`class.move_deferred`, guarded in must-fail). Also `cmp` gained a trivial `range` post (`result ∈ {−1,0,1}`) so hoisted-comparison invariants can case on it.

### M17 — proof ergonomics II: inline `assert`, provenance lines, condition calls *(2026-08-10)*

Driven by the authoring-experience review after the bignum pillar (LLM-reported friction, Alvaro-triaged):

- **Inline `/// assert P`** (design §9's deferred statement-level form, now landed): a named obligation at its program point (`fn.assert.<label>`), then a hypothesis (`h_assert_<label>`) for everything downstream — a stepping-stone lemma proven once (automation or `discharge`-by-name) instead of re-derived inside every later obligation. Asserts attach to statement positions, loop-annotation blocks, and block ends; they are monitored dynamically at their program point (zero-skip discipline applies), work with `defer`/`assume` by name, substitute through templates, and get clause well-formedness defs so elaboration errors map to their own line. `corpus/verifies/assert_facts.sable` shows the shape — including an assert feeding a u64 *overflow VC* (the nonlinear square bound stated once, discharged once, operation VC automatic); guards: `must-fail/assert_unprovable`, `test-fails/assert_violated`.
- **Context provenance**: every entry in a diagnostic's context stack (pres, invariants, paths, callee posts, class invariants, asserts) now carries its source line — `pre x ≤ 5   (line 5)` — so the origin of every hypothesis is traceable without hunting.
- **Calls in loop conditions already worked** — the friction report was wrong on this point: `while (cmp(&r, &b) >= 0)` verifies today, with the callee's posts binding to *both* path directions (the condition is evaluated once per head in the havocked context, exactly as designed in M1's havoc decomposition). What was missing was corpus proof: `corpus/verifies/cond_call.sable` now pins it (the body path needs the post for safety, the exit path for the function's own post), plus dynamic coverage. The bignum hoisted-`c` pattern is therefore optional style, not necessity — and the sweep landed the same day: `div`/`gcd` rewritten with direct condition calls (the `c`/`t` temps and their five iff/range invariants deleted) and seven labeled asserts carrying the shared facts (`zero_val`, `one_val`, `b_le_r`/`r_le_a` order bounds, `y_pos`/`t_lt`). Bignum: 255 → 243 obligations, 73 → 67 discharges, each shorter — several previously-hand-proved obligations (the `d = b·m` base case, gcd's invariant initialization, the variant decrease, `rem`'s pre) now close automatically off assert hypotheses. The rest of the corpus was scanned: the other hoisted-call sites are genuine value uses, and the remaining discharge-heavy files (hashmap, json_parse) predate `assert` but their scripts are instantiation-shaped rather than shared-fact-shaped — left as is.
- **Operator overloading** is sketched for discussion in `docs/notes/operator-overloading-sketch.md`: concrete-class operator sugar (cheap — the program `+` and the proof `+` never meet) vs. operators in templates (requires type parameters over classes; its own future ADR, gated on a forcing benchmark).

### M18 — operator bindings *(2026-08-10, ADR 0012)*

`operator + = add;` — a top-level *program-language* declaration (an earlier `///` draft was rejected: operator binding steers program elaboration and has no proof content) binding `+ - * / %` to `fn (&C, &C) -> C` functions and all six comparisons, through one `operator cmp` binding, to a `fn (&C, &C) -> i32` under the −1/0/1 convention (`a < b` ⇒ `cmp(&a,&b) < 0`). The rewrite happens entirely in the checker; downstream stages see the ordinary contracted call, so pres/posts flow unchanged and **the bignum rewrite to `q = q + m; r = r - d;` under `while (r >= b)` landed with zero discharge churn** — 243 obligations byte-identical. The enabling fact: the program `+` and the proof `+` never meet (contracts speak through `natVal`). Operands are named class values (nesting binds a `var` first); guards: `op.unbound`, `op.bad_signature`, `op.duplicate`. Template operators stay deferred to a type-parameters-over-classes ADR (see the sketch note).

### M19 — modules v1 *(2026-08-10, ADR 0013)*

`use bignum;` — file-based modules, Rust-flavored surface. A module is a file (name = stem), resolved against the importing file's directory then `-M` paths; imports are transitive, cycle-checked, deduplicated by canonical path. Linking is source-level: the loader concatenates module sources and parses each in combined coordinates, so the merged AST is one Program and every stage from mono to the monitor is module-oblivious — imported class indices seed the parser (`extern_classes`) and the flat merge reproduces them. Diagnostics stay per-file (`ModuleSet.locate`): an error in an imported module points at *its* file and line, and cross-module context entries carry `(file:line)` provenance. `use m::{a,b};` name-lists are validated (`module.unknown_name`); collisions across modules are errors (`module.name_collision`); guards for all four module diagnostics live in must-fail (helper modules under `must-fail/mods/`). Verification was whole-DAG in v1 (imports re-verified with the root); slice 2 (M23, ADR 0018) made it separate — imports verify once into content-addressed artifacts. The payoff landed immediately: all 17 dynamic-test files now `use` their subjects from `corpus/verifies` instead of carrying copies — the bignum test shrank from ~700 lines of copied subject to `use bignum;` plus its fourteen tests, and test_hashmap demonstrates a test-side `impl Hashable for u64` on an imported trait. Imports carry the subject's *full* contract, so the copies' quiet omissions of unmonitorable clauses (unbounded ∀/∃, deep grammar recursion) surfaced; the zero-skip harness grew a two-sided `// expect-skip: <substr>` fence — an unfenced skip fails, and a fence matching no skip also fails.

### M20 — byte-string literals *(2026-08-10, ADR 0014)*

`b"..."` is a `[u8]` literal of its UTF-8 bytes — lexer + a one-arm parser desugar to the ordinary array literal; no later stage knows literals exist. Escapes `\n \r \t \0 \\ \" \xNN`; non-ASCII source text contributes its UTF-8 bytes verbatim (deviation from Rust, deliberate: `b"Aé€😀"` vs `b"A\xc0\x80B"` is the exact contrast the UTF-8 tests state). Bare `"..."` is *reserved* for the future `String` class (`lex.string_reserved`), so no literal ever changes type when strings land. The JSON/UTF-8/hex test data went from 52-entry decimal arrays to readable text (`b"{\"key\": [1, 2.5e-3, true, null]}"`); guards for the three lex diagnostics; `test_byte_literals` pins every escape byte-for-byte.

### M21 — String v1 *(2026-08-10, ADR 0015)*

`var s = "héllo";` in verified code — `String` as a *library class* (`corpus/verifies/string.sable`): owned `[u8]` bytes under the class invariant `validScan bytes 0`, the utf8 module's new byte-table validity predicate (no existential → monitorable, and kernel-tied to the canonical `validFrom` by `validScan_sound`). The probe-first find: literal obligations close by plain simp through ten *conditional step lemmas* gated on byte ranges — concrete bytes unfold, abstract hypotheses don't match, and nothing loops (tagging the recursive def itself blows `maxRecDepth` under `ite` congruence — measured, rejected). That forced `#[unfold]`, the general opt-in that emits a ghost def or theorem `@[simp]`. Bare literals are parser sugar (hidden `[u8]` temp + `String::from_bytes(&temp)` — the one lang-item-by-name coupling), UTF-8-guaranteed by the lexer; array-literal locals now bind in verified functions as concrete `Seq` facts (previously test-only). `cmp` is byte-lexicographic with full iff posts (first-difference witness / byte equality / range) under `operator cmp`, so all six comparisons work on `String`. File totals: **271 obligations across 6 functions, 10 discharges** (copy-loop frame, `validScan_congr` at init exit, two lex witnesses, and six refutation scripts for the non-witness paths of the iff posts — the last six written because the grind-budget warning named them as expensive, exactly ADR 0011's loop); the utf8 module grew `validScan`/`validScan_sound`/`validScan_congr` (~180 lines of proof text) with obligations unchanged. Dynamic: the invariant monitors per init/drop at zero skips; `test-fails/string_invalid_bytes` pins the overlong-encoding trap. Deferred (recorded in the ADR): concat, slicing, codepoint iteration, literals outside `var` initializers.

### M22 — `const` + immutable-by-default locals *(2026-08-10, ADR 0016)*

`const u64 MAX_BYTES = 4611686018427387904;` — named compile-time constants, substituted into program AST and clause text (the mono bare-token machinery) before any later stage runs; downstream a constant is indistinguishable from its literal, so omega and the monitor see numerals and the verbatim-splice invariant is untouched. Constants export through modules; 2^62 now has a name in the utf8/JSON contracts. And the flip (Alvaro's proposal): **locals are immutable unless declared `mut`** — `mut u64 lo`, `var mut q`, `mut [u8] buf` — enforced at assignment, element stores, `&mut` borrows, and `&mut`-method receivers (four named diagnostics + `mut.not_a_declaration`, all guarded). Parameters are immutable with no marker (the sweep found zero parameter mutations); `&mut [T]` parameters and `self.f` keep their existing markers; `for` indices are loop-owned. The corpus sweep added 111 markers — marker density now equals mutation density, and every unmarked local is a proven-constant read.

### M23 — separate verification (modules slice 2) *(2026-08-10, ADR 0018)*

One content-addressed Lean artifact per module (`.sable-out/modules/<stem>_<hash>.{lean,olean,ok}`): an imported module's obligations verify once and importers consume them through Lean's own `import` — `sable check string.sable` dropped 27.6s → 2.0s (utf8's 205 obligations imported, not re-proven); cold full corpus 164s → 130s. Import lines name dependency artifacts by hash, so an artifact transitively pins generated dependencies. M44 later made reuse fail-closed: `.ok` is necessary but not sufficient; exact generated bytes, the immutable proof environment, and the exact canonical Sable source graph must also agree. Emission is name subtraction (a file declares only what no imported artifact declares; generic instances demanded by an importer land in the importer's file), which forced byte-stable generation — vcgen's scope binders are now name-sorted. Flat-namespace guards with must-fail programs: `module.foreign_escape`, ghost `module.name_collision`, `module.duplicate_decl`. Dep diagnostics still point at the dep's own file from any importer. Roots still verify their own obligations on every check, while their generated documents are immutable and content-addressed.

### M24 — Algorithm D: fast long division *(2026-08-10)*

The roadmap's boss fight ("when `qhat_bound` is discharged, the moonshot is essentially won"): bignum's `div` is now Knuth 4.3.1 schoolbook long division — normalize by a doubling-loop scale factor, one quotient digit per limb from a two-limb estimate against the divisor's top limb, corrections counted and proven ≤ 4. **`qhat_bound` is discharged and load-bearing**: `qhat_ge`/`qhat_le4` (stated in pure ℤ over top-limb decompositions, validated first in `docs/notes/algd-probe.lean`) prove the correction loop's exactness sandwich, and the post-loop `assert c ≤ 4` — the bound itself, on the correction counter — verifies from them. The design keeps every invariant at the `natVal` level: the digit loop drives the verified `add`/`sub`/`mul`/`cmp` through two new helpers (`shift_in`, `nat1`), so no carry/borrow reasoning reopens, and the quotient needs no denormalization (`q = (a·m)/(v·m)`). Recorded deviation: Knuth's exact normalization needs the scale factor's power-of-two-ness — outside omega's fragment — so the loop guard `t + m ≤ 2^31` quarter-normalizes (invariant `t + m ≤ 2^32`, trivially preserved) at the cost of q̂ ≤ q+4 instead of q+2: two extra constant-time corrections, zero extra proof difficulty. 346 obligations across the module, zero deferred/assumed; 43 discharge scripts developed against the emitted Lean at a reduced grind budget and transcribed back (minutes per cycle — and the M23 artifact cache kept every staging iteration from re-proving bignum's other 200+ obligations). Multi-limb dynamic tests reconstruct dividends through `q·b + r`; their add/sub/mul invariants exceed the monitor's i128 at these magnitudes and carry `expect-skip` fences.

### M25 — module visibility *(2026-08-10, ADR 0019)*

`pub fn` / `pub class` / `pub trait` / `pub const` — default private, Rust-shaped. The boundary in one line: **the program language sees its own module plus the `pub` items of modules it directly imports; the proof layer sees the whole DAG** (a pub contract must elaborate for importers, and contracts name ghost defs freely — so ghosts, theorems, and clause text stay one flat namespace by necessity, not just taste). `use m::{a,b}` is now restrictive (v1 treated the list as documentation), listed names must be exported, and transitive references are `module.not_imported` until the module `use`s the owner itself. Enforcement is a loader pass over the per-module parses before the flat merge erases ownership — a reference walk (calls, ctors, class-typed params/returns/fields, trait bounds, impl heads, operator bindings, const tokens) against a DAG-wide item index; impls and operator bindings export with their trait/class, `pub` anywhere else is `module.bad_pub`. The sweep added 47 `pub` markers by fixpoint iteration on the new diagnostics — export density is reference density, the `mut` sweep's discipline. Guards for all three diagnostics incl. the restrictive-list and transitive variants. Still flat-merge underneath: same-named private helpers in two modules still collide (documented in the ADR; mangling deferred until it hurts).

G0's nominal-type audit tightened the implementation boundary without changing
that surface: functions/classes/records now share one explicit runtime lookup,
while traits and constants each have their own namespace. Restrictive lists
recognize `pub const`, and actual references resolve in their own namespace.
Visibility walks recursive use-site generic types as well as an exhaustive match
over nominal checked types. Cross-module collision selection is reconstructed in
source order before owner lookup, so neither hash-map order nor visibility can
hide the first link error. Same-module duplicate traits and duplicate impl spec
or method members now point deterministically at the second declaration. The
linker is still flat; real per-module names and backend mangling remain step 5.

### M26 — class values as places *(2026-08-11, ADR 0020)*

ADR 0010's deferred slice B, the part two benchmarks forced at once: **class-valued fields** (`class Outer { Inner inner; }` — nested Lean structures, with the inner class's field facts *and invariant* pushed one level down), **by-value class parameters** (classes are affine, so passing one consumes the local — `class.use_after_move`), and **borrowing a field** (`&o.inner`, `&self.inner`: the borrowed place is the field, not the base). `&mut C` and local-to-local moves stay deferred; nothing forces them yet. The finding that made it cheap: **a move and a borrow are identical to the logic** — both bind the structure value with its facts and invariant, differing only in the affine discipline (checker) and runtime transfer, so vcgen gained one match arm rather than a verification concept, and `Val::Obj`/`push_class_state_facts`/`push_invariant_hyps` just recurse. Affinity itself is one new `VarInfo` field on the state machine that already tracked definite initialization — a typechecker diagnostic with a span, not a failed proof, which is the same architecture `docs/notes/unsafe-sketch.md` bets on for resources, now demonstrated a level up. The deep content is ownership maturing from *locals* to *places*: `Integer` wants a `Nat` inside a class, resource carving wants a byte range inside an allocation, same notion at different granularity. Known gap, recorded: direct nested reads (`self.inner.v`) are not surface syntax — borrow the field and use an accessor; clause text already nests freely. The `Integer` benchmark that forced the slice immediately found a latent modules bug: a module that both declares a class and imports one had inconsistent class indices, because the flat merge ordered by *load* order (root first) while every parse saw its dependencies' classes first — the root is loaded first but finishes last. Both now use finish order, which reproduces every module's view simultaneously; guarded by `corpus/verifies/class_import.sable`.

### M27 — `Integer`: signed arithmetic on `Nat` *(2026-08-11, ADR 0021)*

Sign plus magnitude over bignum's `Nat` — the first Sable type built *on* a verified class rather than on arrays, and the benchmark that forced M26. `class Integer { Nat mag; u64 neg; }` under three invariants, the third of which (`neg = 0 ∨ natVal mag.limbs ≥ 1`, banning negative zero) is load-bearing rather than tidy: because a negative operand has magnitude at least one, like-sign addition needs no zero check, and neither does the quotient's rounding correction. The whole specification is one ghost function, `intVal neg m = if neg = 1 then 0 - natVal m else natVal m`, and one clause per operation — `+ - * / %` and all six comparisons, bound through `operator`, which is keyed by (symbol, class) and so coexists with the `Nat` bindings the same program imports. The payoff of ADR 0004 lands here: **Euclidean `/` and `%` are Lean's own on `Int`, so `intVal result = intVal a / intVal b` is a contract about the operation itself, not a model of it**. Magnitude division gives `A = Q·B + R`; four ghost facts turn it into the signed pair, a negative divisor only flipping the quotient's sign and a negative dividend with non-zero remainder being the one case that rounds away. The other invariant, `0 ≤ natVal mag.limbs`, is discharged once at the constructor so every borrow gets nonnegativity for free instead of re-deriving it from limb bounds at each sign branch. **233 obligations across 27 functions, 17 discharges, zero deferred or assumed**; eleven dynamic tests pin the Euclidean convention on all four sign combinations at zero skipped clauses. Two language extensions were forced, both completing M26's story where it was still whole-local: **array-valued fields are borrowable places** (`&a.limbs` — `Nat` is affine, so `negate` holding only a borrow must duplicate the magnitude, and the cheapest copy re-runs the prefix constructor over the existing limbs; the checker returns `&[T]`, vcgen picks `Val::Arr` from the type it already recorded, the interpreter needed nothing because sharing the field's `Rc` was already what a field borrow did), and **affinity is per path** (`initialized` already joined correctly across an `if` — a returning branch contributes nothing — but `moved` was tracked monotonically beside it, so a move on a returning branch killed the local below; `int_mul` and `int_rem` both tripped it, and the two facts now join together). Recorded gaps: operator operands must be named locals, so the implementation calls `add(&a.mag, &b.mag)` rather than `a.mag + b.mag`; there is no unary minus on class values; `Integer` has no parsing, formatting, or machine-integer conversions.

### M28 — the place engine, local-to-local moves, and `&mut C` *(2026-08-11, ADR 0023)*

U2a of the unsafe ladder, built on the safe side first for exactly one reason: to be a test surface for the ownership machinery before erasure and view versioning complicate it. It returned **three soundness bugs**, all found by asking what a real `Place` (root plus field path, with `contains`/`overlaps`) would catch and all caught by the dynamic monitor on the false postcondition they let through. (1) A mutable borrow overlapping another borrow in one call: vcgen havocs the mutable argument and keeps the shared argument's pre-call symbol, so the callee's contract frames one storage location as two. (2) A borrow of a moved-out place, because `use_after_move` guarded only the name-read path — latent today (the interpreter shares `Rc`s) and live the moment a move actually transfers, which is what resources do. (3) A `&mut self` method call in a *declaration initializer* did not put its receiver in the loop's havoc set, and `Stmt::VarDecl` initializers were not scanned at all — so `while (...) { u64 t = c.bump(); ... }` kept the receiver's pre-loop state at the loop head and `post result = 0` verified on a function returning 3. Receiver marking is now precise rather than conservative (a `&self` method cannot write, and dropping its facts at every loop head would cost framing that verified code depends on), so `collect_assigned` takes a resolver. Two more holes came out of `&mut C` itself: class-borrow arguments on *methods* were accepted by the checker and reached an `unreachable!` in vcgen — an ICE reachable from ordinary `&C` source, now fixed by sharing the argument machinery across all three call forms — and construction assumed a borrowed argument's class invariant without owing `borrow_inv` for it, the one call form that skipped ADR 0010's obligation.

The features, all of which the place engine made cheap: **local-to-local class moves** (`a = b;`, `var d = a;`, including reviving a moved-from local by moving a new value back in — the reassignment arm no longer enumerates which expressions may move in, since a bare name is a move and everything else class-typed is a call or construction whose result nothing else names), and **general `&mut C`** on functions, methods, and inits. ADR 0023 fixes what `&mut C` means, and the whole design is one sentence: **the only way to mutate through it is to call one of the class's own `&mut self` methods**. That is what makes the caller's post-call invariant assumption sound — each such method carries an `inv_exit` obligation, so the invariant holds after every mutation the callee could have performed — and it is why `&mut a.f` is rejected rather than merely unimplemented: a callee handed unique access to one field has never heard of the base class whose invariant constrains that field against its siblings, so nobody re-establishes it. In the logic `&mut C` turned out to be `&mut [T]` with a structure instead of a sequence: one entry-state map now serves `&mut` arrays, `&mut C`, and the `self` of a `&mut self` method, because they are the same construct. `Integer::negate_in_place` is the first library operation that mutates instead of allocating, and its sign flip sits in a `&mut self` method whose precondition (`natVal self.mag.limbs ≥ 1`) is what keeps the no-negative-zero invariant true — the class states the condition under which its own mutation is legal, and the free function only checks it. Eight named diagnostics with spans, each with a `must-fail` guard. The one piece of the sketched lattice that did **not** need building: per-place `shared-borrowed(n) | mutably-borrowed` counters — a borrow is an argument, not a value, so borrow state never has to survive a statement.

### M29 — the resource category *(2026-08-11, ADR 0024)*

U2b's first slice, and the point where `docs/notes/unsafe-sketch.md`'s central bet becomes code: **authority is a checker property, and the logic reasons only about pure values.** `resource RawSpan` / `resource &RawSpan` / `resource &mut RawSpan` are a third value category — affine in the checker, a `Sable.SpanView` binder in Lean, and *nothing* at runtime. The load-bearing decision is that the view is ghost: a clause may say `s.len`, program code may not (`resource.view_is_ghost`). That one line is what makes erasure real rather than aspirational — a program able to read the view would need it at runtime, and a runtime view is a thing a program could construct, which is precisely the authority forgery the category exists to prevent. The strongest evidence for the bet is what `resource &mut R` cost in vcgen: **nothing**. It is the `&mut` array rule with a view instead of a sequence, so the `entry_states` map and `havoc_mut_borrow_args` that M28 generalized already covered it — the logic does not know resources are special, because in the logic they are not. Ownership is M28's engine with a type test bolted on: the same `Place` set, the same `check_borrow_conflicts`, no second ownership system, which was the exit criterion that mattered. Two rules *are* stricter than the class rules: a resource moved on one reaching branch and not the other is rejected (`resource.branch_shape`), and a loop body that consumes a resource live at the head is rejected (`resource.loop_shape`) — not for soundness, since dropping a resource is permitted and leaks are not unsoundness, but because with authority the difference between a deliberate release and a forgotten path is worth a diagnostic. The loop rule separates the two things a resource is: the *token* survives the backedge (a checker property, no VC), the *view* is havocked like any other mutated state, and the corpus subject shows both halves — `framed_loop` verifies only with its view invariant. `lean/Sable/Raw.lean` carries `ByteState` and `SpanView` with `take`/`drop`/`cat`; the views graduate from `unsafe-probe.lean` exactly as ADR 0022 said they would, while `Own`, `Cap`, and the preservation theorems stay in the probe until there are raw operations to justify. Eleven named diagnostics, each guarded. Deliberately still narrow: built-in `RawSpan` only, no allocation, no `load8`/`store8`, no resource fields, no user-defined resource types, and class members may not take resources at all — authority inside a class needs destruction semantics, an unbuilt prerequisite rather than a default to pick silently. Recorded rather than claimed: erasure is implemented on both sides by the same filter but is not demonstrated end-to-end, because nothing can create a `RawSpan` until the byte heap lands.

`split_off` and `join` complete the slice as compiler-known **sealed transformations** — not library functions and not prelude declarations, because each states a rule about who owns what and those rules are the compiler's. `split_off(&mut whole, n)` leaves the prefix in the borrowed token and returns the suffix, which answers the open question of whether the first resource slice needs a product type: **it does not**, one side goes back through the borrow. Bounds and adjacency are *failed VCs, never checker errors* — the checker tracks tokens, not geometry, and that division is the architecture in one rule. The subject that earns the slice is `carve_one_at_a_time`: one byte carved off the front per iteration and joined onto the processed prefix, two tokens live across the backedge with both views changing every turn — the shape the resource-soundness proof's carving step was established for, now a verified program at 23 obligations and zero discharge scripts. Writing it found two holes in the same hour: the loop-shape rule flagged a resource declared *and* consumed inside the body (per-iteration scratch the backedge does not owe), and `join` moving its arguments in a second pass accepted `join(a, a)` — which the adjacency VC does **not** catch, because an empty span is adjacent to itself, so a zero-length token would have been duplicated out of nothing.

### M30 — lexical byte exposure: the first safe wrapper over raw memory *(2026-08-11, ADR 0026)*

The unsafe ladder's first go/no-go checkpoint, and **the verdict is go**: `copy_prefix` copies bytes through raw pointers inside `unsafe` and verifies from a three-line value-level contract — no heap predicate, frame clause, separating conjunction, provenance lemma, disjointness proof, or discharge script. Four other subjects in `corpus/verifies/unsafe_copy.sable` do the same, including one that splits a span inside the exposure and rejoins it; 29 obligations, zero hand proofs. The checkpoint's other half — that the checker explains failures locally — is carried by eight negative subjects each landing on a named diagnostic at the right span. Two decisions do the work. **Exposure is a construct, not a proof**: `unsafe expose &a as (p, resource m) { ... }` lends the array's bytes for the body and takes them back, so the bridge between the safe world's `[u8]` and the raw world's bytes is syntax with generated obligations (the whole extent came back; every byte is present and in `u8` range) rather than something a user reasons about. And **affinity supplies separation**: `raw_copy_nonoverlapping` has *no nonoverlap premise at all*, because the two spans are distinct affine tokens and that is what being distinct means — the design test the plan set for whether a caller holding two exclusive resources must prove they do not alias. Nonescape is done by hidden **loan brands** with no lifetime syntax: branded values cannot be returned, assigned to a local outside the body, or passed to a user function that could launder them, and the brand follows *provenance* through `raw_offset`/`split_off`/`join` — but not onto loaded bytes, since a byte read out of memory is an ordinary number, which branding it broke until a corpus subject caught `return b`. A shared exposure cannot mutate *structurally* (its resource binding is not `mut`, so unique access never exists) rather than by frame condition, which is the better answer.

The three findings that decided the rung are all about the shape of what the **compiler** emits, not the user's proof burden. Automation needs the vocabulary *visible*: every spec-level notion in `lean/Sable/Raw.lean` carries an explicit unfolding lemma. `reconstructible` had to lose its existential, and a store's effect had to be functional (`m₂ = write m k (.init w)`) so composition lemmas fire without case analysis. One preservation lemma per operation keeps exposure exit automatic. `unsafe regions: N` records how many regions rest on proof rather than the type system. This rung also cleared U3's inherited differential criteria. Its then-current warm daemon could retain old prelude oleans after `lake build`; M44 closes that path by selecting an immutable proof environment per request and replacing the daemon server when its id changes.

### M31 — audited externs and the trust manifest *(2026-08-11, ADR 0027)*

Sable can now call code it cannot verify, and — the part that mattered — the build stops claiming it verified everything. `extern "C" #[audit(id := "...", reason := "...")] fn c_fill(raw<u8> p, u64 n, u8 value, resource &mut RawSpan mem);` declares an audited foreign contract: no body and therefore no obligations, but its clauses must elaborate and its audit metadata is mandatory. **Effects are structural, through resource parameters**: only a passed `resource &mut R` may change, while `resource &R` frames itself; there is no `modifies` clause to get wrong. Resources erase at the ABI, and extern returns/generics are restricted to prevent retained storage. The trust manifest is emitted into generated Lean, so `test.fill.v1` and `test.fill.v2` name different artifacts. M44 later made `.ok` only one reuse condition: exact generated bytes, exact Sable graph, and the immutable proof environment must also match. Build status reads `verified relative to audited boundary` when assumptions remain and reserves `fully verified` for modules that trust none.

Three findings. **M30's brand rule was too blunt** and this milestone found it: it forbade passing branded storage to any function, which blocked the extern call outright. The right rule follows from a property of the language — with no globals and no raw- or resource-typed fields, a callee that cannot *return* storage cannot retain it either, so only a signature returning raw or resource can launder a brand. **`extern.generic` had to move from the checker to the parser**, because monomorphization drops an uninstantiated template before the checker sees it and substitutes the parameters away on an instantiated one, leaving nothing to reject. And **M30's unfalsifiable exposure obligation is now falsifiable**: every operation in that surface preserved reconstructibility so `expose.<a>.bytes` always closed, and an extern whose post says the bytes become `uninit` fails it — trusting a boundary is different from trusting the compiler, and this is where the difference shows. Test shims are keyed on the audit id, not the name, and an unknown id traps rather than running the empty body: a contract that appears to hold because nothing happened is the one outcome a monitor must never produce.

### M32 — POSIX handles and the explicit world *(2026-08-11, ADR 0028)*

The second FFI benchmark, and the plan chose that order deliberately: a real `read` adds file state, external input, short reads, errors, and interruption, none of which the deterministic `c_fill` shim had to answer. Two non-memory resources arrive — `resource OpenFile` is the authority to use one descriptor, with its *position* in the view because that is where POSIX puts it (an open file description has its own offset), and `resource PosixWorld` is the outside. **Any foreign operation that touches global state must receive the world explicitly**, which is what replaces a `modifies` clause over the universe and means a caller can tell from a signature alone whether a function can reach outside at all. Authority for a descriptor is carved out of the world that has descriptors — `open_file(&mut w, fd)`, with "is it really open" as a *precondition* rather than a checker rule, the same division `split_off` set: the checker tracks tokens, the VCs track geometry, and the state of the outside world is geometry. `posix_world(script)` is the one place authority appears from nothing, so it is confined to `test_` functions; the script is what makes external behaviour something a test *author* controls, and the corpus checks that a failed read leaves both the buffer and the position exactly where they were. Handles are passed explicitly rather than owned by an RAII class, so `close` consumes the `OpenFile` and a double close or a read-after-close is a checker error at the second use — leaking a descriptor is what affine-not-linear authority permits.

Three findings, and one honest cost. **The exposure obligation caught the extern contract being under-specified**: a `read` post saying "these bytes came from the stream" says nothing about whether they are *bytes*, so the caller's `[u8]` could not be reconstructed from them — a world's stream is now a byte stream by well-formedness, stated for every index, since off-the-end junk is our modelling choice as much as the stream is and choosing it to be a byte removes a window premise from every read contract. **M30's "state effects functionally" lesson extends to foreign contracts**: the destination is one equation over `SpanView.fillFrom`, and because `n = 0` leaves every byte where it was, a short read and a failed read need no case analysis at all — written as three clauses (transferred prefix, untouched tail, nothing-changed-on-error) it needed two nested splits and did not close. And **a wrapper that hides the world must say what it preserved**: `read_twice` could not prove its second read's precondition until `read_into`'s post said the handle and descriptor count survived, which writing the second caller is what found. The cost: **this is the first rung whose safe wrapper needs a hand proof** — a three-line `discharge` on the exposure exit, not on the wrapper's own contract, where `copy_prefix` needed nothing. A foreign contract whose effect depends on an unpredictable outcome puts a case analysis in front of the reconstruction, and the tempting fix (a prelude lemma shaped to one signature) would be a prelude that knows about `posix_read`. Recorded rather than smoothed over, along with the fact that resource-*view* contracts are not monitorable at all — a view is ghost, so the verifier covers those and the monitor covers how many bytes arrived and which ones.

### M33 — destruction semantics and resource fields *(2026-08-11, ADR 0029)*

`deinit` bodies had to be empty, and several earlier milestones deferred to this one by name. The semantics were pinned *before* the restriction was lifted, which is the order the plan insisted on: the class invariant holds on **entry** and is not re-established, because the value ceases to exist and there is nothing left to hold it — so a destructor owes no `inv_exit` and has no `_old_self` twin, since there is no "after" to compare against. The body may move fields out, which is how a class that owns authority hands it on; the *field* is the place that dies rather than the object, so untouched siblings stay readable (that is `partially-moved`); a moved field is not dropped again, and the rest drop in reverse declaration order. The interpreter's order within a drop is **invariant → body → remaining fields**, because checking after the body would evaluate the invariant over a hole the body just made — unambiguous by accident while bodies were empty. Classes now hold resource fields, and `#[must_consume]` marks one whose authority must go somewhere: abandoning it is a diagnostic, as is putting the marker on a class with no destructor at all, while an *unmarked* affine resource field may be abandoned — that is a leak, and affine-not-linear authority permits leaks. The marker is what turns a permitted leak into a diagnosed one.

**The most useful output of this milestone is what it invalidated.** M28's mutable field borrow turns out to be *sound in a destructor*: `&mut a.f` was deferred because a callee could not re-establish `a`'s invariant, and in a `deinit` there is no invariant left to break — the reason evaporates exactly where the invariant does, and `&mut self.w` is how the destructor hands its world to `posix_close`. M31's brand argument **stopped being true**: it reasoned that only a raw or resource *return type* could launder a loan brand out of an exposure, because Sable had no storage-typed fields, and resource fields make a class exactly such a container — a function returning one can carry borrowed storage out, which `class_holds_storage` now decides transitively and a new must-fail guards. The lesson is not that the earlier argument was careless (it was correct when made) but that an argument from "the language has no X" expires when X arrives. And `havoc_mut_borrow_args` assumed a borrow names a whole place, so `&mut self.w` replaced `self` with a view and lost the self-chain; a field borrow now writes the fresh state back into the base. Two smaller consequences: a by-value class argument removes the value from its source place in the interpreter (harmless while destructors were empty, a real double drop once bodies run), and `is_partially_moved` was *deleted* rather than kept behind an `allow` — only `self` can be partially moved today and `self` is not usable as a whole, so it has no reachable caller.

### M34 — one ownership transfer *(2026-08-11, ADR 0030)*

Unscheduled, and taken before the typed-storage milestone because an external review of M33 was right about the part it named and the sweep it prompted found more. Ordinary calls removed a by-value class argument from its source place; every other transfer — an inferred local move, an assignment, a field assignment, a constructor or method argument, a return — evaluated by cloning and marked nothing. The divergence was not a missing case in one pass but a missing *notion* in both: what a move does was written six times and agreed nowhere. The interpreter now has one `take_place` and one `drop_place` behind one `eval_moved`, and the checker one `transfer` at the matching sinks, which kills the source place, asks the loan-brand question, and reports whether a `#[must_consume]` obligation travelled with the value. Overwriting a place runs a full drop (destructor and fields, not the invariant check alone); a returned local leaves with the caller instead of being destroyed behind it; an owned parameter dies with the callee's frame after its contract has been checked against it.

**What the sweep turned up is the argument for doing it before typed storage**, which adds sinks — `init`, `take`, `drop_in_place`, an arena owning a `PointsTo` beside a `SystemDealloc` — on top of this layer. `self.f = x` marked nothing, so a class could hold a resource the caller still named: duplicated authority through the one sink with no rule. An owned array moved into a field kept its old name alive, and both names reach the same elements while the logic treats them as separate values — a **verified** post was false at runtime, and the v1 comment calling this "not tracked" was documenting an unsoundness. `return self.f` handed a field's authority to a caller still holding the object, so asking twice yielded two tokens; a member may now move a field out only if it puts something back, because the invariant is stated over every field and an invariant over a hole is not a question with an answer — only a `deinit` may leave one, which is M33's rule and precisely its reason. The loop-shape rule was resource-only although its argument never mentioned authority. `#[must_consume]` meant "moved somewhere", which a temporary satisfied, so the obligation now travels with the token — which is what `SystemDealloc` will need. Adoption did not spend the world's claim on a descriptor, so affinity stopped reuse of one token but not minting a second beside it. And three ICEs reachable from ordinary source (a method assigning a resource parameter to a resource field, a call to a method returning a class or resource, a function returning `raw<u8>`) were all missing match arms rather than missing designs.

**A second review pass found four more of the same shape**, each the rule missing from one more spot: `unsafe { }` and exposure bodies were scopes in the *interpreter* while the checker keeps their locals in the enclosing function (so an accepted program panicked the monitor — the two sides cannot differ, and the checker's answer is the language's); an inferred `var q = raw_offset(p, 0)` dropped the loan brand a typed declaration computes; a discarded class-valued call result was a temporary nobody destroyed, which it now is, at the end of its statement; and a live `#[must_consume]` place could be assigned over, abandoning the authority the marker exists to protect — consume it first, which empties the place. The standing limitation is stated rather than implied: passing a marked token by value discharges the obligation, so the marker means *must leave this frame* rather than *must reach a consuming primitive*, and changing that needs the marker on a type. ADR 0027's nonescape argument is amended in the same pass: "a callee that cannot return storage cannot retain it" is compiler-checked for a verified callee and an **audited promise** for a foreign one, since nothing stops C stashing a pointer in a global.

**A third pass closed the joins, the ABI, and the template path.** Branch and loop joins snapshotted initialization and the move set while `VarInfo` had grown a brand and a must-consume obligation, so whichever branch the checker walked last decided the rest — traversal order deciding a rule. The joins are now over one `PlaceState` (initialized joins by AND over reaching paths, brand and obligation by OR), which also required the obligation to become a *state of the place* rather than a flag consulted against the move set: since the move set is a union over reaching branches, "consumed on one path" had been reading as consumed, and a destructor that closed a handle only inside an `if` was accepted. The extern return rule became a whitelist — an integer or nothing — because blacklisting raw and resource returns named the storage types and missed the container (a class may hold resource fields). An exposure body is now a scope while `unsafe { }` is not, which is the honest asymmetry: the block grants vocabulary and has no lifetime, and the exposure *is* one, so a local derived from the loan cannot outlive it. And generic class templates were checked without the marker list, without the field-hole rule, and with **no destructor checking at all** — a template `deinit` consuming one field twice passed; verifying a generic once at the template (ADR 0009) is only a saving if what it verifies is the same thing.

**A fourth pass closed the place/state boundary before typed storage.** `VarInfo` records a field under `self.f`, while two move-shape checks and exposure cleanup asked only for the place root `self`; a loop could therefore consume a field and restore it as live, and closing an exposure could erase an outer field move. `Place::state_key` is now the single mapping used at those boundaries. Exposure cleanup first rejects any disappearing local with a must-consume obligation, and a loop backedge must preserve brands and obligations as well as affine liveness before the zero-iteration snapshot is restored. Four negative subjects guard the two field-move cases, scoped obligation loss, and obligation migration across a loop.

**Stage gate:** the static bump arena may proceed without deallocation, but `SystemDealloc` may not be introduced while `#[must_consume]` means only “leave this frame.” Mandatory consumption must become a property that follows the resource type through parameters and is discharged only by a declared consuming operation before the free-list milestone adds deallocation authority. U7b therefore uses a program-lifetime static root; the stronger consumption rule is an entry criterion for U8, not work to hide inside the allocator.

**Exact-once needs two corpus halves, and that is the reusable lesson.** "No value is destroyed twice" is what the transfer paths needed, and a compiler that destroyed *nothing* would pass it: `corpus/tests/test_ownership.sable` uses a destructor that falsifies its own invariant so a second drop traps, and `corpus/test-fails/deinit_runs.sable` gives a destructor a failing call to show each path destroys at all. The second cannot live in `corpus/verifies` — a verifying file may not contain a deliberately failing call.

### M35 — abstract typed `u64` cells *(2026-08-12, ADR 0031)*

The first U7b slice is deliberately vertical rather than generic: `resource PointsTo<u64>` carries an abstract `CellState` through raw-span conversion, initialization, copy-read, take, drop, and conversion back. No byte representation was smuggled in. Entering the typed role consumes exactly one aligned eight-byte `RawSpan` and discards its former contents; leaving requires an empty cell and explicitly zero-fills the returned span as cleanup. That makes the operation usable inside lexical exposure while preserving the line between `RawStorable` and the later `BitwiseRepr` capability.

Every enforcement layer moved together. The checker spends owned authority at both conversions; vcgen emits local provenance/alignment/state obligations over `PointsToView Int`; the interpreter tags typed extents and excludes raw byte access; and the SVM gained matching instructions in both its relational and executable presentations, with agreement, determinism, totality, and progress still kernel-checked. Direct guards cover zero-fill, misalignment, byte/typed alias exclusion, invalid state transitions, and dead allocations; the Rust↔Lean harness now agrees on 46 subjects, including valid and invalid typed paths. The corpus adds a fully verified init/read/take round trip, a verified drop path, dynamic zero-fill checks, and named failures for wrong extent, wrong state, raw-authority reuse, and unsupported `PointsTo<T>`.

This is **not all of U7b**. At this checkpoint the next slice was the
compiler-established layout now recorded as M36; the remaining path is one
explicit record probe, then a non-deallocating program-lifetime static root and
bump arena. `SystemDealloc` remains gated on resource-type mandatory
consumption before U8; typed cells do not weaken that gate.

### M36 — compiler-established layout *(2026-08-12, ADR 0032)*

The fixed eight-byte fact from M35 is now one canonical `Layout`: positive size plus nonzero power-of-two alignment, attached to every integer type model and visible in contracts as `u64.layout` or generic `T.layout`. It is proof vocabulary, not a program value or resource, so user code cannot forge geometry. Explicit projection lemmas keep automation from depending on reducible unfolding—the first typed-cell rerun caught that boundary immediately when `(u64.layout).size` initially remained opaque.

`PointsToView` carries its layout and the `u64` well-formedness fact pins it to the canonical instance. Raw conversion creates that field, state transitions preserve it, and conversion back derives span length from it. The VC generator, interpreter, and SVM now consult their type-layout mapping instead of independently spelling `8`; the SVM has direct guards for the mapping, and the 46-subject differential suite still agrees. `corpus/verifies/layout.sable` exercises both concrete projection facts and template-level `T.layout` substitution (9/9 obligations).

U7b still has two distinct pieces: probe one explicitly laid-out POD record without representation semantics, then add the non-deallocating static root and bump arena. The `SystemDealloc` gate before U8 is unchanged.

### M37 — program-lifetime static roots *(2026-08-12, ADR 0033)*

`unsafe static_alloc(8) as (p, resource mem);` supplies the first root without slipping `SystemDealloc` past its stage gate. The statement is atomic because Sable has no tuple values and resource authority is erased: it binds a runtime pointer and exactly one checker-owned `RawSpan`. The size is a positive compile-time literal within the 50,000,000-byte profile cap, giving the verifier an infallible source under that profile; the SVM retains OOM when run with a smaller external cap. Each execution gets fresh provenance and the allocation is never released, so returned authority can outlive the function that acquired it and repeated calls leak distinct roots rather than duplicating one singleton capability.

The implementation is vertical but small: `SpanView.uninit` on the proof side, a live fresh allocation in the interpreter, and direct lowering to the SVM's already-proven `.rawAlloc`. The source example builds a `PointsTo<u64>` on the root and verifies 5/5 obligations; its dynamic test passes, two stable diagnostics reject a nonliteral or zero size, and the differential harness now agrees on 47 subjects. Next is the safe resource-only bump allocator over this root. The explicit POD record remains a green Lean probe, deferred at the source level because treating it as an ordinary class would prematurely require class values in the SVM.

### M38 — safe static bump arena *(2026-08-12, ADR 0034)*

`BumpArena` owns the unused suffix of one program-lifetime root under four
small invariants: bounded and aligned cursor, plus exact suffix offset and
length. Its public `alloc_u64` operation is entirely safe library code: move
the suffix out, use the sealed `split_off`, restore the remainder, and advance
by the canonical `u64.layout.size`. The mutating method's contract explicitly
frames capacity and allocation provenance, so repeated calls compose and each
returned `RawSpan` is provably the extent at the offset observed immediately
before it.

The verified subject keeps two allocations live simultaneously, derives their
pointers from the retained root pointer, converts both to abstract typed cells,
and proves the result is 42 (33/33 obligations, no proof script). Dynamic
execution covers the same path, and a must-fail subject pins exhaustion at the
third allocation. The arena itself contains no unsafe block: only root
acquisition, typed role conversion, and raw access remain unsafe. U7b's static
bump-arena exit criteria are met without deallocation. The source-level POD
record remains deliberately deferred behind runtime semantics; its explicit
layout/state-transition probe is green in Lean.

The next gate is U8a: make mandatory consumption a resource-type property that
propagates through owned calls and is discharged only at declared consuming
operations. `SystemDealloc`, leases, free, and coalescing remain blocked until
that rule is demonstrated against a do-nothing sink.

### M39 — resource-type mandatory consumption *(2026-08-12, ADR 0035)*

The U8 entry gate is now closed. `OpenFile` is the proving mandatory resource
type: owned parameters inherit its obligation, moves relocate it, function
returns re-establish it at the caller's receiving place, and every direct
return or unit fallthrough rejects authority that did not reach a terminal
operation. Fresh mandatory results cannot be discarded as expression
statements. A class field inherits the policy from its type and therefore
requires `deinit` without a field annotation; the RAII subjects now verify in
that form.

Terminal foreign consumption is explicit and audited:
`#[consumes] resource OpenFile fh` is legal only on an extern parameter. An
ordinary verified function cannot claim the attribute—its body must carry the
token onward—and an extern may neither omit it for a mandatory type nor attach
it to an affine one. Because this strengthens the foreign contract,
`posix.close.v1` became `posix.close.v2` rather than silently changing under the
same audit identity. The positive return/wrapper chain verifies at 3/3
obligations; seven focused negative subjects cover abandonment and declaration
boundaries, and the POSIX/ownership/RAII dynamic suites execute against the
versioned shim.

The field-level marker remains as a local ownership policy for otherwise
affine resources such as `RawSpan`; it is no longer the mechanism release
authority will rely on. U8b may now introduce `SystemDealloc` and the allocator
identity/lease model, but free and coalescing should still land only as part of
a vertical positive, negative, dynamic, and machine-semantics slice.

### M40 — releasable system roots *(2026-08-12, ADR 0036)*

`unsafe system_alloc(N) as (base, resource bytes, resource release);` is the
first releasable root: fresh provenance, one complete uninitialized `RawSpan`,
and a mandatory `SystemDealloc` whose view records allocation identity and
length. `unsafe system_dealloc(base, bytes, release);` is the only terminal
consumer. Its local VC requires the base pointer and the complete matching raw
extent, which forces carved blocks to be rejoined and typed cells to be emptied
and returned to raw authority before the machine executes `rawFree`.

System release is more tightly sealed than `OpenFile`: an audited extern may
not accept the token even with `#[consumes]`, because resources erase at the
ABI and C could merely promise away a release it did not perform in the Sable
machine. The checker, VC generator, interpreter, and SVM lowering all moved
together. The two positive paths verify at 9/9 obligations and execute
dynamically; eight focused failures cover the lifetime and identity boundary;
and the Rust/Lean differential suite now agrees on 48 source programs, while
the direct SVM suite already covers invalid, double, interior, and post-free
behavior.

Next is the allocator-specific layer: allocator identity, `BlockLease`, and an
in-band free-list invariant accounting for free plus live regions. Client free
must consume the matching lease, while only final allocator destruction owns
and consumes `SystemDealloc`.

### M41 — verified in-band free-list allocator *(2026-08-12, ADR 0037–0052)*

The U8 allocator experiment is complete. One affine `AllocatorState` owns the
free authority from a releasable system root, while client allocations are
mandatory, nonsplittable `BlockLease` resources carrying allocator identity,
exact key, and byte extent through raw and typed roles. Allocator-internal
`FreeBlock` and `FreeHeader` roles split, join, and materialize the real
two-`u64` in-band metadata without exposing a general lease-to-span escape.
Destruction is possible only after every role has rejoined into the complete
key-zero root extent and all stored headers are gone.

The policy is ordinary verified Sable over those sealed transitions: a finite
root-offset-ordered `StoredChain`, read-only terminating traversal, first-fit
selection, exact whole-or-split authority change, deterministic address search
for return, and local predecessor/successor coalescing. `free_list_return`
keeps the four adjacency cases explicit and proves each merge by clearing real
headers back to blocks and applying exact span joins. The root-length sentinel
is never dereferenced, including when a predecessor merge reaches the end of
the arena.

The public dispatcher verifies 94 obligations across its module closure with
zero `assume` and zero `defer`. Six dynamic fixtures cover every return branch;
wrong-owner, repeated-return, and subregion substitutions fail locally. A
fixed-seed reference-model harness exercises 144 returns, checking the runtime
head and every in-band header after every operation, and covers all four
adjacency cases. The complete corpus passes with one worker in 256.46 seconds.
This closes every U8 exit criterion and makes U9—the reusable `ResourceMap`
plus an arena-backed intrusive list—the next architecture test.

### M42 — generic resource-map authority *(2026-08-12, ADR 0053)*

U9's aggregate abstraction now exists in the compiler rather than only in its
metatheory probe. `ResourceMap<K, R>` has a pure partial-map view and one affine
token whose hidden interpretation owns the valid composition of all entries.
The first admitted instance is intentionally narrow—
`ResourceMap<u64, PointsTo<u64>>`—so parser, checker, VC generation, ordinary
call contracts, and dynamic monitoring are tested without pretending typed
records already exist. `resource_map_put` consumes a cell into an absent key;
`resource_map_take` removes a present entry and returns that exact cell. Neither
rule exposes separation logic or a global nonoverlap premise.

The positive subject routes both operations through public contracted wrappers:
two initialized cells enter the map, leave in reverse order, retain values and
pointer identity, become raw spans again, rejoin, and satisfy the original
system release token. All 22 obligations across three functions are automatic.
Five static failures pin absent take, duplicate put, repeated take, use after
put, and unsupported type arguments. The interpreter carries only a
sanitizer-side set of occupied keys—also across Sable calls—and independently
catches absent take and duplicate put; the SVM still erases every authority
operation.

The complete corpus passes with one worker in 261.79 seconds.

The generic proof in `docs/notes/resource-map-probe.lean` remains the authority
justification: take/put preserve hidden context validity and mutable entry
update derives from take–mutate–put. M43 applies that unchanged abstraction to
the typed-node client the probe was designed to force.

### M43 — typed records and the intrusive-list acceptance subject *(2026-08-12, ADRs 0054–0055)*

U9 is complete. POD records declare checked size, alignment, and field offsets;
the outer alignment must be a multiple of every field alignment, so the record's
base guarantee composes with those relative offsets. The static
`record.field_alignment` regression rejects under-aligned declarations.
their initial raw-storable fields are fixed integers, `raw<Record>`, and
`option<raw<Record>>`. Record values remain abstract rather than serialized.
Typed record cells implement the same explicit into/init/read/take/drop/from
lifecycle as `u64`, and `ResourceMap<u64, PointsTo<Record>>` reuses the generic
aggregate rules unchanged. The 19-obligation typed-record vertical slice,
layout/type must-fails, and dynamic repeated-init guard cover the prerequisite.

`corpus/verifies/intrusive_list.sable` then places two 24-byte nodes in one
system arena. Its visible invariant is a recursive relation between nullable
raw links, a partial map of exact node permissions, and an abstract sequence.
The function traverses both nodes, unlinks the head, rewrites the remaining
back-link, re-establishes the one-node invariant, tears both cells down, joins
the spans, and releases the precise 48-byte root. All 34 obligations verify
without `assume` or `defer`; the dynamic subject returns 50.

The final pre-U10 triangulation gate is also complete (ADR 0056). Abstract
record values, nullable raw pointers, construction/projection, and all six
record-cell transitions now exist in the relational SVM and its proved
functional evaluator. Per-byte record ownership excludes both byte access and
overlapping `u64` cells throughout the extent. The 47 direct machine guards and
59-subject Rust/Lean differential corpus cover successful record and pointer-
option outcomes plus the important `undef` state and tag failures. Agreement,
determinism, totality, and progress remain kernel-checked. That bare core is now
the compatibility base for M44/U10's first profile-specific wrapper.

### M44 — first formal UART machine profile *(complete, 2026-08-12, ADR 0057)*

The first U10 slice keeps device state out of both the raw heap and the audited
extern boundary. Source programs carry an affine `resource Uart`; ordinary
code cannot construct it, derive it from an integer, copy it, or pass it through
an extern. The ABI rule is now an explicit resource whitelist—`RawSpan`,
`OpenFile`, and `PosixWorld`—and `Uart` is deliberately absent. The signature
authority budget is one: a function, method, initializer, or template may
declare zero or one explicit UART parameter, never two. A second would give
VCgen two apparently independent views of the singleton UART0 used by both
executable semantics. Owned or borrowed `Uart` resource fields are rejected in
monomorphic and generic classes for the same reason; device identities and
functional field write-back are deferred. Tests alone may choose a deterministic
profile script with the compiler-sealed `test_uart` constructor.

Two device intrinsics live behind `unsafe` without becoming trust escapes.
`uart_status(&mut uart) -> u8` consumes the next oracle value, advances an
explicit cursor, appends an ordered status-read event, and establishes whether
the transmitter is ready. `uart_write(byte, &mut uart)` has a generated
readiness obligation, appends a transmit event, and clears readiness, so two
writes require two successful polls. The proof-facing `UartView` exposes a
transmit projection for contracts while the machine retains every read and
write in chronological order.

The formal machine extension is a wrapper in `lean/Sable/SVMUart.lean`, not
device fields threaded through every core rule. It delegates non-device steps
to the existing SVM and preserves the exact bare-core rendering when no profile
is selected; selected runs add profile identity, cursor, readiness, oracle, and
trace. The wrapper's relational and executable presentations agree in both
directions, with determinism and progress proved. Generated verification
content records `uart-poll-v1`, the intrinsics used, and a stable content hash
of the recursive local Lean import closure rooted at `MMIO.lean` and
`SVMUart.lean`, together with `lean-toolchain` and `lakefile.toml`. That is a
kernel-checked machine dependency, so it does not downgrade status to
“verified relative to audited boundary” as an extern assumption would.

The cache boundary was hardened with the profile. Each request captures an
immutable `proof-env-v2` byte map before profile generation or dependency work:
every local Lean source plus `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. Its source snapshot and single-job Lake build live under a
content-addressed id; batch Lean and the daemon consume the same exact snapshot
and generated text. Module artifacts additionally bind the canonical Sable
paths, source bytes, resolved import edges, and order. Generated root/module
documents are immutable and compared byte-for-byte on reuse; the FNV hashes are
only compact names, so a collision fails closed. The in-process cache retains
only identical builds currently in flight.

The first acceptance subject, `corpus/verifies/uart.sable`, is a bounded
poll/transmit driver: it either emits exactly the requested byte after observing
readiness or exhausts its budget without changing the transmit projection. It
assumes neither fairness nor eventual readiness, and 16/16 obligations verify.
Four dynamic tests (4/4) cover an immediately-ready script, readiness on the third
poll, a permanently-not-ready script, and `test_uart(0)` evaluated directly as
an erased resource argument. The single-job Lean package build is green. The
Rust/Lean differential gate agrees on 69/69 subjects, including profile traces,
cursor movement, readiness clearing, invalid writes, profile reselection before
replacement-script evaluation, and selection through assignment, discard, and
an inferred declaration.

The audit also closed general checker/VCgen/monitor soundness omissions. Loop
mutation discovery now exhaustively follows conditions, bodies, nested
`unsafe`/`expose` statements, and every ordinary, trait, raw, resource, and
device operand. Affine shape and the variant are snapshotted before the
condition; a false condition retains its post-condition state; and both VCgen
and the interpreter compare the pre-condition head measure with the post-body
measure on every taken iteration, including the last. Trait calls now use the
ordinary overlapping-borrow check, while UART-bearing trait signatures remain
rejected until abstract trait contracts can carry resource state.

Erasure likewise preserves effects: the interpreter evaluates resource-valued
arguments and transformation operands left-to-right before discarding their
proof-only value. SVM lowering preserves `test_uart` selection in declarations,
assignments, inferred declarations, and discarded expression statements;
authority-only resource operations erase only when their operands are
syntactically runtime-inert, otherwise lowering rejects the subject.

The sound havoc rule exposed free-list proofs that had relied on stale state.
`free_list_walk_unchanged` now carries a `state = old state` frame and restored
chain, while insert-location and first-fit transport their current facts through
the same invariant. Targeted checks are green for 33/33, 13/13, and 22/22
obligations across those three function pairs. The focused Rust library suite is
green at 9/9, and the complete single-worker serial corpus is green in 297.65s.
The full serial Rust suite is green: units, corpus, randomized allocator,
grind-budget, LSP, SVM differential, and doc tests.

M44 is complete and this is the **unsafe-Sable v1 stopping point**. Production
capability provisioning and native fixed-address lowering, a general
MMIO/device-description abstraction, UART receive/interrupt/error/timing models,
page tables, privileged instructions, any Sail/ISA connection, concurrency,
DMA, and atomics remain deliberately deferred and require their own decisions.

### M45 — scalar LLVM IR backend *(complete 2026-08-12, ADR 0058)*

The scalar v0 acceptance boundary is complete. `sable build --emit-llvm` lowers
only an opaque `VerifiedProgram` containing the exact checked and monomorphized
AST whose obligations succeeded
in Lean; code generation cannot reload, mutate, or independently reconstruct
the source program. The emitter is handwritten textual LLVM IR with no libLLVM
dependency. Entry selection is bound to the root span stored inside that
capability, rather than to a caller-supplied module view.

The landed subset covers scalar literals, locals, assignment, direct
nonrecursive calls, Boolean negation, unit procedures, returns, proof-assert
erasure, otherwise-scalar `unsafe` blocks, `if`, `while`, signedness-aware
comparisons, CFG short circuiting, explicit `widen`/`narrow`, and checked
integer arithmetic. Per-block reachability handles nested returns; loop
conditions remain in the header and are re-evaluated each trip; entry-hoisted
local slots retain declaration-site initializer stores. Entry mode emits only the
transitive call closure plus an `i32 @main` bridge; whole-module mode rejects
generic/class/record/trait declarations instead of silently omitting them.
Output embeds its artifact and immutable proof-environment identities, stdout
is pipe-clean, and `-o` publishes through a same-directory temporary file.

Signed and unsigned addition, subtraction, and multiplication use the matching
`llvm.*.with.overflow` intrinsic, and signed negation uses
`llvm.ssub.with.overflow`; their overflow bits branch to a defined trap.
Division and remainder guard zero before `udiv`/`urem`/`sdiv`/`srem`, and signed
division guards `MIN / -1`. Signed remainder treats `MIN % -1` as zero without
executing LLVM's invalid `srem` pair. When LLVM's truncating signed remainder is
negative, explicit unflagged add/subtract operations and SSA selections correct
both quotient and remainder to Sable's Euclidean convention. Widening selects `sext` or `zext`; narrowing
first represents the source value in `i128`, checks the destination's signed
range, and truncates only on the success edge. Every arithmetic/conversion
failure reports raw operand bits through the weak `__sable_rt_trap_v1` hook,
then the internal `noreturn` helper invokes `llvm.trap` even if the hook returns.
The emitter uses no `nsw`, `nuw`, `exact`, `inbounds`, or `llvm.assume` shortcut.

The complete low-concurrency gate is green under
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`.
That run includes 26/26 library tests, 6/6 verified LLVM CLI tests, and a 1/1
native differential test comparing the exact `VerifiedProgram` interpreter
outcome with Clang `-O0` and `-O2` for scalar, control-flow, and arithmetic
subjects. The arithmetic matrix covers positive and negative divisors,
`MIN % -1`, and successful conversion boundary values; the separate native trap
matrix covers failing conversions. The CFG matrix carries a loop condition whose
repeated native result would expose accidental hoisting.
The CLI gate also preserves an existing output on verification failure and
rejects audited assumptions before publication.

The trap ABI gate exercises all seven published kinds at both optimization
levels and pins the exact kind, type-info, and raw-operand payload. A returning
strong hook cannot suppress the mandatory following `llvm.trap`. The same
serial command kept the SVM Rust/Lean differential green at 69/69, completed
the full verifier/dynamic corpus in 220.78s, and passed the randomized allocator,
grind-budget, LSP, and documentation tests. This closes M45 without claiming a
proof of the emitter: the native differential and executable ABI gates test the
new compiler component while Lean continues to authorize the exact input AST.

The v0 acceptance boundary is intentionally narrow: fixed-width integers,
booleans, unit, scalar locals/parameters/returns, nonrecursive calls, ordinary
control flow, short circuiting, conversions, and checked arithmetic. Entry mode
checks the selected function's transitive closure, while whole-module mode
rejects any unsupported production declaration. Arrays, options, classes,
records, borrows, raw/resource/device operations, externs, deferred obligations,
and recursion receive source diagnostics rather than partial lowering.

Arithmetic retains Sable semantics under optimization: explicit overflow,
division, and narrowing guards; Euclidean signed division correction; no
`nsw`/`nuw`/`inbounds`/`llvm.assume` shortcuts. Internal names use
length-prefixed mangling without promising a public ABI, and file output is
atomic. Deterministic emitter tests require no LLVM installation; the required
closure gate additionally used Clang for exact interpreter/native outcomes and
the versioned trap ABI. Arrays, options, classes, records, and their ABI and
storage policies are deliberately not smuggled into this result: aggregate
backend support belongs to M46 and later.

## Post-U10 usability sequence

Unsafe Sable v1, the scalar LLVM v0 boundary, the first end-to-end Boolean
option slice, G1.4a's internal POD record-value slice, and G1.4b's owned-local
Boolean-array proof/runtime slice are complete. G1.5's closure of that exact
local slice in the formal SVM and differential lowerer is also complete. G1.6's
native storage and lexical cleanup for that same local slice are complete;
G1.7 opens `&[bool]`/`&mut [bool]` parameters through the checker and VC
generation, G1.8 runs and monitors them, G1.9 gives the formal SVM a
lending call argument so the two executables can be compared on one, and G1.10
lowers one natively by lending its descriptor.
The broader
aggregate-generics/backend track continues at M46+; G2.0's affine-option
representation/fail-closed checkpoint and G2.1's local semantic slice are
closed, as is G2.2's formal-SVM slice. G2.3's exact local native slice is
closed as well. N0–N5's native `Nat`/`Integer` ladder is closed. The order
remains a working hypothesis, not a promise that evidence cannot reorder it:

1. **M45 complete:** preserve the scalar LLVM boundary with exact
   interpreter/native differentials and end-to-end trap tests as later work
   extends it.
2. Generalize aggregate values and their lowering in forcing stages:

   - **G0 — recursive types (complete):** this is deliberately the compiler's
     representation/parser/identity/fail-closed foundation, not non-integer
     runtime semantics. Recursive `GenericTy`, opaque canonical keys, and
     whole-span `TypeArg` values now cover use-site integers, `bool`, in-scope
     parameters, visible records and classes (with recursively checked class
     arguments), `[T]`, and `option<T>`. Lookahead and AST construction share one
     parser with caps of 64 nodes per recursive path, 256 arguments per list, and
     4096 nodes per outer argument. Imported generic-class arities are retained
     separately from checked class indices. Duplicate type parameters and the
     256-parameter declaration ceiling still fail in the parser; every parsed
     non-integer argument still fails at `mono.type_arg_unsupported` before a
     checked type exists.

     Preparation, substitution, and generic-use traversal cover record literals,
     `some(...)`, class destructors, and member contracts and variants. Each
     structural `InstanceKey` includes function/class kind, template base, and
     the original recursive `CanonicalTypeKey` arguments, so exact requests
     deduplicate independently of emitted spelling. The registry rejects legacy
     spelling ambiguity and source/template/impl-lowered collisions
     deterministically. Namespace preflight keeps functions/classes/records in
     one runtime category while traits and constants remain separate; recursive
     nominal visibility is exhaustive, restrictive imports include public
     constants, and duplicate trait/impl members diagnose in source order. The
     complete low-concurrency command (`CARGO_BUILD_JOBS=1`,
     `CARGO_INCREMENTAL=0`, `SABLE_TEST_JOBS=1`, `SABLE_LEAN_JOBS=1`,
     `SABLE_REQUIRE_CLANG=1`, Cargo `-j1`, Rust `--test-threads=1`) is green:
     library 82/82; all 368 verifier/must-fail/dynamic/dynamic-failure corpus
     subjects in 424.42s; LLVM CLI 6/6; exact-`VerifiedProgram`
     interpreter↔Clang differential at `-O0` and `-O2`; SVM 69/69; allocator,
     grind-budget, and LSP gates green.
   - **G1 — Boolean/POD aggregates (through G1.6 complete):** establish
     non-integer aggregate storage, value, verification, interpreter, and LLVM
     paths one fenced representation at a time.

     **G1.0 — representation and proof provenance (complete):** declaration
     parameters now use `Ty::Param(TypeParamId)`, and aggregate payloads carried
     a narrowed `ValueTy` until ADR 0064 made them full `Ty` values gated per
     stage; since ADR 0066 each of those gates answers yes or a named error and
     nothing else, and a caller uses the payload it already holds. ADR 0067
     lifted binding mode out of the shape constructors: `&T`/`&mut T` are one
     `Ty::Borrow`, a bare type owns, and `Ty::is_affine` reads ownership off
     the shape. This was an
     internal separation of concerns, not a usable Boolean/POD feature: parser
     and checker acceptance was not widened, and concrete Boolean/record arrays
     and options remained fail-closed. Mono validates every declaration
     parameter id before direct-index substitution, rejects noncanonical legacy parameter
     forms, and exhaustively checks afterward that ordinary declarations contain
     no parameter. Retained ADR 0009 templates intentionally remain abstract.

     Proof reuse is now the explicit
     `ProofReuse::Adr0009IntModel` capability with an opaque payload. Its fields
     are private and its constructor is crate-private, so external AST callers
     can inspect but cannot forge it. Mono rejects a caller-supplied marker and
     authors it only for instances licensed by the existing concrete-integer
     domain; VCgen recognizes only that exact variant. The preparation and
     VC-generation entry points are crate-private as well. At that checkpoint,
     checker and VCgen rejected Boolean/POD aggregate semantics independently,
     the interpreter and SVM repeated the fail-closed guard, and module
     visibility followed nominal records carried inside aggregate payloads.
     Existing integer programs keep
     their previous semantics.

     The complete low-concurrency closure command was
     `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
     SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
     --test-threads=1 --nocapture`. It passed 101/101 library tests; all 368
     corpus subjects (79 verifies, 228 must-fail, 44 dynamic, 17 dynamic-fail)
     in 382.78s; LLVM CLI 6/6; the exact-`VerifiedProgram`
     interpreter↔Clang differential at `-O0` and `-O2` 1/1; and SVM 69/69.
     Randomized allocator, grind-budget, LSP, and documentation gates were
     green. G1.0 is closed.

     **G1.1 — verified/interpreted `option<bool>` (complete):** ordinary
     functions and inherent class methods may
     return `option<bool>`. Explicit and inferred locals support contextual
     `some(bool-expression)` and `none`, assignment, calls returning the type,
     `.is_some`, and `.value` where the path proves someness. VC generation uses
     Lean `Option Bool`; because Sable's symbolic program booleans are
     propositions, packing uses an explicit decidable Prop-to-`Bool` term and
     extraction produces `o.value = true`. The interpreter and dynamic monitor
     retain the payload type on present and absent values, preserving Lean's
     typed `default` (`0` for integer options, `false` for Boolean options)
     without weakening the executable trap on absent `.value`.

     This slice does not admit Boolean arrays or `alloc_array<bool>`, any
     option-typed parameter, option-valued class or record fields, trait or impl
     method option returns, record or nested option payloads, or Boolean generic
     type arguments. At the G1.1 checkpoint, the formal SVM and LLVM emitter
     independently rejected the new type.

     The complete low-concurrency closure command was
     `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
     SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
     --test-threads=1 --nocapture`. It passed 116/116 library tests; all 374
     corpus subjects (80 verifies, 231 must-fail, 45 dynamic, 18 dynamic-fail)
     in 409.31s; the focused `option_bool` verification at 21/21 obligations
     across six functions and its dynamic subject at 1/1; LLVM CLI 6/6; the
     exact `VerifiedProgram` interpreter↔Clang differential at `-O0` and `-O2`
     1/1; and SVM differential 69/69. Randomized allocator, grind-budget, LSP,
     and documentation gates were green. G1.1 is closed.

     **G1.2 — formal SVM Boolean options (complete):** the formal value plane now uses
     `Val.opt : Option Val`, replacing the old integer-specialized payload.
     `some`, `none`, `.is_some`, and `.value` are generic over machine values in
     both the inductive relation and the functional evaluator, and their
     two-directional agreement proof remains intact. A non-option operand is
     `undef`; extracting `none` is `Trap.optionNone`. Rendering preserves
     `opt none` and the historical integer spelling `opt some 7`, while adding
     `opt some false` and `opt some true`. Direct guards pin present false,
     present true, absence, extraction, both failure classes, and integer wire
     compatibility.

     The formal core's recursive representation deliberately exceeds source
     authorization. Rust lowering accepts only G1.1's ordinary-function
     intersection: concrete integer/Boolean option returns and explicit or
     inferred locals, contextual constructors, assignment and A-normal
     call-result transport, `.is_some`, and `.value`. Option parameters and
     fields, trait returns, record/nested payloads, Boolean arrays, residual or
     Boolean generic arguments, classes and method calls, and audited extern
     calls remain independently rejected. No option ABI was introduced.

     Its focused one-job Lake build covers `SVM`, `SVMEval`, `SVMOptionTests`,
     the raw/UART suites, and the `Sable` package, while the Rust↔Lean SVM
     differential agrees on 76/76 subjects.

     **G1.3 — LLVM Boolean options (complete):** the matching native value is
     the internal named type `%sable.option.bool = type { i8, i8 }`, tag then
     canonicalized payload. `none` is all zero; `some(false)` and `some(true)`
     use tag one and payload zero or one. Internal returns, direct calls, and
     explicit/inferred locals transport it through branches, assignment,
     loads/stores, and returns. `.is_some` tests the tag; `.value` branches to
     trap kind 8 with zero metadata and operand payloads before extracting on
     the success edge. `ob` is an internal/versionable mangling component, not
     an ABI promise.

     The emitter still rejects option parameters, option entry/extern ABI,
     option fields and trait methods, classes/method calls, residual generics,
     and every non-Boolean option payload. The combined G1.2/G1.3 closure
     command was `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
     SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
     --test-threads=1 --nocapture`. It passed 129/129 library tests; all 374
     corpus subjects (80 verifies, 231 must-fail, 45 dynamic, 18 dynamic-fail)
     in 414.80s; LLVM CLI 6/6, including exact zero metadata/payload for the
     kind-8 option-none trap and mandatory `llvm.trap`; the 1/1 exact
     `VerifiedProgram` interpreter↔Clang differential, now looping over four
     subjects (scalar, control flow, arithmetic, and Boolean option) at `-O0`
     and `-O2`, with 42 from the option subject; and SVM differential 76/76.
     Randomized allocator, grind-budget, LSP, and documentation gates were
     green. G1.2 and G1.3 are closed.

     **G1.4a — ordinary Boolean/POD calls and LLVM POD records (complete):**
     ordinary function calls now accept Boolean arguments. VC generation
     crosses the symbolic proposition/runtime-value boundary explicitly with a
     Prop-to-`Bool` reification based on the formal parameter type. Ordinary
     POD records may cross function parameters and returns in the
     verifier, interpreter, and dynamic monitor. Record returns regain the
     nominal declaration's `wf` fact, and loop havoc keeps that fact for the
     fresh record symbol. Class-method record returns and Boolean/record trait
     signatures remain closed rather than inheriting ordinary-call support.

     LLVM lowers a supported root-owned integer-field POD declaration as an
     internal named semantic aggregate. Construction, field projection,
     locals, branches, internal parameters, direct calls, and returns are in
     scope. This ordinary value deliberately ignores the declaration's raw
     `#[layout]` and field-offset metadata: those describe abstract raw-cell
     geometry, not an LLVM storage layout. Imported records, extern/entry/public
     ABIs, pointer and Boolean fields, nested and container records, and classes
     remain rejected. The internal name is versionable; this stage neither
     defines a record ABI nor makes generic classes real.

     The complete one-worker closure passed `cargo check`; 150/150 library
     tests; all 382 corpus subjects (82 verifies, 235 must-fail, 47 dynamic, 18
     dynamic-fail) in 218.30s; focused Boolean-call verification at 16/16
     obligations across ten functions and record-call verification at 13/13
     across four functions, with each dynamic subject at 1/1; LLVM CLI 6/6;
     and the 1/1 exact-`VerifiedProgram` interpreter↔Clang differential at
     `-O0` and `-O2`, now looping over five subjects including POD records. SVM
     differential remained green at 76/76. Its Rust lowerer also hardened
     semantic operand, source-scope, sealed-op, record-geometry, and
     integer-array coherence at the public AST boundary; that does not admit
     Boolean arrays. Randomized allocator,
     grind-budget, LSP, and documentation gates were green. G1.4a is closed.

     **G1.4b — owned-local Boolean arrays (complete):** fresh `[bool]` locals may
     be explicitly or inferentially typed and initialized by contextual literals or
     `alloc_array<bool>(u64, bool)`. This includes empty arrays. The supported
     surface is `.len`, checked index reads, element stores, loops, assertions,
     and contracts; array bounds keep their ordinary proof obligation and
     executable trap.

     VC generation gives this payload its actual proof type,
     `Sable.Seq Bool`. Because symbolic program Booleans remain propositions,
     literals, allocation fills, and stores use an explicit Prop-to-`Bool`
     reification, while an indexed read becomes `get ... = true`. Loop havoc
     keeps a Boolean sequence and its sound length relation without fabricating
     numeric element bounds. This is independent of ADR 0009's integer-only
     template proof reuse.

     The interpreter and monitor preserve an array's payload domain even when
     it is empty. Separate integer and Boolean runtime/snapshot variants support
     Boolean length, reads, stores, deep snapshots, and same-domain equality.
     Integer/Boolean-array equality is unmonitorable rather than coerced, and
     integer-only sequence helpers reject the Boolean domain.

     The slice stays local: Boolean-array parameters (ordinary, method, trait,
     and extern), Boolean-array returns, class/record fields, borrows, exposure,
     whole-array rebinding, Boolean `for` indices, and generic Boolean-array
     arguments remain rejected.
     At the G1.4b checkpoint the Rust SVM lowerer rejected Boolean arrays and
     the formal machine remained unchanged; the LLVM emitter independently
     rejected them, so no machine value or native storage/lifetime/ABI policy
     had yet been introduced.

     G1.4b closed under `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0
     SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
     --test-threads=1 --nocapture`: 171/171 library tests; all 394 corpus
     subjects (83 verifies, 244 must-fail, 48 dynamic, 19 dynamic-fail), whose
     all-target corpus portion took 208.73s; the focused `bool_arrays` subject
     at 18/18 obligations across four functions; both dynamic tests and the
     expected out-of-bounds failure; LLVM CLI 6/6; the 1/1 exact-
     `VerifiedProgram` interpreter↔Clang differential over five subjects at
     `-O0` and `-O2`; and the unchanged SVM differential at 76/76. A standalone
     corpus repeat was green in 195.71s. Randomized allocator, grind-budget,
     LSP, and documentation gates were green. G1.4b is closed.

     One boundary has a synthetic checker regression rather than a source
     corpus file: a discarded `alloc_array<bool>` expression statement. The
     parser cannot spell that form, but the public checked-AST boundary still
     rejects a forged instance rather than relying on the surface grammar.

     **G1.5 — formal SVM Boolean arrays (complete):** the machine value is
     `Val.arr (elem : ValTag) (a : Seq Val)` — a payload tag beside ordinary
     machine values (ADR 0062). The tag remains present at length zero. Length,
     checked index, allocation, and store are generalized over the admitted
     payload domains in both the relational semantics and functional evaluator;
     evaluator agreement, determinism, totality, and progress remain proved
     without deferred axioms. Rendering preserves `arr [...]` and spells scalar
     elements bare, lowercase for Booleans.

     Evaluation and trap precedence are explicit. Allocation evaluates length,
     then its scalar initializer, then negative-length/capacity geometry. Store
     evaluates index, then value and scalar shape, then resolves the array,
     checks payload compatibility, and finally checks bounds. A mismatched
     scalar store is therefore `undef` even when the index is OOB; a matching
     store to the same empty array produces `indexOOB`. Direct guards cover
     Boolean allocation/read/store/length, empty-tag retention, OOB, OOM,
     invalid initializers, and precedence.

     The Rust bridge preserves G1.4b's source fence. Only a fresh owned local
     initialized by `alloc_array<bool>` or a contextual Boolean literal may
     acquire the formal value; parameters, returns, fields, borrows, exposure,
     whole-array movement, and other transport are rejected. Literal lowering
     evaluates every element into a compiler-reserved temporary in source order
     before allocating a false-filled array and emitting ordered stores, so an
     element trap beats allocation/OOM. Expansion is limited to the SVM profile
     cap of 50,000,000 elements, and an empty literal still constructs a tagged
     Boolean array. LLVM storage, lifetime, and ABI lowering remained out of
     scope at the G1.5 checkpoint.

     G1.5 closed under `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0
     SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
     --test-threads=1 --nocapture`. `cargo check` and the full 22-target one-job
     Lake build were green; Rust library tests passed 175/175; all 394 corpus
     subjects (83 verifies, 244 must-fail, 48 tests, 19 test-fails) passed
     in 266.78s; LLVM CLI passed 6/6 with required Clang; the exact
     `VerifiedProgram`↔Clang O0/O2 differential passed 1/1 over five subjects;
     and the SVM differential passed 86/86.
     `free_list_return_random`, grind-budget, LSP, and doc-tests were
     green. G1.5 is closed.

     **G1.6 — native owned-local Boolean arrays (complete):** LLVM admits
     exactly the G1.4b/G1.5 local intersection.
     A fresh owned `[bool]` local may be initialized by
     `alloc_array<bool>(u64, bool)` or a contextual literal and then used for
     `.len`, checked reads, and element stores. The internal descriptor is
     `%sable.array.bool = type { ptr, i64 }`; elements are canonical zero/one
     `i8` bytes, not packed `i1` values. Parameters, returns, class/record
     fields, borrows, exposure, whole-array rebinding or movement, calls,
     extern/public ABI positions, generic/option containment, discarded array
     temporaries, and native integer arrays remain fail closed.

     Nonempty storage crosses only two external versioned hooks:
     `__sable_rt_array_alloc_v1(i64 bytes)` and
     `__sable_rt_array_free_v1(ptr)`. Zero length uses a null data pointer and
     bypasses both calls while its checked type still identifies `[bool]`.
     `runtime/hosted/sable_rt_v1.c` is an optional hosted implementation that
     rejects byte counts not representable by `size_t` and otherwise delegates
     to the C allocator; generated LLVM never directly imports `malloc` or
     `free`. The hook contract is a runtime boundary, not a Sable array ABI.

     Evaluation and failure order match the verifier, interpreter, and SVM.
     Allocation evaluates length, then initializer, then checks the
     50,000,000-element cap and hook result. A literal evaluates every element
     left-to-right before allocating and applying ordered stores. A store
     evaluates index and then value, performs an unsigned bounds check, and
     only then computes a non-`inbounds` address; a read also guards before its
     address/load. Cap exhaustion or hook null reports trap kind 9 with
     `(type_info, lhs, rhs) = (0, len, 0)`. Out-of-bounds read or store reports
     kind 10 with `(0, index, len)`. The returning observer cannot suppress the
     mandatory following `llvm.trap`.

     Owned locals now have an explicit native cleanup stack. The function
     body, each `if` arm, and each `while` body execution are scopes; normal
     exit frees in reverse declaration order, loop-body cleanup precedes the
     backedge, and a return evaluates its expression before unwinding active
     scopes inner-to-outer. `unsafe { ... }` is still an open marker whose
     declarations live in the enclosing scope. Trap edges do not run cleanup.
     The interpreter mirrors those lexical deaths by removing owned-array
     places at block and frame exit.

     The same audit fixed an older integer-array transfer hole. Array-field
     assignment is a special consuming boundary because ordinary whole-array
     reads are forbidden; it now explicitly rejects a local already marked
     moved. Interpreter moves take the named owned-array source, and owned-array
     local/parameter drops clear their places. The regression moves one array
     into two fields and requires `array.use_after_move`, raising the corpus
     inventory to 395 subjects (83 verifies, 245 must-fail, 48 tests, 19
     test-fails).

     G1.6 closed under `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0
     SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1
     -- --test-threads=1 --nocapture`. `cargo check` and the standalone
     22-target one-job Lake build were green; Rust library tests passed 185/185
     and LLVM units 26/26; all 395 corpus subjects (83 verifies, 245 must-fail,
     48 tests, 19 test-fails) passed in 192.76s; LLVM CLI passed 7/7, including
     the strong-hook allocation/free, zero, OOM, OOB, early-return, branch, and
     loop fixture at Clang `-O0` and `-O2`; the exact interpreter/native
     differential passed 1/1 over six subjects at both levels; and SVM stayed
     green at 86/86. Randomized allocator, grind-budget, LSP, documentation,
     diff-check, and static-audit gates were green. G1.6 is closed.

     **G1.7 — borrowed Boolean-array parameters (checker and VC complete,
     ADR 0068):** `&[bool]` and `&mut [bool]` are ordinary parameters. Nothing
     in the array-parameter proof path was integer-specific: `lean_array_ty`,
     the parameter binder and its `_old_` twin, the loop and call-site havoc,
     the element read and store bridges, and `Sable.Seq` itself were already
     payload-generic. What refused the shape was a set of gates spelling
     `[bool]` with an accessor that looks through the borrow, so each gate now
     asks the question it was written for: an owner is restricted to a local
     value, and a borrowed array carries a proof model wherever `&[T]` does.

     The parameter's well-formedness is the length fact
     `0 ≤ m.len ≤ u64.max` and nothing else. There is no element fact, because
     `Bool` is already its complete value domain — the analogue of an integer
     array's range hypothesis does not exist rather than being omitted. Loop
     havoc leaves a shared borrow alone (it is never a store target) and gives a
     unique borrow a fresh binder plus length preservation, which is what
     `Seq.len_set` justifies.

     `type.bool_array_param` and `type.bool_array_borrow` are deleted rather
     than narrowed: the parser's `P::Param` row already refuses an owned array
     of every element type, so a narrowed refusal would have been a diagnostic
     no source program could reach. `type.trait_param_unsupported` gains arrays
     in any binding mode, closing a panic that an `&[u64]` trait signature
     could already reach.

     `corpus/verifies/bool_array_params.sable` verifies 37/37 obligations
     across six functions with one hand discharge, covering reads, an element
     invariant, a reborrow passed to a second function, an owner lending a
     literal, a `&mut [bool]` writer with `old m`, and a `&mut` round trip
     whose post follows only from the callee's posts over the fresh sequence.
     `docs/type-matrix.md` opens `[bool]` × `param` and `[bool]` × `param &mut`
     (33/81 → 35/81) and no other cell.

     **G1.8 — the same shape at run time (interpreter and monitor complete,
     ADR 0068):** `sable test` runs a borrowed Boolean-array parameter with its
     contract monitored. No execution code was written: the runtime array is
     payload-tagged, `ExprKind::Borrow` hands the callee the caller's own
     handle, and owned-parameter destruction matches the bare constructors, so
     a `&mut [bool]` writes through and a lent array still dies with its owner.
     The gates split the way the checker's and VC generation's did — an owner
     is restricted to a local value, a borrowed array transports wherever
     `&[T]` does.

     The monitor needed nothing either. A frame snapshots a unique borrow's
     array at entry for `old p`, and the snapshot carries the payload, so
     `m.len`, `m.get k`, a bounded `∀`, an `↔`, and `(old m).get k` all
     evaluate. `corpus/tests/test_bool_array_params.sable` runs the verified
     subject's contracts across seven tests at **zero skipped clauses and no
     `expect-skip` fence**. `docs/shape-admission.md` opens
     `&[bool]`/`&mut [bool]` × `interp type` and no other cell;
     `docs/type-matrix.md` does not move.

     **G1.9 — the same shape in the formal machine (complete, ADR 0069):** a
     formal SVM call argument is `Arg.byValue e` or `Arg.lend x`. Both supply
     the same entry value, so evaluation order, the ⊥-read, and argument traps
     are unchanged; what lending adds is where the value goes back. `Arg.loans`
     pairs each lent argument with the parameter that receives it, `call_enter`
     records that list in the frame, and both `ret_pop` and `nil_pop` apply
     `Env.restore` before binding the destination — a procedure writes through
     a `&mut` parameter as often as a function does.

     Copy-in/copy-out is faithful because a unique borrow is exclusive: no
     second name reaches that storage while the callee runs, and the machine
     has no concurrency. A shared borrow therefore needs no constructor; `Val`
     is unchanged, and a borrow is still not a machine value.

     The rules, the evaluator, and both directions of the agreement theorem
     moved together and no proof needed real work — the write-back is a total
     function both sides name, so every arm kept its shape. `SVMArrayTests`
     pins write-through, the by-value contrast, both ways of leaving a body,
     loan composition through frames, a terminal callee trap, the payload tag
     crossing the call, the ⊥-read, and an integer array lending identically.

     `lower_fn_entry` admits a borrowed array parameter of any payload, and
     `lower_arg` reads the argument form off the argument's type rather than
     its syntax, so a `&mut` reborrow passed on by name still lends.
     `corpus/svm-diff/bool_array_borrows.sable` compares ten zero-argument
     subjects against `interp.rs`; removing the `lend` arm makes three of them
     diverge. `docs/shape-admission.md` opens `&[bool]`/`&mut [bool]` ×
     `svm parameter` and no other cell; `docs/type-matrix.md` does not move.

     **G1.10 — the same shape natively (complete, ADR 0070):** `&[bool]` and
     `&mut [bool]` are parameters of internal ordinary functions. The IR type
     of a borrowed array is the IR type of the array — one
     `%sable.array.bool` descriptor, passed by value — so the emitter gained no
     type, no hook, no trap kind, and no element encoding. What split is the
     question each site asks: `is_owned_bool_array` still decides ownership
     (which declarations allocate, enter the cleanup registry, and free), and
     the borrow-transparent `is_bool_array` decides representation (the IR
     type, the descriptor loads, element addressing, index and length bases).
     A borrow therefore never enters a cleanup scope.

     Write-through is the shared data pointer, not a copy-out: the callee's
     descriptor copy holds the caller's pointer, so a store lands in the
     caller's bytes during the call. That is deliberately not the formal
     machine's mechanism (ADR 0069 restores a loan at the pop); both are
     faithful because a unique borrow is exclusive, and
     `corpus/llvm-diff/bool_array_borrows.sable` compares the interpreter's
     answer with Clang `-O0`/`-O2` rather than assuming they agree. The
     mangled component generalizes to `a` + element code + `s`/`m` (`abs`,
     `abm` beside `au32s`, `au32m`); it stays internal and versionable, and no
     array ABI follows. Owned array parameters and returns, entries, fields,
     externs, other widths, exposure, and container containment stay refused.

     `docs/shape-admission.md` opens `&[bool]`/`&mut [bool]` × `llvm
     parameter` and no other cell — those rows now match `&[u32]`/`&mut [u32]`
     in all three LLVM columns; `docs/type-matrix.md` does not move, because
     the backend is not on the verification path.

     **The backend's type lowerings are total (ADR 0071).** `llvm_ty` and
     `type_code` answer `Option<String>` for every `Ty` instead of ending in
     `unreachable!`; `None` becomes a spanned
     `internal.backend.type_lowering` diagnostic naming the shape and the
     declaration. The `require_*` gates still refuse first under their own
     names, and `llvm_lowering_is_total_on_admitted_shapes` still checks that
     implication — what changed is that its failure mode is now a bad
     diagnostic rather than a process abort. `IntTy::bits`/`min`/`max` and
     `integer_type_code` keep their separate post-monomorphization contract.

     **A borrow is not a local binding (ADR 0072).** `var view = &mut a;` bound
     a *snapshot* of the owner's symbolic term under a second name, so a store
     through either name moved only that entry while both stayed believed —
     `sable check` proved false postconditions over arrays of every payload,
     classes, class fields, resources, and `unsafe expose`, and an aliased pair
     of arguments proved a false post for an ordinary borrow-free callee.
     `check::local_ty` now refuses a local whose type is not owned, under
     `type.borrow_local_unsupported`, keyed on `Ty::binding_mode()` so it holds
     for every referent. This fences the hole: there is still no loan map and
     no loan liveness, and what holds instead is that a borrow exists only
     where the compiler already relates it to its owner — at a call, as an
     argument, for the length of that call. Borrow locals would need an
     aliasing model of their own; that is not scheduled, and this rule is what
     such a model would replace. `docs/shape-admission.md` gains a `check
     local` column; `docs/type-matrix.md` does not move, because a borrow has
     no declared local spelling for a source-level probe to write.

     **An exposure freezes its owner (ADR 0073).** The same defect class had
     one more door: `unsafe expose` left the exposed array's name live in the
     body, so the owner and the loan were two believed names for one buffer —
     a direct store beside a raw load proved contradictory postconditions, a
     direct store beside a raw store was silently discarded by the exit
     copy-back, and a nested exposure of the same array was accepted (ADR
     0026's claim that the borrow rules already rejected it was wrong; the
     borrow-conflict rule is consulted only within one call's argument list).
     The checker now freezes the owner's name for the body under
     `expose.owner_frozen` — read, write, index, `.len`, borrow, field move,
     and re-exposure are all refused; a length the body needs is bound to a
     local before the loan opens. Six must-fail subjects guard the doors;
     `copy_prefix`, `fill_all`, `checksum_all`, and `read_into` hoist their
     lengths and verify unchanged. Neither admission table moves.

     **Checker and VC generation admit copyable option parameters.** An
     `option<u64>`-family or `option<bool>` parameter now crosses the call
     boundary by value: the callee binds `Option Int` / `Option Bool` with the
     accessor/match surface an option local already has, an integer payload
     carries `h_p_range` over `.value` (sound under ADR 0008's `getD default`
     junk model — the absent case reads 0, in range for every integer type),
     and the caller substitutes the parenthesized option chain into the
     callee's clauses. A return binder still transports only the callee's
     posts — a deliberate asymmetry recorded at the parameter arm. The
     type-parameter payload keeps `type.option_param` (no abstract option
     transport across a call), trait methods extend
     `type.trait_param_unsupported` to options, init/method parameters stay
     behind `type.member_param`, the affine family stays behind
     `type.affine_option_param`, and the LLVM backend lowers the
     `option<bool>` parameter through the existing `%sable.option.bool`
     by-value aggregate — `corpus/llvm-diff/option_param.sable` pins literal,
     local, call-result, and forwarded arguments against Clang at `-O0`/`-O2`
     — while the `option<u64>`-family parameter keeps `backend.unsupported`
     (the type has no LLVM representation in any position, so a lone parameter
     lowering would be incoherent). The interpreter executes option parameters and
     the monitor checks their contracts at the call boundary — match-shaped
     posts over a parameter, `.is_some` pres, the absent case's typed junk
     `.value`, and copy semantics at the argument, pinned at zero skips by
     `corpus/tests/test_option_param.sable`; a stored option field then
     kept `interp.option_position_unsupported`.
     `corpus/verifies/option_param.sable` carries the
     match-shaped contracts, the payload-fact proof, and the some/none
     callers; `docs/type-matrix.md` opens `option<u64>` × `param` and
     `option<bool>` × `param` (35/81 → 37/81) and no other cell;
     `docs/shape-admission.md` moves exactly `check parameter`,
     `vc parameter position`, and `svm parameter` for those two shapes, plus
     `llvm parameter` for `option<bool>` alone.
     SVM lowering transports the parameter as an ordinary `Arg.byValue`
     machine value — the untyped `Val.opt` already crosses `call`/`ret`, so
     the rules, evaluator, and agreement proofs needed no change — with
     `corpus/svm-diff/option_params.sable` pinning some/none transport,
     option-local and forwarded-parameter arguments, round trips through an
     option-returning callee, and the absent-`.value` trap, in both payload
     families; the program-wide SVM strictness re-check keeps trait option
     parameters and returns, stored option fields, and the affine family
     refused by their own names.
     **A havoc path is exhaustive or it is wrong (ADR 0074).** An audit of VC
     generation confirmed five defects with one common cause: "fresh symbolic
     state for a type" existed as several divergent `match`es over `Ty`, and
     every wildcard arm silently kept a stale chain — the prover then read
     pre-loop or pre-call values as post-mutation state. Two were false
     proofs (`sable check` said `fully verified` about contracts `sable test`
     refutes): a class-valued field reassigned in an init loop was never
     havocked, and a `raw<u8>` local mutated in a loop kept its pre-loop
     chain, so a proved-trap-free program trapped. One was fail-open: sealed
     resource ops destructured borrow arguments ignoring `field`, so a
     destructor's `&mut self.<field>` panicked `split_off` at an
     `unreachable!` and would have clobbered `self` in the other arms — now a
     named checker refusal, `resource.field_borrow_op`, with the local-move
     rewrite in the note and a fail-closed latch in every arm. One was a
     wrong-layer error: a deinit whose loop assigns a field hit a
     generated-Lean identifier error; `Cctx::Deinit` now joins the method
     case (fresh `_self_loop`, field facts, no class invariant). And one was
     a landmine: the method-call arm lacked the plain-call arm's `&mut [T]`
     argument havoc, unreachable only because `type.member_param` — then
     pinned by zero corpus subjects — refuses the spelling. The fix vehicle
     is `Generator::fresh_state_for(ty, binder, base, len)`: parameter
     entry, the one call-site havoc (`havoc_mut_borrow_args`, now used for
     arrays too, by ordinary, method, and constructor calls alike), and both
     loop-havoc branches all consume it, and its dispatch over `Ty` has no
     wildcard — a shape with no fresh-state story latches `refuse_vc_type`.
     Both false-proof reproducers flipped from `fully verified` to unproved;
     each defect carries corpus subjects in both directions (must-fail +
     test-fails for the false contracts, verifies + tests for the sound
     rewrites), and `type.member_param` gained one must-fail per refused
     family. Neither admission table moves a cell.

     The havoc dispatch is additionally guarded by a per-arm loop corpus:
     every type a loop body can mutate has a `corpus/verifies/loop_havoc_*`
     subject whose contract observes the post-loop state, with a
     `corpus/tests/test_loop_havoc_*` twin running the same contracts at
     zero unfenced skips — integer, Boolean, template-parameter, copyable
     option, owning option (loop `.take`; whole-option reassignment stays
     refused), nullable-pointer option, record, class, owned
     integer/Boolean array, resource-view parameter, and resource-field
     arms, plus named runners for the raw-pointer and init-loop
     class-field shapes and a `type.array_assign` must-fail for the one
     refused loop mutation (whole-array rebinding). `&mut`
     array/class/resource parameters mutated in loops and method-context
     field loops were already held by `insertion_sort`,
     `bool_array_params`, `class_values`, `free_list_walk`, and
     `hashmap`. A new arm added to `Ty` without a
     battery pair is a compile error first (`fresh_state_for` is
     wildcard-free) and a missing-subject review question second.

     **The exposure copy-back model is pinned, and the LLVM `expose`
     refusal is load-bearing.** Proof, interpreter, and formal machine all
     model `unsafe expose` as copy-in/copy-out — the loan takes the
     owner's bytes at entry, a mutable exit rebuilds the owner from the
     loan's final bytes — and that model is faithful only because ADR
     0073's freeze makes the loan the storage's sole name for the body.
     `corpus/verifies/expose_copy_back.sable` and its test twin pin the
     observable in both directions: a `raw_store8` through the loan is
     seen through the owner after the body, and every other byte
     survives. The third consumer, `llvm.rs`, refuses `Stmt::Expose`
     under `backend.unsupported`, and that refusal is what keeps the
     three-way agreement true: a native lowering that handed the body a
     real pointer into the owner's storage would falsify the copy model
     the proofs and both executables share. It must not be lifted until
     (a) the ADR 0073 freeze is enforced on whatever the native path
     admits, so no second name can reach the storage while the loan is
     out, and (b) exposure has a genuine aliasing story — a decided
     semantics for the loan *being* the owner's storage, carried through
     the machine rules, the evaluator, the agreement proofs, and the
     differential gates together — rather than an unreviewed switch from
     copies to pointers.

     **Checker and VC generation admit copyable member parameters.** A
     `bool`, `option<u64>`-family, or `option<bool>` parameter of a class
     init or method crosses the member boundary by value exactly as it
     crosses a plain call: the body binds the same `Bool` or `Option`
     entry state (member bodies already share `fresh_state_for`), and the
     caller substitutes the reified Boolean or the parenthesized option
     chain into the member's clauses — the method-call arm gained the one
     missing reification; the constructor arm already had both. The same
     discharges the plain-call subjects use close the match-shaped member
     posts (`corpus/verifies/member_value_params.sable`).
     `check::member_param_ty` keeps one name, `type.member_param`, for
     every family it still refuses (records, raw pointers, options of
     anything but a concrete value payload, owned arrays, `&mut [T]`,
     method `&[T]`), and its option arm matches the owned option
     directly, so borrow spellings stay behind
     `type.borrow_param_unsupported`. The interpreter and monitor needed
     nothing: member contracts over the new parameters run at zero
     skips — match-shaped init and method posts, `.is_some` pres, `old
     self` frames beside a `bool` argument, the absent-`.value` trap, and
     copy semantics at both member boundaries
     (`corpus/tests/test_member_value_params.sable`); each false-contract
     direction carries a must-fail + test-fails twin, and `corpus/pairs/`
     pins member-vs-free agreement (same-run) and argument-naming
     invariance (same-lean). The formal SVM has no member-call leg to
     extend — `CtorCall`/`MethodCall` are outside the core subset, so no
     svm-diff subject can exist — and the LLVM backend keeps every member
     call behind the fixed-owner fences; the initializer-parameter
     validator drops its unreachable `bool` admission so the newly
     spellable shape is a named refusal, not an uncovered lowering.
     Cross-module transport rides the existing artifact path
     (`corpus/verifies/member_param_import.sable`), and a class
     template's concrete `bool`/option member parameters admit at the
     instance (`Slot<T>` in the same subject).
     `docs/type-matrix.md` opens exactly `bool`, `option<u64>`, and
     `option<bool>` × `init param` and `method param` (57/210 → 63/210);
     `docs/shape-admission.md` moves exactly the `check init param` and
     `check method param` columns for those three shapes.

     **Stored option state (ADR 0076).** `option<u64>`-family and
     `option<bool>` class fields open end-to-end: the payload-driven gate
     (the abstract payload keeps `type.option_field`, the checker's own
     fence since mono instantiates first), the field accessor surface
     (`self.f.is_some`/`.value` through the ordinary postfix accessors),
     the stored state's `.value` range fact beside the field facts every
     whole-object state carries, `old self.f` in posts and as a match
     scrutinee (the monitor's `match_opt` now takes `old` paths), the
     interpreter's field gate split by container (record fields keep
     `interp.option_position_unsupported`), and both loop-havoc branches.
     The groundwork commit made all four field-state dispatches explicit
     and fail-closed first (ADR 0074 discipline; type-snapshot
     byte-identical, no cell moved) and added `vc class field` and
     `interp class/record field` admission columns. 122 obligations in
     `corpus/verifies/option_field.sable` plus an importing module, a
     zero-skip tests twin, four must-fail + three test-fails negation
     twins, and two same-lean pairs; `docs/type-matrix.md` opens exactly
     the two class-field cells (63 → 65 of 163 intended).

     **A nullable owning handle (ADR 0080).** `option<class>` joins the
     affine family: take is skolemization through the one havoc dispatch
     (fresh binder pinned by `old = some taken`; the closed producer set
     is what makes invariant-at-take sound), the wrap consumes its
     source, and the single semantic edit is the interpreter's drop
     routing — a present payload dies through `drop_value`, a trap runs
     no destructors. The exact-once discipline lands as both corpus
     halves plus trap-beats-deinit; the monitor's affine snapshot is
     payload-generic; every boundary closes in the family's names with
     zero SVM/LLVM edits (no differential oracle exists for the cell —
     behavior is pinned by interp + corpus). 74 of 180 intended open.

     **Record elements are values (ADR 0079).** `[record]` opens across
     locals, element reads/stores, borrows, and init `&[record]` — the
     payload family split by container (array gates admit, option gates
     refuse, each in its own name), elementwise `R.wf` as the element
     fact with the emitted `wf_iff` unfolding lemma automation needs,
     `a[i].x` pinned as a non-place in both directions, class fields
     behind `type.record_array_field` until the field-element paths
     generalize, off-range junk deliberately unanswered by the monitor
     (Seq junk is unconstrained; no Lean default exists to mirror). The
     class-field parity commit then removes the interim gate and makes
     the three field-element paths payload-driven, and the machine
     commit adds `ValTag.record` carrying the declaration tag — the
     agreement proofs survived unchanged, the `#guard` battery pins
     cross-record stores as tag confusion beating OOB, and
     `corpus/svm-diff/record_arrays.sable` compares six A-normal
     subjects against the interpreter, both trap depths included. The
     matrix gains the `[record]` row: 73 of 180 intended open.

     **Option nesting is the recursive family (ADR 0078).**
     `option<option<T>>` — a founding example of the representation
     problem — is a type at any depth for concrete value leaves, in
     locals, returns, and plain parameters. The widening went through
     ADR 0077's classification as designed: one new family variant
     (`OptionOfValue`, admitted when the inner payload is `Value` or
     itself), and every wrapper a compile error until each stage
     answered — option wrappers admit, array wrappers refuse (no
     per-element option storage), the VC position gate splits parameter
     transport from flat-only field storage. One recursive helper emits
     the single range fact at the chain's integer leaf; the junk model
     composes per level, and marking core's `Option.default_eq_none` as
     simp made the whole junk-obligation class automatic — the first
     down payment on the tactics direction. Members and fields keep
     their refusals in their own names; the interp class-field gate
     stays deliberately wider (executability, not policy). The corpus
     battery includes the first container-slice svm-diff subject (the
     machine was already recursive) and depth-three pins;
     `docs/type-matrix.md` opens exactly the two option-payload cells
     (65 → 67 of 163 intended).

     **A closed cell is work or a decision (ADR 0075).** The matrix's
     closed cells now say which kind of closed they are: `not yet` (work
     remaining, the fail-safe default) or `never` (a recorded decision
     with its reason, pinned in the `NEVER` table and red-tested in both
     directions — a by-design cell the front end starts admitting cannot
     be blessed over). Progress reads against an honest denominator:
     **63 of 163 intended cells open; 47 never open by design.** The
     first draft of the decision table overclaimed seven cells that
     ADRs 0026/0029/0031/0054 hold open — struck on review, which is the
     argument for the fail-safe default recorded in the ADR.

   - **G2 — affine options (staged; G2.0–G2.3 complete):**
     carry ownership and destruction correctly through present/absent aggregate
     values without widening the existing copy-option family by accident.

     **G2.0 — representation/fail-closed foundation (complete):** a
     conditionally owning array option is a checked identity no copy-option
     rule can reach by accident. The parser accepts `option<[T]>` for Boolean,
     integer, or in-scope type-parameter payloads. Monomorphization must
     validate, substitute, and recheck that identity. The checked
     representation also carries a record payload case, and module traversal
     must enforce its nominal visibility for future or synthetic checked-AST
     inputs; the surface parser does not yet construct that case. Since
     ADR 0065 `Ty::Option(Box<Ty>)` is the only option constructor and
     ownership is computed from the payload (`option<[T]>` is an option over
     an owned array), so each rule that would duplicate an option asks
     `Ty::as_affine_option_payload` explicitly instead of relying on a
     constructor it cannot name.

     G2.0 deliberately had no construction, accessor, move, destruction,
     proof, interpreter, machine, or native semantics. The checker, VC
     generator, interpreter, Rust-to-SVM lowerer, and LLVM emitter each rejected
     an owning option before copy-option semantics could be selected. At an
     otherwise-admissible direct ingress they used stable `type`, `vc`,
     `interp`, `svm`, and `backend` `affine_option_unsupported` diagnostics
     respectively. That remains the G2.0 closure claim; G2.1 opens only the
     local checker/proof/interpreter/monitor subset below. Existing copyable
     options retain their current behavior.

     The exact closure command was
     `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
     SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
     --test-threads=1 --nocapture`. `cargo check` and standalone
     `lake -Kjobs=1 build` were green; Lake built 22/22 targets with only the
     same existing linter warnings. Rust library tests passed 192/192; all 396
     corpus subjects (83 verifies, 246 must-fail, 48 tests, 19 test-fails)
     passed in 192.03s; LLVM CLI passed 7/7; exact interpreter/native
     differential passed 1/1 over six subjects at `-O0` and `-O2`; and SVM
     differential stayed 86/86. Randomized allocator, grind-budget, LSP,
     doc-tests, rustfmt, diff-check, and static-audit gates were green. G2.0 is
     closed.

     **G2.1 — local construction and take (complete):** admit only explicit
     mutable local `option<[bool]>` values with
     mandatory initialization by `none` or directly by
     `some(alloc_array<bool>(len, init))`. Wrapping an existing owned array and
     Boolean-array literals remain rejected. `.is_some` observes without
     consuming or cloning; program `.value` remains forbidden. `.take` is a
     named-place operation accepted only as the direct initializer of an
     explicit owned `[bool]` local. It atomically checks presence, transfers the
     payload, and leaves the mutable source initialized as `none`; it does not
     move the option container or introduce a presence typestate lattice.

     VC generation models the local as `Option (Sable.Seq Bool)`, discharges
     someness against a pre-update snapshot, and updates the symbolic source to
     typed `none`; take participates in loop mutation/havoc collection. The
     interpreter uses a separate runtime affine-option value, mutates the named
     slot atomically, and recursively drops a present payload exactly once.
     The proof monitor observes immutable snapshots. Affine payload clauses
     use option `match`; affine `.value` is unmonitorable because `Sable.Seq`
     intentionally has no global `Inhabited` instance. Parameters, returns,
     calls, fields, traits, generics, borrows, exposure, nested or non-Boolean
     affine options, whole-option assignment, inferred bindings, and discarded
     affine temporaries remain closed.

     G2.1 closed under the exact one-worker command
     `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
     SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
     --test-threads=1 --nocapture`. `cargo check -j1` was green, and standalone
     Lake built 22/22 targets with only the same existing linter warnings. Rust
     library tests passed 211/211; the recursive corpus passed all 416 subjects
     (84 verifies, 263 must-fail, 49 tests, 20 test-fails) in 193.06s; LLVM CLI
     passed 7/7; the native differential passed 1/1 spanning six subjects at
     `-O0` and `-O2`; and SVM differential remained 86/86. Randomized free-list
     allocator, grind-budget, LSP, documentation, rustfmt, diff-check, and
     static-audit gates were green. G2.1 is closed.

     **G2.2 — formal machine (complete):** the
     relational SVM and proved evaluator now carry atomic statement-level
     `Stmt.optTake dst src` over the existing recursive `Val.opt`; the formal
     core is intentionally generic, while Rust lowering admits only the exact
     `option<[bool]>` source and owned `[bool]` destination from G2.1. A pure
     extraction followed by assignment is not an acceptable model because its
     intermediate state has two owners.

     For distinct names, present transfers the payload in one step while
     clearing the source to `none`; absent traps `optionNone`; and a missing or
     wrong outer source is `undef`. Aliasing source and destination is
     immediately `undef`. Destination absence is not required because the flat
     machine environment reuses lexical-local names across loop iterations;
     the take overwrites that stale binding. The tagged Boolean-array payload,
     including an empty array, is retained exactly. Parameters, returns, calls,
     fields, traits, generics, borrows, exposure, whole-option movement, and all
     affine-option ABIs remain fenced. At the G2.2 checkpoint LLVM still
     rejected the type pending the separate G2.3 widening.

     G2.2 closed under the exact one-worker command
     `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
     SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
     --test-threads=1 --nocapture`. `cargo check` and the standalone Lake build
     were green; Lake built 22/22 targets with only the existing warnings.
     Focused SVM units passed 35/35, Rust library tests 211/211, and the
     recursive corpus all 416 subjects (84 verifies, 263 must-fail, 49 tests,
     20 test-fails) in 270.58s. LLVM CLI passed 7/7; the native differential
     passed 1/1 over six subjects at `-O0` and `-O2`; and SVM differential
     passed 92/92. Free-list allocator, grind-budget, LSP, documentation,
     rustfmt, diff-check, and static-audit gates were green. G2.2 is closed.

     **G2.3 — native local lowering (complete):** the internal value is
     `%sable.option.array.bool = type { i8, %sable.array.bool }`. Tag zero is the
     full zero aggregate; tag one owns the nested descriptor, including the
     null/zero descriptor of a present empty array. LLVM admits only explicit
     mutable local `option<[bool]>` construction by `none` or direct
     `some(alloc_array<bool>(...))`, named `.is_some`, and `.take` directly into
     an explicit owned `[bool]` local.

     Take guards tag one using existing option-none trap kind 8, extracts the
     descriptor on the success edge, stores the complete source as zero, and
     only then installs the destination. The cleanup registry is typed over
     ordinary Boolean arrays and affine Boolean-array options and unwinds both
     in reverse declaration/scope order. Option destruction calls the existing
     free hook only after both a tag-one and nonnull-pointer check. Absent,
     taken, and present-empty options perform no free; trap edges perform no
     cleanup. Construction and payload access retain the existing allocation
     and free hooks, 50,000,000-element cap, zero bypass, and trap kinds 9 and
     10.

     Parameters, returns, call transport, entries, externs, fields, traits,
     classes, generics, borrows, exposure, inferred bindings, whole-option
     assignment/movement, discarded affine temporaries, non-Boolean payloads,
     and existing-array or literal wrapping stay fenced. The named type is
     internal and versionable; no affine-option ABI follows. G2.3 closed under
     the exact standard command
     `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
     SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
     --test-threads=1 --nocapture`. `cargo check` was green; standalone Lake
     built 22/22 targets with only the existing warnings; focused LLVM units
     passed 29/29; and Rust library tests passed 213/213. The recursive corpus
     passed all 416 subjects (84 verifies, 263 must-fail, 49 tests, 20
     test-fails) in 194.43s. LLVM CLI passed 8/8; the exact interpreter/native
     differential passed 1/1 over seven subjects at Clang `-O0` and `-O2`; and
     SVM differential remained 92/92. Free-list allocator, grind-budget, LSP,
     documentation, rustfmt, diff-check, and static-audit gates were green.
     G2.3 is closed.
   - **N0 — native `u32`-array foundation (closed):** admit exactly fresh owned
     local `[u32]` literals and
     `alloc_array<u32>` values, length/index/store, and explicit named
     `&[u32]`/`&mut [u32]` arguments to internal ordinary functions. The
     internal descriptor is `%sable.array.u32 = type { ptr, i64 }`; allocation
     scales logical length by four bytes while traps retain logical lengths.
     The existing v1 hook promises byte storage only, so typed element loads
     and stores are explicitly `align 1`. Zero bypass, the 50,000,000-element
     cap, kinds 9/10, reverse lexical cleanup, no cleanup on traps, and the
     existing versioned hooks are unchanged.

     Borrow parameters are non-owning and accepted only through the exact
     checked borrow node with matching mutability. Owned-array parameters and
     returns, fields, classes, methods, entries, externs, other payloads,
     whole-value transport, and every array ABI remain fenced. Verification,
     interpretation, and the formal integer-array value predate N0; this is an
     LLVM/runtime widening, not a new proof rule.

     N0 closed under the exact one-worker command
     `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
     SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
     --test-threads=1 --nocapture`. `cargo check` was green; focused LLVM units
     passed 31/31; Rust library tests passed 215/215; and all 416 recursive
     corpus files (84 verifies, 263 must-fail, 49 tests, 20 test-fails) passed
     in 213.51s. LLVM CLI passed 9/9; the exact interpreter/native differential
     passed 1/1 over eight subjects at Clang `-O0` and `-O2`; and SVM
     differential remained 92/92. Randomized allocator, grind-budget, LSP,
     documentation, rustfmt, diff-check, and static-audit gates were green.

   - **N1a — fixed-owner native `Nat` construction and comparison (closed):**
     admit exactly one concrete class shape with one owned `[u32]` field, no
     methods, and an explicit empty destructor. The internal representation is
     `%sable.class.<id> = type { %sable.array.u32 }`. A direct constructor call
     initializes a final immutable stack owner through an internal
     destination-pointer initializer; the initializer must establish its field
     exactly once from fresh array storage on every path before any field
     store. Reverse lexical cleanup frees the nested limb allocation.

     Internal ordinary functions may accept shared `&Nat`; calls require the
     exact checked, fieldless named borrow and lower it as a non-owning pointer.
     Successful class/resource/field borrows now retain their checked `Expr.ty`,
     preserving the LLVM backend's fail-closed revalidation. Constructor and
     function closure selection, initializer mangling, class-field length/index
     operations, and unaligned limb accesses are all internal-only.

     The end-to-end subject imports the real verified `Nat::from_prefix` and
     `cmp`, checks copy independence plus less/equal/greater and zero cases, and
     returns 42 in the interpreter and Clang at `-O0`/`-O2`. Mutable owner
     locals, reassignment, moves, returns, owned class parameters, methods,
     mutable class borrows, multiple/nested fields, generic classes, nonempty
     destructors, extern crossings, and a public class ABI remain fenced.

     N1a closed under the exact standard one-worker command. `cargo check` and
     rustfmt were green; focused LLVM units passed 33/33; Rust library tests
     passed 217/217; and all 417 corpus subjects passed (85 verifies, 263
     must-fail, 49 tests, 20 test-fails), including the 19-obligation native
     bignum subject. LLVM CLI passed 9/9; the exact interpreter/native
     differential passed 1/1 over nine subjects at Clang `-O0` and `-O2`; SVM
     differential remained 92/92; and randomized allocator, grind-budget, LSP,
     documentation, and diff-check gates were green.

   - **N1b — internal fixed-owner returns and moves (closed):** lower an
     internal class-returning free function as `void` with a caller-supplied
     destination pointer. A return or final local declaration may initialize
     that destination from the existing constructor path, another internal
     class-returning call, or one live named local owner. A named move copies
     the aggregate and zeros its source before lexical cleanup, so the existing
     null-safe nested-array destructor remains the single cleanup mechanism.

     Move validation is path-sensitive and fail closed. Later reads or borrows
     of a moved owner are rejected; two reaching `if` arms must have identical
     move state; a terminating arm contributes no successor state; and a
     reaching loop backedge may not change the owner-liveness shape. The real
     imported bignum fixture mirrors `Nat::from_prefix`'s preconditions and
     verifies direct construction return, tail return calls, local-to-local
     movement, moved-local return, and early-return/fallthrough selection while
     preserving exit 42.

     This remains an internal exact-shape convention, not a Sable or C class
     ABI. Mutable owners, reassignment, owned class parameters, methods,
     mutable class borrows, discarded class results, moves from fields,
     broader/nested/generic shapes, nonempty destructors, extern transport,
     and public/cross-module class ABIs remain rejected.

   - **N2 — native `Nat` addition (closed):** admit the real imported bignum
     `add` call closure using the representation and lifetime mechanisms
     already closed by N0–N1b. Shared `&Nat` inputs and reborrows remain
     non-owning; scalar length/limb helpers drive a fresh local `[u32]` scratch
     buffer through a carry loop; trimming and `Nat::from_prefix` construct the
     result; and the existing hidden destination convention carries that
     result through a return or one named move. The scratch buffer and nested
     result allocation retain reverse lexical cleanup, while neutralized move
     sources remain null-safe.

     `corpus/verifies/bignum_add_native.sable` verifies all 40/40 obligations
     and covers zero identity, `1 + 2`, a full-width carry, and unequal operand
     lengths. Its emitted program returns 42 when compiled directly with Clang
     at both `-O0` and `-O2`. This checkpoint adds no proof rule, runtime hook,
     class representation, or aggregate ABI.

     Mutable class owners and reassignment remain reserved for N4. The
     subsequent N3 checkpoint below closes `sub` and schoolbook `mul`;
     `div`, `rem`, and `gcd` remain N4, and nested `Integer` ownership remains
     N5. Owned class parameters, methods, mutable class borrows, discarded
     class results, field moves, broader or generic class shapes, nonempty
     destructors, and every public, extern, or cross-module class ABI remain
     rejected.

   - **N3 — native `Nat` subtraction and multiplication (closed):** admit the
     real imported `sub` and schoolbook `mul` closures using only N0–N2's
     representation, call, and lifetime machinery. `sub` borrows both inputs,
     performs checked borrow arithmetic into one fresh `[u32]` scratch array,
     trims the prefix, constructs the result, and returns it through N1b's
     destination convention and named local move. `mul` uses the same pattern
     with nested scalar loops, checked carry/product arithmetic, and one fresh
     output scratch array. Reverse lexical cleanup frees scratch arrays and
     neutralized move sources remain null-safe; no new hook, representation,
     ownership rule, or ABI is introduced.

     `corpus/verifies/bignum_sub_mul_native.sable` verifies all 51/51
     obligations across 19 selected functions. It covers subtraction to zero,
     a borrow chain across two zero limbs, multiplication by zero, a maximum
     limb squared, and a cross-limb carry. Its emitted program returns 42 when
     compiled directly with Clang at both `-O0` and `-O2`.

     Mutable class owners and reassignment remain reserved for N4, together
     with `div`, `rem`, and `gcd` and their loop-carried ownership cleanup.
     Nested `Integer` ownership, by-value class constructor/function arguments,
     class-field borrows, `&mut Integer`, methods, and nested reverse
     destruction remain N5. Owned class parameters, discarded class results,
     field moves, broader or generic shapes, nonempty destructors, and every
     public, extern, or cross-module class ABI remain rejected.

   - **N4 — native `Nat` division, remainder, and gcd (closed):** admit the
     selected closures of the real verified `div`, `rem`, and `gcd` while
     retaining the exact N1a `Nat { [u32] limbs; }` representation. N4 adds
     mutable locals of that shape and class-local reassignment; it does not
     add a class ABI, new runtime hook, or proof rule.

     Each reassignment target receives one scratch slot hoisted to the function
     entry. Lowering evaluates the complete right-hand side into that scratch
     before destroying the old target, so self-borrowing forms such as
     `dd = dd - vn` and `q = shift_in(&q, d)` keep the borrowed owner valid
     until the producing call returns. The old owner is then dropped, the
     replacement aggregate is transferred into its target, and the scratch is
     zeroed. Reassigning a moved mutable target revives it; ordinary moved-value
     checks still reject a read or borrow before that revival.

     Existing lexical cleanup supplies the loop lifetime rule. Owners declared
     in a loop body are destroyed in reverse order before each backedge, outer
     mutable owners keep their function-scope cleanup, and zeroed named-move
     carriers make later null-safe cleanup a no-op. Reassignment scratch slots
     are unregistered and empty after transfer. Reaching `if` arms and loop
     backedges must still agree on which outer owners are live.

     `corpus/verifies/bignum_div_native.sable` verifies all 109/109 obligations
     across 21 selected functions with six small hand discharges. It covers
     division by one, exact and inexact quotient/remainder pairs, a multi-limb
     quotient-estimate correction, and basic, zero-input, and coprime gcd
     cases. Its emitted program returns 42 when compiled directly with Clang
     at both `-O0` and `-O2`.

     The separate N5 checkpoint below adds only the exact nested `Integer`
     closure. Both checkpoints retain internal-only representations and scalar
     process wrappers.

   - **N5 — native signed `Integer` (closed):** admit exactly
     `Integer { Nat mag; u64 neg; }`, represented
     internally as the already-supported `Nat` aggregate followed by an `i64`.
     This is a declaration-specific widening, not recursive class-layout
     inference. Initializer validation tracks `mag` and `neg` independently,
     requires each field to be initialized exactly once on every reaching path,
     and distinguishes scalar initialization from ownership transfer into
     `mag`.

     The internal take convention now accepts an exact owned `Nat` parameter
     for `Integer::make` and `of_nat`. The caller passes the aggregate by value
     and neutralizes a named source. A class-returning argument is first
     produced into a unique entry-hoisted, unregistered scratch destination;
     the completed aggregate is loaded by value and the scratch is zeroed
     immediately before the call. The callee stores the value in an owning slot
     registered for lexical cleanup, and moving that slot into `Integer.mag`
     zeros it. This gives by-value ownership transfer its real callee-drop
     behavior without a caller-side post-call drop or a C, platform, or
     cross-module class ABI.

     Field projection admits the real implementation's scalar reads and exact
     borrows: `x.neg` reads the `u64` field, `&x.mag` borrows the nested `Nat`,
     and `&a.limbs` borrows its array descriptor. Mutable `&mut Integer` lowers
     as a non-owning pointer. Method dependency selection, mangling, validation,
     and emission are opened only for the private unit-returning
     `Integer::flip_sign(&mut self)` reached by `negate_in_place`; its store
     updates scalar `neg` in place while the source verifier remains responsible
     for re-establishing the class invariant.

     Class destruction is recursive and follows reverse declaration order.
     Dropping an `Integer` visits `neg` as a scalar no-op, then drops `mag`,
     which in turn projects `limbs` and uses the established null-checked array
     free. Named moves and owned parameters consumed into fields are zeroed
     before their registered cleanup; the unregistered argument scratch is
     zeroed before the call. Together these preserve one eventual free for each
     nonempty magnitude.

     `corpus/verifies/integer_native.sable` verifies 237/237 obligations across
     39 selected functions. Its small cases cover construction, unary and
     in-place sign operations, addition, subtraction, multiplication, and
     Euclidean division/remainder for positive and negative dividend/divisor
     combinations. The emitted program returns 42 when compiled directly with
     Clang at both `-O0` and `-O2`.

     The dedicated strong allocator-hook test is green under Clang `-O0` and
     `-O2`: it exits 42 with `live = 0`, and aborts on a leak, unknown free, or
     double free. The exact `VerifiedProgram` differential is green 1/1 over
     13 subjects at both optimization levels, including `Integer` exit 42.

     N5 closed under
     `SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1`. The gentle
     serial run passed 223/223 library tests; corpus 1/1 in 93.64s; randomized
     allocator 1/1; grind-budget 1/1; LLVM CLI 10/10; differential 1/1 in
     31.35s; LSP 1/1; SVM differential 1/1; and documentation tests.
     `cargo check -j1` and rustfmt were green as well.

     Owned `Integer` parameters, other owned class parameters, methods beyond
     the exact `flip_sign` call closure, mutable borrows of other classes,
     discarded class results, field moves, additional nongeneric or generic
     class shapes, nonempty destructors, array whole-value transport, and every
     public, extern, or cross-module class ABI remain rejected.

   - **G3 — slots and `Vec` (later planning target):** make generic element
     storage and movement real for the existing growable-vector benchmark;
     neither N0 nor the bignum ladder broadens the option ABI or authorizes
     generic owner storage.
   - **G4 — `HashMap`:** exercise the completed generic aggregate stack with
     key/value storage, probing, and its existing verified contracts.

3. Add printing and formatting together with the smallest practical `String`
   standard-library layer.
4. Introduce `Result`-shaped explicit error handling; keep general surface
   pattern matching deferred until a benchmark demonstrates that accessors or
   combinators are insufficient.
5. Replace flat source merging with real module namespaces and stable backend
   name mangling.
6. Add floating-point types only when a target domain forces their semantics;
   they remain last because rounding modes, NaNs, and proof vocabulary deserve
   a benchmark rather than speculative surface area.

## Parallel track (low intensity)

The SVM semantic oracle — **checkpoint reached, with the first profile
composition and G1.5 Boolean arrays complete and G2.2 affine-option take
complete**. `lean/Sable/SVM.lean` is the
machine as inductive relations, now *total*: `undef` is the third terminal
outcome (ADR 0005 res. 1) covering ⊥-reads, type confusion, and out-of-range
literals, so pillar 1 holds literally. `lean/Sable/SVMEval.lean` adds the
functional evaluator/stepper with two-directional agreement proofs;
determinism, totality, and progress are kernel-checked corollaries. Calls and
frames, byte raw memory, abstract `u64`/POD cells, recursive options (nullable
raw pointers included), and tag-carrying arrays of ordinary machine values
(ADR 0062) all live in both core presentations. G1.5 generalizes
length/index/allocation/store, preserves empty tags and trap precedence, and
adds direct Boolean-array guards. G2.2 adds the generic atomic core `optTake`
transition and an exact Boolean-array affine option bridge. Its full serial gate is green: `cargo check`; Lake 22/22;
focused SVM units 35/35; Rust library tests 211/211; the 416-subject recursive
corpus in 270.58s; LLVM CLI 7/7; six-subject O0/O2 native differential 1/1;
SVM differential 92/92; and the free-list, grind, LSP, docs, formatting,
diff-check, and static-audit gates. ADR 0057's `SVMUart` wrapper remains
byte-for-byte compatible for bare executions.

The full G1.5 serial closure is green: `cargo check`; the 22-target one-job
Lake build; 175/175 Rust library tests; all 394 corpus subjects (83 verifies,
244 must-fail, 48 tests, 19 test-fails) in 266.78s; LLVM CLI 6/6 with
required Clang; exact `VerifiedProgram`↔Clang O0/O2 differential 1/1 over five
subjects; SVM differential 86/86; and
`free_list_return_random`, grind-budget, LSP, and doc-tests. The
older ghost-transition erasure theorem and class track remain separate future
work.

## Testing strategy

`corpus/verifies/` must verify; `corpus/must-fail/` programs carry an `// expect-error:` annotation naming the obligation or diagnostic that must fire. The must-fail corpus is what keeps a trusted VCgen honest (stage-1 trust posture, design §10.1) and doubles as executable documentation of every diagnostic. `corpus/tests/` must pass `sable test -M corpus/verifies` with zero skipped clauses, where a deliberately-unmonitorable subject clause is fenced by `// expect-skip: <substr>` (stale fences fail); `corpus/test-fails/` must be caught with the annotated message.
