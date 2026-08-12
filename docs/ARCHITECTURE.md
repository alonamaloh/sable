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
- **Typed storage is abstract before it is representational** (ADRs 0031–0032). The first complete slice is `PointsTo<u64>`: raw authority over one canonical `u64.layout` converts into an uninitialized typed cell, whose state moves through init/read/take/drop, and converts back only when empty. `Layout` is compiler-established proof vocabulary (positive size, nonzero power-of-two alignment), visible as `T.layout` in generic clauses but never forgeable as a program value. The typed value is never decoded from or serialized into bytes; conversion back explicitly zero-fills as cleanup. Both executable heaps tag typed extents and reject byte access while the tag exists, while Lean VCs see only `PointsToView Int`. The SVM relational rules and evaluator agreement cover all six instructions, and differential subjects compare them with the interpreter.
- **A destructor owns the value outright** (ADR 0029). `deinit` bodies run; the class invariant holds on *entry* and is not re-established, so a destructor owes no `inv_exit` and has no `_old_self`. It may move fields out — the *field* is the place that dies, and untouched siblings stay readable — and a moved field is not dropped again. The interpreter's order within a drop is **invariant → body → remaining fields in reverse declaration order**. Classes hold resource fields; `#[must_consume]` turns an abandoned one from a permitted leak into a diagnostic. `&mut self.f` is legal in a destructor and nowhere else, because the invariant it could break no longer has to hold.
- **A move is one operation, and every sink performs it** (ADR 0030). A declaration, an assignment, a field assignment, a call/constructor/method argument and a return all *take* a value: the source place stops holding it, and whatever the destination held is destroyed. The interpreter has one `take_place`/`drop_place` behind `eval_moved` — overwriting a place runs a full drop (invariant → destructor → remaining fields), a returned local leaves with the caller rather than being destroyed behind it, and an owned parameter dies with the callee's frame after its contract has been checked. The checker has one `transfer` at the matching sinks: it kills the source place, applies the loan-brand rule (recursively, so `raw_offset(p, 1)` cannot launder what `p` may not), and reports whether a `#[must_consume]` obligation travelled with the value. Affinity covers class values, resources, **and owned arrays** — two names reaching the same elements is unsound the same way, and the diagnostic names the category (`class`/`resource`/`array` prefixes on `use_after_move` and `loop_shape`). A member may move a field out but must restore it before it exits (`class.field_not_restored`); only a `deinit` may leave a hole, because only there is the invariant already gone. A contract still reads a moved-from parameter's entry value: a value outlives the transfer of authority over it. Branch joins and loop checks operate over the whole per-place state (`PlaceState`: initialized, branded, obligation) rather than a chosen subset: branches join initialization by AND and brand/obligation by OR over reaching paths, while a loop requires its backedge to preserve affine liveness, brands, and obligations before restoring the zero-iteration entry state. Every `Place` maps to that state by its complete rendered key (`self.f`, not merely `self`). The `#[must_consume]` obligation is a *state of the place*: moving the token clears it, landing sets it, a marked field regains it on assignment, and a live one may not be assigned over. Two corollaries about *where* a value dies: a discarded class-valued result is a temporary with no place, destroyed at the end of its statement, and **`unsafe { ... }` is a marker while an exposure body is a scope** — the block grants vocabulary and has no lifetime (its locals belong to the enclosing function, and the interpreter runs it through `exec_open_block`), while an exposure *is* a lifetime, so the loan's bindings and everything the body declared end at its closing brace. Scope exit rejects a disappearing local that still holds a must-consume token.
- **Non-memory resources, and an explicit world** (ADR 0028). `resource OpenFile` is the authority to use one descriptor (position in the view, as POSIX has it); `resource PosixWorld` is the outside, and any foreign operation touching global state must receive it explicitly — which is what replaces a `modifies` clause over the universe, and lets a caller see from a signature whether a function can reach outside. Authority for a descriptor is carved from the world (`open_file(&mut w, fd)`) with *availability* as a precondition — open, and not already handed out — and carving **spends** it (`PosixWorldView.claimed`, updated functionally as `w.claim fd`), since affinity governs a token that exists and would not stop a second being minted beside it (ADR 0030). The checker tracks tokens, the VCs track the state of the outside. `posix_world(script)` is confined to `test_` functions — the one place authority appears from nothing — and the script is how a test author controls short reads and I/O errors, which the *view* deliberately does not model because no contract can predict them.
- **Foreign contracts are audited, and the build says so** (ADR 0027). `extern "C" #[audit(id := ..., reason := ...)] fn f(...);` owes no obligations — there is no body to check — but its clauses still get well-formedness defs, and the audit metadata is mandatory. Effects are structural: only a passed `resource &mut R` may change, so there is no `modifies` clause in the language. Resources are erased from the ABI. **Nonescape sits on the audited side of the boundary**: that a callee unable to *return* storage cannot retain it is compiler-checked for a verified callee (no globals, so the pointer dies with the frame) and an audited promise for a foreign one, since nothing stops C stashing it in a foreign global — part of what the audit id covers (ADR 0030). The trust manifest is emitted **into** the hashed Lean content, so changing an audit id invalidates an artifact exactly as changing a proof does (ADR 0018's hash is over bytes); importers inherit it through the flat merge. Status reads `verified relative to audited boundary`, never `fully verified`, whenever an extern assumption remains. `sable test` supplies deterministic shims keyed on the *audit id*; an unknown id traps rather than running the empty body.
- **A safe `[u8]` reaches raw memory through a lexical construct, not a proof** (ADR 0026). `unsafe expose &a / &mut a as (p, resource m) { ... }` lends the array's bytes for the body and takes them back: entry binds a span whose bytes are the array's elements, exit makes the array what the bytes say, under generated obligations (the whole extent came back; every byte is present and in `u8` range). Hidden *loan brands* do nonescape with no lifetime syntax — branded values cannot be returned, assigned outside the body, or passed to a user function — and the brand follows provenance through `raw_offset`/`split_off`/`join` but not onto loaded bytes. Raw operations pair a pointer with a resource borrow (`Ty::Raw`, `Val::Ptr`, `SpanView.namesByte`) and live inside `unsafe`; `unsafe regions: N` is reported in build output. `raw_copy_nonoverlapping` carries **no nonoverlap premise**: two distinct affine tokens *are* separation.
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
