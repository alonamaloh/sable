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
  │                                   combined source string; imported checked-class
  │                                   indices and generic-class arities seed dependent
  │                                   parses through separate tables; flat merge → ONE
  │                                   Program. Visibility resolves runtime
  │                                   (fn/class/record), trait, and const namespaces
  │                                   separately before that merge.
  │                                   Every later stage is module-oblivious;
  │                                   ModuleSet retains exact canonical paths,
  │                                   source bytes, resolved edges, and order;
  │                                   locate maps spans back to file/line/column.
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
  │                                   G0 represents and parses type arguments recursively
  │                                   (int/bool/parameter/record/class/array/option), with
  │                                   whole-argument spans and opaque canonical type keys.
  │                                   Paths are capped at depth 64, lists at 256 entries,
  │                                   and each outer argument at 4096 nodes. Wider shapes
  │                                   remain semantic non-v1 and fail closed in mono.
  │                                   Instances are keyed structurally by function/class
  │                                   kind, template base, and original canonical args;
  │                                   exact requests deduplicate while a registry rejects
  │                                   ambiguous legacy emitted names deterministically.
  │                                   G1.0 validates declaration parameter identities
  │                                   before substitution and checks that every ordinary
  │                                   output is concrete. Retained ADR 0009 templates alone
  │                                   carry explicit Ty::Param/ValueTy::Param values into
  │                                   checking and VC generation. Only mono may attach the
  │                                   exact ADR0009IntModel proof-reuse capability; its
  │                                   authorization payload is opaque, and preparation plus
  │                                   VC-generation entry points are crate-private.
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
  │                                   integer values are Lean `Int` strings and
  │                                   program booleans are symbolic propositions;
  │                                   G1.1 stores Boolean options as `Option Bool`,
  │                                   using explicit Prop↔Bool bridges at packing
  │                                   and extraction rather than conflating models;
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
check                                 capture one immutable ProofEnvironment before
  ▼                                   VC/profile work; publish its exact Lean source
  │                                   under .sable-out/proof-envs/<id>/source and
  │                                   build once, under a per-id lock and one Lake
  │                                   job, at the stable .../<id>/built path; READY
  │                                   is written last and is never rebuilt;
  │                                   batch Lean checks the exact generated text
  │                                   against that build + .sable-out/modules;
  │                                   the daemon receives the same text and id,
  │                                   switches servers when the id changes, and
  │                                   falls back to the same batch environment;
  │                                   client disconnect still closes its worker
diagnose (compiler/src/diag.rs)       lean JSON messages → source map lookup →
                                      rendered error: obligation name, goal,
                                      .sable span, context, lean excerpt
```

Generated Lean goes to `.sable-out/` (gitignored): immutable content-addressed roots under `.sable-out/roots/`, one artifact per imported module under `.sable-out/modules/` (`<stem>_<hash>.{lean,olean,ok}`, ADR 0018), and immutable proof environments under `.sable-out/proof-envs/`. Reuse is fail-closed rather than an existence test: generated `.lean` bytes must match exactly, and the artifact must carry the same proof-environment id and the same canonical Sable paths, source bytes, resolved import edges, and order. Those source-graph facts are checked after dependency preparation, around Lean checking, and before publication or root stamping. The in-process cache coalesces only identical builds currently in flight; completed results are not retained. Immutable publication also compares the winner's bytes, so an FNV collision is an error rather than evidence reuse.

The versioned `proof-env-v2-fnv64:<hash>` tag covers `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, and every repository-local `.lean` file under `lean/`; exact byte maps, not the compact FNV tag alone, authorize reuse. Generated content separately records machine-profile ids and hashes, used machine intrinsics, and audited extern ids. `uart-poll-v1`'s displayed profile hash is computed from the immutable snapshot over the recursive local import closure rooted at `Sable/MMIO.lean` and `Sable/SVMUart.lean`, plus `lean-toolchain` and `lakefile.toml`. Thus profile identity states the device-semantics dependency, while the broader proof-environment identity pins everything Lean actually reads.

## Native lowering boundary (scalar v0 and G1.3 Boolean options complete)

ADR 0058 adds a second consumer only *after* the verification path succeeds:
the exact checked, monomorphized AST becomes a `VerifiedProgram`, and a
handwritten textual LLVM emitter consumes that capability. It may not reload
source or accept an unchecked `Program`. This keeps module resolution,
monomorphization, checking, VC generation, and Lean evidence on one side of a
single code-generation boundary rather than building a parallel frontend.

The working `sable build --emit-llvm` path has no libLLVM dependency. Scalar v0
accepts scalar literals, locals, calls, Boolean negation, unit,
`if`, `while`, signedness-aware comparisons, CFG short circuiting, explicit
integer conversions, and checked arithmetic; it rejects unsupported code
within the selected `--entry` call closure (or anywhere in whole-module mode).
Local slots are hoisted to the entry block but their initializer stores remain
at the source declaration, so loops neither grow the stack nor fabricate
initialization. Signed and unsigned add/subtract/multiply and signed negation
use the matching LLVM overflow intrinsics. Division and remainder guard zero
before any LLVM division instruction; signed division also guards `MIN / -1`,
while signed `MIN % -1` bypasses LLVM's invalid `srem` pair and yields zero.
Negative truncating remainders are corrected to Sable's Euclidean quotient and
remainder. Widening uses `sext`/`zext`; narrowing extends into `i128`, checks the
destination range, and only then truncates. Failures call the weak versioned
trap hook and unconditionally continue to the internal `llvm.trap` path. No
`nsw`, `nuw`, `exact`, `inbounds`, or `llvm.assume` promise substitutes for
these checks.

Output carries the exact artifact and proof-environment identities, uses
versionable length-prefixed internal mangling, and file publication is atomic.
Scalar v0's complete low-concurrency regression
(`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`) is green:
26/26 library tests and 6/6 verified LLVM CLI tests, followed by a 1/1 native
differential gate that compares the exact `VerifiedProgram` interpreter outcome
with Clang `-O0` and `-O2` for scalar, control-flow, and arithmetic programs.
Those subjects exercise negative divisors, `MIN % -1`, conversion bounds, and a
loop condition designed to catch hoisting out of the header. All seven published
trap kinds are observed with their exact kind, type-info, and raw operand payload
at both optimization levels; a returning hook still cannot suppress the
mandatory `llvm.trap`. The same serial run kept the SVM differential green at
69/69, completed the full verifier/dynamic corpus in 220.78s, and passed the
randomized allocator, grind-budget, LSP, and documentation tests. LLVM remains
optional for emitting IR. At that checkpoint, aggregate lowering and aggregate
ABIs remained outside the completed scalar boundary.

G1.3 adds one internal aggregate representation without declaring an ABI:
`%sable.option.bool = type { i8, i8 }`, with a tag byte followed by a
canonicalized Boolean payload byte. `none` is `zeroinitializer` (tag zero,
payload zero); `some(false)` and `some(true)` have tag one and payload zero or
one. Internal returns, direct calls, explicit/inferred locals, branches,
assignment, loads/stores, and returns transport the value as a unit. `.is_some`
tests the tag, while `.value` branches to the trap path before extracting the
payload. Kind 8 reports option absence with zero type metadata and operand
payloads, and the common trap helper still invokes mandatory `llvm.trap` after
the weak diagnostic hook returns. The `ob` mangling component is internal and
versionable like the named IR type.

The validation boundary stays narrower than the IR type: no option parameter,
entry, or extern ABI exists; option-valued fields and trait methods,
classes/method calls, residual generic forms, and every non-Boolean option
payload remain rejected. The combined closure evidence appears with G1.2/G1.3
below.

## Key invariants

- **Generic widening starts fail closed.** G0 is complete as a representation,
  parser, identity, and rejection foundation. `GenericTy` and its opaque
  canonical key recurse over integers, `bool`, parameters, records, classes,
  arrays, and options. Each call or constructor `TypeArg` retains the span of
  its complete outer type. The same bounded parser drives lookahead and AST
  construction: a recursive path is at most 64 nodes, any argument list at most
  256 entries, and one outer argument at most 4096 nodes. Imported generic-class
  arities live in a table separate from checked class indices. None of that
  widens v1 semantics: every non-integer shape reaches
  `mono.type_arg_unsupported` before checked types are built. Preparation,
  substitution, and generic-use walks cover record literals, `some(...)`, class
  destructors, and member contracts and variants. Each `InstanceKey` is the
  function/class kind, template base, and original recursive
  `CanonicalTypeKey` arguments, so only exact structural requests deduplicate.
  The collision-free legacy emitted spelling is unchanged; an emitted-name
  registry rejects ambiguous legacy spellings and collisions with source,
  template, or impl-lowered names deterministically. Duplicate traits, impl
  specs, and impl methods likewise diagnose the second source declaration.
- **Parameter identity and proof provenance are explicit before aggregate
  semantics widen.** G1.0 represents declaration parameters as
  `Ty::Param(TypeParamId)` and storable array/option payloads as
  `ValueTy::{Int, Bool, Record, Param}`. It no longer makes a parameter look
  intrinsically integer-valued merely because ADR 0009's current proof model
  is integer-only. Before substitution, mono checks every declaration-position
  parameter id (including expression annotations, conversions, and
  `alloc_array` element types), rejecting out-of-bounds and noncanonical legacy
  forms. After expansion it exhaustively rejects a parameter left in any
  ordinary declaration; retained templates are the sole exception.

  Template-proof reuse is a named capability,
  `ProofReuse::Adr0009IntModel`, rather than a nullable template name. Its
  payload has private fields and a crate-private constructor: external AST
  callers may inspect the marker but cannot manufacture it. Mono rejects a
  pre-populated capability and is its only pipeline author; the preparation and
  VC-generation entry points are likewise crate-private, so external callers
  cannot route a hand-built program around that check. VCgen skips instance
  obligations only when the exact variant is present. This prevents a later
  Boolean or record instance from silently inheriting a theorem proved over
  `Sable.IntModel`. At this checkpoint the checker and VCgen independently
  rejected non-integer aggregate payloads; the interpreter and SVM repeated the
  fail-closed guard at their own execution/lowering boundaries. Module
  visibility also descended through `ValueTy::Record`, so a nominal payload
  could not bypass a restrictive import. G1.0 therefore changed representation
  and invariants, not the accepted language: Boolean/POD arrays and options
  remained unusable, and existing integer behavior was preserved.

  G1.0 is closed by the complete low-concurrency command
  `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
  SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`. It
  passed 101/101 library tests; all 368 corpus subjects (79 verifies, 228
  must-fail, 44 dynamic, 17 dynamic-fail) in 382.78s; LLVM CLI 6/6; the exact
  verified-program interpreter↔Clang differential at `-O0` and `-O2` 1/1;
  and SVM differential 69/69. Randomized allocator, grind-budget, LSP, and
  documentation gates were green. G1.0 is closed.
- **The first Boolean aggregate slice is deliberately local and
  independently fenced.** G1.1 admits `option<bool>` returns on ordinary
  functions and inherent class methods, plus explicit and inferred locals,
  contextual `some(bool-expression)` and `none`, assignment, calls returning
  the type, `.is_some`, and `.value` on a path that proves someness. It does not
  admit option-typed parameters, option-valued class or record fields, trait or
  impl method option returns, Boolean arrays or `alloc_array<bool>`, record or
  nested option payloads, or Boolean generic arguments. These position fences
  are checked before execution as well as at the individual checker/VC
  boundaries.

  VCgen gives the feature its real Lean type, `Option Bool`. Sable program
  booleans are represented symbolically as propositions, so constructing
  `some(p)` uses an explicit `@decide p (Classical.propDecidable p)` term;
  extracting an option payload returns the proposition `o.value = true`.
  Neither direction silently treats a `Prop` as a `Bool`. The Rust interpreter
  and dynamic specification monitor carry the checked payload type inside an
  option value even when it is absent. Consequently the logical junk value is
  Lean's payload-specific `default` (`0` for integers and `false` for `Bool`),
  while executable unguarded access still traps.

  At the G1.1 checkpoint, the formal SVM and LLVM emitter remained separate
  fail-closed consumers and rejected Boolean options; carrying this exact
  feature through those boundaries was assigned to G1.2 and G1.3. G1.1's
  complete low-concurrency closure command was
  `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
  SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`. It
  passed 116/116 library tests; all 374 corpus subjects (80 verifies, 231
  must-fail, 45 dynamic, 18 dynamic-fail) in 409.31s; the focused `option_bool`
  verification at 21/21 obligations across six functions and its dynamic
  subject at 1/1; LLVM CLI 6/6; the exact `VerifiedProgram` interpreter↔Clang
  differential at `-O0` and `-O2` 1/1; and SVM differential 69/69. Randomized
  allocator, grind-budget, LSP, and documentation gates were green. G1.1 is closed.
- **The formal option value is recursive; the source-to-SVM boundary is not.**
  G1.2 changes the Lean machine value from an integer-specialized option to
  `Val.opt : Option Val`. Its relational rules and proved executable evaluator
  give `some`, `none`, `.is_some`, and `.value` payload-generic semantics.
  `some(e)` preserves any successfully evaluated machine value; an accessor on
  a value of the wrong outer shape reaches `undef`; and `.value` on `none`
  reaches `Trap.optionNone`. The renderer preserves the established integer
  wire observations (`opt none`, `opt some 7`) and adds compact Boolean ones
  (`opt some false`, `opt some true`). Direct Lean guards pin absence,
  `some(false)`, `some(true)`, extraction, both failure classes, and the old
  integer spelling independently of the rule/evaluator agreement theorem.

  That uniform formal representation is not permission for a recursive source
  aggregate. The Rust lowerer admits only the ordinary-function intersection
  already checked in G1.1: concrete integer/Boolean option returns and locals,
  contextual constructors, assignment and A-normal call-result transport, and
  ordinary accessors. It independently rejects option parameters and fields,
  trait option returns, record and nested payloads, residual or Boolean generic
  arguments, Boolean arrays, classes and method calls, and the audited extern
  ABI. Thus the formal core can grow without an unreviewed compiler path
  inheriting that generality. At the G1.2 checkpoint LLVM remained fail closed.

  The initial focused gate passed a one-job Lake build covering `SVM`,
  `SVMEval`, `SVMOptionTests`, the raw and UART suites, and the `Sable` package,
  plus the Rust↔Lean differential at 76/76. G1.2 is closed by the combined
  serial evidence below.
- **LLVM Boolean options are canonical internal values, not a public ABI.**
  G1.3 lowers only G1.1's ordinary-function `option<bool>` intersection to
  `%sable.option.bool = type { i8, i8 }`. Canonical `none` is all zero;
  `some(false)` and `some(true)` set the tag to one and carry payload zero or
  one. The value crosses internal returns and calls and lives in ordinary local
  slots across control flow. `.is_some` reads the tag; guarded `.value` reaches
  kind-8 `optionNone` on absence with exact zero metadata/payloads, and extracts
  the Boolean only on the success edge. No option parameter/entry/extern ABI,
  option field or trait method, class/method call, residual generic form, or
  non-Boolean option payload is accepted.

  The combined G1.2/G1.3 closure command was
  `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
  SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`. It
  passed 129/129 library tests; all 374 corpus subjects (80 verifies, 231
  must-fail, 45 dynamic, 18 dynamic-fail) in 414.80s; LLVM CLI 6/6, including
  the exact zero-metadata/zero-payload kind-8 trap followed by mandatory
  `llvm.trap`; the 1/1 exact-`VerifiedProgram` interpreter↔Clang differential,
  which loops over scalar, control-flow, arithmetic, and Boolean-option subjects
  at `-O0` and `-O2` and observes 42 from the option subject; and SVM
  differential 76/76. Randomized allocator, grind-budget, LSP, and
  documentation gates were green. G1.2 and G1.3 are closed.
- **Module visibility follows the referenced namespace.** The loader keeps one
  flat runtime namespace for functions, classes, and records, and distinct
  trait and constant namespaces. Restrictive `use m::{...}` filters names across
  those categories (including `pub const`), while each actual reference checks
  visibility in its own category. The nominal walk covers recursive generic
  arguments and matches checked `Ty` exhaustively, so adding a type form cannot
  silently bypass visibility. A deterministic collision preflight runs before
  owner lookup and the flat merge. This is category-correct v1 linking, not the
  later per-module namespaces and backend mangling.
- **G0 is closed by the full serial gate, not parser tests alone.** With one
  Cargo job, one Sable test job, one Lean job, and one Rust test thread, the
  final checkpoint passed 82/82 library tests, all 368 corpus subjects in
  424.42s, LLVM CLI 6/6, the exact verified-program interpreter↔Clang
  differential at `-O0` and `-O2`, and SVM differential 69/69.
- **Verbatim splice.** Contract clauses appear in generated Lean exactly as written (module call-site substitution of parameter names by argument expressions). Generated theorems bind program variables under their source names so clauses elaborate unchanged. If a clause doesn't elaborate, the error must point at the `.sable` clause, not at generated code.
- **Every obligation and every hypothesis is named by content.** Hypothesis names are content-anchored slugs (`h_pre_sorted_a`, `h_inv_<slug>`, `h_path_<slug>`, `h_<callee>_post_<slug>`, `h_cinv_<slug>`; same-slug collisions get `_2` suffixes rather than shadowing) — discharge scripts survive unrelated edits. Obligation names are `fn.kind.<expression-slug>`, or `fn.kind.<label>` where the clause carries `#[label(name)]` (stable semantic names; hypotheses become `h_inv_<label>` etc.). Lean theorem names are sanitized versions; user-facing names live in the source map.
- **Class structures are emitted under mangled names** (`SableC_<name>`) so user class names can never collide with Lean root-namespace names (`class Nat` vs core `Nat`). Clauses never name the class — only values — so the verbatim-splice invariant is untouched; the prefix appears only in compiler-built binder types and `.mk` literals.
- **Binders carry source names.** A call/alloc/ctor result bound to a local binds under the local's name (`u64 p = probe_step(...)` → binder `p`, hypothesis `h_p_range`), not a positional `_r16`; a `&mut` method call rebinds the receiver's name (`m_2`); the mid-loop self state is `_self_loop`. Same motivation as content-anchored hypotheses: discharge scripts must survive unrelated edits.
- **Havoc is SSA-style versioning.** At a loop head, binders holding havocked names are renamed to stale versions (`_oldN_x`) and surviving hypotheses are *rewritten* to the stale names under `h_stale_*` — facts about pre-loop values (e.g. alloc facts) stay available instead of being dropped; fresh loop-invariant hypotheses keep the content-anchored names. Mutation discovery is exhaustive over the condition and body, including nested statement operands, `unsafe`/`expose`, ordinary and trait calls, and sealed raw/resource/device operations. Affine shape and the variant are captured before the condition; a false condition exits with its post-condition state, while a taken iteration proves decrease from that head value to the post-body value. Mid-method `self` havoc keeps *only* the loop invariants (the class invariant is not in force mid-method, design §7): a self-mutating loop states its full working payload — lengths, element facts, and a frame invariant against `old self` — as loop invariants. Record-field projections through update chains are reduced at generation time (`{ x with vals := v }.occ` → `x.occ`), so goals stay over stable atoms omega can use.
- **The machine has a raw heap, and every safe rule preserves it unchanged** (ADR 0025). `lean/Sable/SVM.lean`'s configuration carries a `RawHeap` — fresh-provenance counter plus allocations of `RawByte` where uninitialized is a distinct state — and `Val.ptr alloc off` is provenance plus an offset, never an address. Pointer arithmetic is an *expression* because it is pure; everything that touches the heap is an A-normalized *statement*, which is why `Eval` needed no change at all. Rule side conditions are decidable (`loadByte`, `freeable`, `inBounds`), since they are what the machine must compute to tell a store from `undef`. Invalid raw operations reach `undef`; exhausting the cap is `Trap.oom`. `lean/Sable/SVMRawTests.lean` pins the outcomes as `#guard`s — a second layer under the agreement proofs, because a rule and evaluator changed together consistently can be wrong and still agree.
- **Typed storage is abstract before it is representational** (ADRs 0031–0032). The first complete slice is `PointsTo<u64>`: raw authority over one canonical `u64.layout` converts into an uninitialized typed cell, whose state moves through init/read/take/drop, and converts back only when empty. `Layout` is compiler-established proof vocabulary (positive size, nonzero power-of-two alignment), visible as `T.layout` in generic clauses but never forgeable as a program value. The typed value is never decoded from or serialized into bytes; conversion back explicitly zero-fills as cleanup. Both executable heaps tag typed extents and reject byte access while the tag exists, while Lean VCs see only `PointsToView Int`. The SVM relational rules and evaluator agreement cover all six instructions, and differential subjects compare them with the interpreter.
- **The first root source is program-lifetime and intentionally leaking** (ADR 0033). `unsafe static_alloc(N) as (p, resource mem);` atomically creates fresh provenance and one full uninitialized `RawSpan`; its positive literal size is bounded by the execution profile. The pointer and affine resource are ordinary enclosing-function bindings, not loan-branded exposure locals. No deallocation authority exists, so the allocation stays live and abandoning the token is the affine leak this rung permits. VCgen binds `SpanView.uninit`, the interpreter retains the live allocation, and SVM lowering uses the existing fresh allocation instruction.
- **Releasable roots have sealed mandatory authority** (ADR 0036).
  `unsafe system_alloc(N) as (p, resource mem, resource release);` adds one
  `SystemDealloc` tied by view to the fresh allocation. It follows verified
  ownership transfers but cannot cross an extern boundary. Only
  `unsafe system_dealloc(p, mem, release);` terminates it, after a VC proves
  `p` is the base and `mem` is the complete matching raw extent; lowering is
  the SVM's `rawFree`.
- **A destructor owns the value outright** (ADR 0029). `deinit` bodies run; the class invariant holds on *entry* and is not re-established, so a destructor owes no `inv_exit` and has no `_old_self`. It may move fields out — the *field* is the place that dies, and untouched siblings stay readable — and a moved field is not dropped again. The interpreter's order within a drop is **invariant → body → remaining fields in reverse declaration order**. Classes hold resource fields; `#[must_consume]` turns an abandoned one from a permitted leak into a diagnostic. `&mut self.f` is legal in a destructor and nowhere else, because the invariant it could break no longer has to hold.
- **A move is one operation, and every sink performs it** (ADR 0030). A declaration, an assignment, a field assignment, a call/constructor/method argument and a return all *take* a value: the source place stops holding it, and whatever the destination held is destroyed. The interpreter has one `take_place`/`drop_place` behind `eval_moved` — overwriting a place runs a full drop (invariant → destructor → remaining fields), a returned local leaves with the caller rather than being destroyed behind it, and an owned parameter dies with the callee's frame after its contract has been checked. The checker has one `transfer` at the matching sinks: it kills the source place, applies the loan-brand rule (recursively, so `raw_offset(p, 1)` cannot launder what `p` may not), and reports whether a `#[must_consume]` obligation travelled with the value. Affinity covers class values, resources, **and owned arrays** — two names reaching the same elements is unsound the same way, and the diagnostic names the category (`class`/`resource`/`array` prefixes on `use_after_move` and `loop_shape`). A member may move a field out but must restore it before it exits (`class.field_not_restored`); only a `deinit` may leave a hole, because only there is the invariant already gone. A contract still reads a moved-from parameter's entry value: a value outlives the transfer of authority over it. Branch joins and loop checks operate over the whole per-place state (`PlaceState`: initialized, branded, obligation) rather than a chosen subset: branches join initialization by AND and brand/obligation by OR over reaching paths, while a loop requires its backedge to preserve affine liveness, brands, and obligations before restoring the zero-iteration entry state. Every `Place` maps to that state by its complete rendered key (`self.f`, not merely `self`). The `#[must_consume]` obligation is a *state of the place*: moving the token clears it, landing sets it, a marked field regains it on assignment, and a live one may not be assigned over. Two corollaries about *where* a value dies: a discarded class-valued result is a temporary with no place, destroyed at the end of its statement, and **`unsafe { ... }` is a marker while an exposure body is a scope** — the block grants vocabulary and has no lifetime (its locals belong to the enclosing function, and the interpreter runs it through `exec_open_block`), while an exposure *is* a lifetime, so the loan's bindings and everything the body declared end at its closing brace. Scope exit rejects a disappearing local that still holds a must-consume token.
- **Non-memory resources, and an explicit world** (ADR 0028). `resource OpenFile` is the authority to use one descriptor (position in the view, as POSIX has it); `resource PosixWorld` is the outside, and any foreign operation touching global state must receive it explicitly — which is what replaces a `modifies` clause over the universe, and lets a caller see from a signature whether a function can reach outside. Authority for a descriptor is carved from the world (`open_file(&mut w, fd)`) with *availability* as a precondition — open, and not already handed out — and carving **spends** it (`PosixWorldView.claimed`, updated functionally as `w.claim fd`), since affinity governs a token that exists and would not stop a second being minted beside it (ADR 0030). The checker tracks tokens, the VCs track the state of the outside. `posix_world(script)` is confined to `test_` functions — the one place authority appears from nothing — and the script is how a test author controls short reads and I/O errors, which the *view* deliberately does not model because no contract can predict them.
- **Foreign contracts are audited, and the build says so** (ADR 0027). `extern "C" #[audit(id := ..., reason := ...)] fn f(...);` owes no obligations — there is no body to check — but its clauses still get well-formedness defs, and the audit metadata is mandatory. Effects are structural: only a passed `resource &mut R` may change, so there is no `modifies` clause in the language. Resource erasure at this boundary is governed by an explicit ABI whitelist (`RawSpan`, `OpenFile`, and `PosixWorld`), not a permissive “all resources erase” rule; sealed allocator authorities and profile capabilities such as `Uart` cannot cross an extern. **Nonescape sits on the audited side of the boundary**: that a callee unable to *return* storage cannot retain it is compiler-checked for a verified callee (no globals, so the pointer dies with the frame) and an audited promise for a foreign one, since nothing stops C stashing it in a foreign global — part of what the audit id covers (ADR 0030). The trust manifest is emitted **into** the hashed Lean content, so changing an audit id invalidates an artifact exactly as changing a proof does (ADR 0018's hash is over bytes); importers inherit it through the flat merge. Status reads `verified relative to audited boundary`, never `fully verified`, whenever an extern assumption remains. `sable test` supplies deterministic shims keyed on the *audit id*; an unknown id traps rather than running the empty body.
- **A safe `[u8]` reaches raw memory through a lexical construct, not a proof** (ADR 0026). `unsafe expose &a / &mut a as (p, resource m) { ... }` lends the array's bytes for the body and takes them back: entry binds a span whose bytes are the array's elements, exit makes the array what the bytes say, under generated obligations (the whole extent came back; every byte is present and in `u8` range). Hidden *loan brands* do nonescape with no lifetime syntax — branded values cannot be returned, assigned outside the body, or passed to a user function — and the brand follows provenance through `raw_offset`/`split_off`/`join` but not onto loaded bytes. Raw operations pair a pointer with a resource borrow (`Ty::Raw`, `Val::Ptr`, `SpanView.namesByte`) and live inside `unsafe`; `unsafe regions: N` is reported in build output. `raw_copy_nonoverlapping` carries **no nonoverlap premise**: two distinct affine tokens *are* separation.
- **A resource is authority, and only its *view* reaches Lean.** `resource RawSpan` / `resource &RawSpan` / `resource &mut RawSpan` are affine in the checker and erased from runtime signatures; vcgen binds a `Sable.SpanView` and nothing else, so no generated VC mentions a heap, a capability, or disjointness (ADR 0022/0024). The split is enforced by the two languages disagreeing: a clause may read `s.len`, program code may not (`resource.view_is_ghost`) — a program that could read the view would need it at runtime, and a runtime view is forgeable. `resource &mut R` reuses the `&mut` array machinery: entry state as the binder, current state in the env, `old s` resolving to the binder. U10 closed the stale-view cases in nested operations and effectful loop conditions and restored the pre-condition affine-shape rule. The correction exposed every free-list search proof that had depended on stale state; `free_list_walk_unchanged` now states the `state = old state` frame and restored chain, while insert-location and first-fit transport their current stored-chain facts through it. Serial checks are green for 33/33 obligations across the walk helper/caller, 13/13 across the insert-location pair, and 22/22 across the first-fit pair; the complete corpus is green as well.
- **Aggregate authority is one affine map token, not a source-level heap assertion** (ADR 0053). `ResourceMapView<K,V>` is a pure partial map; hidden context validity owns the pairwise-separated composition of its entries. Sealed `resource_map_take` and `resource_map_put` move one exact resource between an entry and an ordinary affine place, with presence/absence as the only visible VCs. The first compiler instance is `ResourceMap<u64, PointsTo<u64>>`: its verified three-function round trip proves pointer/value preservation through contracted calls and exact root release. The interpreter keeps a key-only sanitizer shadow to catch invalid unverified tests, including across Sable calls; the machine and ABI still receive no aggregate authority value.
- **Raw-storable records are explicit POD values, not restricted classes** (ADRs 0054–0056). A declaration fixes positive size and power-of-two alignment; the outer alignment must be a multiple of each field alignment, and field offsets must be aligned, in bounds, and pairwise disjoint. This makes the aligned-base guarantee sufficient for every field address. The initial fields are fixed integers, typed raw pointers, and nullable typed raw pointers; none receives a byte encoding. `PointsTo<Record>` carries an abstract record-tagged cell state, and occupied extents exclude byte access. The U9 acceptance subject stores two real intrusive nodes in one arena and relates their runtime links to an abstract sequence over `ResourceMap<u64, PointsTo<IntrusiveNode>>`; take/put is the only visible permission movement, and teardown reconstructs the exact releasable root. The formal SVM mirrors this with tagged abstract values and cells plus per-byte extent ownership, preserving evaluator/rule agreement while excluding byte and `u64` overlap. Cross-allocation pointer comparison remains outside the rule actually exercised.
- **A device is a profile capability, not a volatile heap cell** (ADR 0057). The first slice is `uart-poll-v1`: an affine `resource Uart`, test-only construction through `test_uart`, and checked `unsafe` intrinsics `uart_status`/`uart_write`. The signature-level authority budget is one: a function, method, initializer, or generic template may declare zero or one explicit `Uart` parameter, never two. A second is rejected because the executable profile has one UART0 while two proof views would falsely appear independent; zero permits ordinary non-device code and lets tests mint their one local scripted authority. Owned or borrowed `Uart` resource fields are also rejected, including in generic classes, until device identities and functional field write-back exist. Trait calls obey the ordinary overlapping-borrow rule, and UART-bearing trait signatures are rejected until abstract trait contracts can carry resource state. A status read consumes one oracle value, advances the cursor, appends an ordered read event, and establishes readiness; a write requires that readiness, appends the byte, and clears it. `lean/Sable/SVMUart.lean` wraps rather than widens the core SVM, so an unselected/bare execution retains the core machine's exact rendering while a selected execution carries the profile state and observations. The emitted profile id and used intrinsics are paired with a content hash over the recursive local Lean import closure, `lean-toolchain`, and `lakefile.toml`. This is a declared, kernel-checked machine dependency and does not change `fully verified` into `verified relative to audited boundary`.
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

Profile-only constructors follow the same confinement rule. For
`uart-poll-v1`, `test_uart(0)` is immediately ready, `test_uart(1)` becomes
ready on its third status read, and every other script stays not-ready. The
interpreter advances the oracle cursor and records the same ordered status-read
and transmit-write events as the formal profile. Resource-view clauses such as
the `writes` projection remain proof-only and are explicitly fenced when a
dynamic test imports the verified driver.

Erasure removes resource values, not expression evaluation. Resource-valued
arguments and transformation operands execute left-to-right before their
proof-only result is discarded; passing `test_uart(0)` directly to an erased
parameter therefore selects the profile before the callee runs. Loop variants
use the verifier's same transition: sample at the head before the condition,
then compare after every taken body, including the final iteration.

## The SVM differential oracle

The core machine semantics (`lean/Sable/SVM.lean`, design §10) is executable:
`lean/Sable/SVMEval.lean` defines a functional evaluator/stepper proven to
agree with the inductive rules in both directions — determinism, totality,
and progress are kernel-checked corollaries. Profile-specific semantics compose
around that core: `lean/Sable/SVMUart.lean` delegates every non-UART statement
and adds the `uart-poll-v1` oracle/readiness/trace transitions, with its own
two-directional agreement, determinism, and progress results. A bare wrapper
run renders byte-for-byte like the old core outcome; a selected run extends the
canonical observation with profile id, oracle cursor, and ordered MMIO trace.

Ordinary options occupy one recursive value form, `Val.opt : Option Val`, in
both presentations. Generic machine constructors and accessors preserve the
payload value, while outer-shape confusion is `undef` and extracting absence is
`Trap.optionNone`. Nullable raw-pointer options remain a distinct value form,
so an accessor cannot cross the ordinary/raw option boundary accidentally.

The harness (`compiler/tests/svm_diff.rs`, ADR 0017) lowers every function in
`corpus/svm-diff/` to Lean terms (`compiler/src/svm.rs`), runs each on both
`interp.rs` and the appropriate Lean evaluator, and compares those canonical
observations exactly — a divergence is a bug in one of two artifacts that are
otherwise trusted independently. Lowering is strict: a subject outside the
machine's supported subset is a hard failure, never a skip. `test_uart`
selection remains a machine statement through explicit and inferred
declarations, assignment, and discard. Authority-only resource operations erase
only when every operand is syntactically runtime-inert; a potentially trapping
or effectful operand is rejected instead of silently dropped. The one-worker
differential run currently covers 76/76 subjects, including Boolean option
absence/presence, local assignment, accessor results, and A-normal call
transport, plus UART success, budget exhaustion, readiness clearing, ordered
traces, invalid writes, profile reselection (including its precedence over
script-expression traps), and all three selection contexts.

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
.sable-out/        immutable roots, module artifacts, proof-env source/build
                   snapshots, and daemon socket (gitignored)
```

## Toolchain pins

Lean is pinned by `lean/lean-toolchain` (elan resolves it). Upgrades are deliberate, tested against the corpus, and get a commit of their own. Rust: whatever stable cargo is current; no nightly features.
