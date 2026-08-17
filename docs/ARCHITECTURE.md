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
  │                                   one recursive type grammar for every position;
  │                                   admissibility is decided after parsing by the
  │                                   (shape × position) table `Parser::admits` (ADR 0063);
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
  │                                   carry explicit Ty::Param values into
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
  │                                   G1.4a uses the same explicit Prop→Bool bridge
  │                                   for ordinary Boolean call arguments and carries
  │                                   nominal POD values across ordinary calls;
  │                                   G1.4b models owned-local Boolean arrays as
  │                                   `Sable.Seq Bool`: writes cross Prop→Bool and
  │                                   reads cross back through `get ... = true`;
  │                                   G1.5 gives the formal SVM a separate tagged
  │                                   `Seq Int`/`Seq Bool` array value while keeping
  │                                   the Rust source bridge owned-local-only;
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

## Native lowering boundary (through the closed N5 `Integer` closure)

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

The validation boundary stays narrower than the IR type: an `option<bool>`
parameter now crosses an internal call as the same by-value aggregate a
return or local uses (still no source or C ABI — the layout and the `ob`
mangling component stay versionable), while no option entry or extern ABI
exists; option-valued fields and trait methods, classes/method calls,
residual generic forms, and every non-Boolean option payload remain rejected.
The combined closure evidence appears with G1.2/G1.3 below.

G1.4a adds a second internal aggregate family: each supported root-owned POD
declaration with integer fields becomes a named LLVM aggregate. Construction,
projection, locals, branches, direct internal parameters, calls, and returns
transport that semantic value. The LLVM type intentionally ignores the
record's explicit `#[layout]` and field offsets: those declarations describe
raw-cell geometry in the abstract storage model, not the layout of an ordinary
LLVM SSA value. Imported records, extern/entry/public ABIs, pointer and Boolean
fields, nested and container records, and classes remain rejected. The named
aggregate is versionable internal lowering, not a record ABI.

At the G1.4b checkpoint the native boundary remained closed: source checking,
VC generation, interpretation, and monitoring admitted owned-local Boolean
arrays without choosing LLVM storage or lifetime. G1.5 then added a tagged
formal-SVM value and the matching local-only Rust bridge, still without native
lowering. Those historical fences matter because G1.6 widens only the same
intersection rather than treating the formal representation as an array ABI.

G1.6 uses `%sable.array.bool = type { ptr, i64 }` for an internal local
descriptor: opaque data pointer, then `u64` length. Elements are canonical
zero/one `i8` bytes rather than packed `i1` values. Nonempty storage is obtained
and released only through the external versioned declarations
`__sable_rt_array_alloc_v1(i64 bytes)` and
`__sable_rt_array_free_v1(ptr)`; zero length uses a null pointer and bypasses
both hooks. The checked type, not the pointer, retains the Boolean payload tag.
The optional hosted C shim in `runtime/hosted/sable_rt_v1.c` implements the
fixed-width boundary with the platform allocator after a `size_t` fit check;
the emitter itself remains target-neutral and never names `malloc` or `free`.

The native ordering is part of the semantics. Allocation evaluates length and
initializer before the 50,000,000-element cap and hook result; a literal
evaluates every element left-to-right before allocation and ordered writes.
Store evaluates index then value, guards with an unsigned comparison, and only
then forms a non-`inbounds` address; a read likewise guards before address and
load. Cap exhaustion and a null allocation result reach trap kind 9 with
`type_info = 0`, `lhs = len`, `rhs = 0`. Out-of-bounds reads and writes reach
kind 10 with `type_info = 0`, `lhs = index`, `rhs = len`. The observer is still
followed by mandatory `llvm.trap`.

Owned-array destruction follows source lifetimes. Function bodies, `if` arms,
and each `while` iteration are cleanup scopes, with reverse declaration order
on normal fallthrough and before a loop backedge. Returns evaluate their value
first and then unwind inner-to-outer. `unsafe` remains an open marker, so its
declarations belong to the enclosing scope; a trap runs no cleanup. At that
checkpoint parameters, returns, fields, borrows, exposure, rebinding or
movement, calls, extern/public positions, generic or option containment,
discarded temporaries, and integer arrays were each rejected independently;
`u32` arrays are opened by N0 below and borrowed Boolean arrays by ADR 0070,
and the rest still are. This is internal lowering, not a public,
foreign, or cross-module array ABI.

## Key invariants

- **One type grammar, one gate table** (ADR 0063). The parser has a single
  recursive type production — nominal records and classes, integers, `bool`,
  type parameters, `[T]`, `option<T>`, `raw<T>`, resource kinds, and the `&T` /
  `&mut T` borrow forms — and every declared type goes through one parse
  (`parse_type_syntax_at`) and one lowering (`Parser::lower_type(syntax, pos)`).
  Two projections sit on top of that pair: `Parser::ty` yields `Ty`, and
  `Parser::int_ty` yields `IntTy` for `const`, `widen`/`narrow`, and
  `impl ... for`. The element of `alloc_array<T>` is no longer a third
  projection — it is `Parser::ty(TyPos::ArrayElement)`, a full `Ty` like every
  other position, because container payloads are full types (ADR 0064). A
  nested position narrows the same way without a second parse — a `ResourceMap`
  key reaches `lower_int_ty` from the syntax its resource kind already parsed.

  Where a shape may be written is decided *after* parsing, by
  `Parser::admits(shape, position)`: one match, readable as a table, keyed by
  the shape of the type and the position it was written in. A position that
  admits a shape is not promising the program checks; several positions admit a
  shape deliberately so a downstream rule (record layout, aggregate payloads,
  the affine-option boundary) owns the rejection and can say more about it than
  a grammar could. What stays in the table are the rejections where admitting
  the shape would commit the compiler to semantics it does not have. That set is
  the match in `Parser::admits`, which this document deliberately does not copy:
  the table is the enumeration.

  Since ADR 0064 the representation is no longer a reason to be in that table
  for any position that lowers to a plain `Ty`: `Ty` holds any shape in any
  container payload, so those rows are decisions about the language rather than
  reports about a data structure. For `ArrayElement` and `OptionPayload` the
  table's refusal now duplicates a stage gate that refuses the same shape under
  the same name — `TyPos::gate_name()` supplies the name to both — so an
  `expect-error` fence cannot say which one a subject reached.
  `docs/shape-admission.md` is where the gates' own answers are visible, and
  ADR 0064 records which rule each of the container `corpus/must-fail` subjects
  actually pins. That table is generated by handing every shape to every
  consuming stage without the parser in the way: each stage's payload gate, its
  position gates, and its type traversals, including the LLVM backend's, so a
  refusal a source program cannot currently reach is still watched.

  Borrow and resource prefixes are a separate production from the recursive
  core, so they never reach `Parser::admits` from a nested position at all and
  `[&T]` is a parse error rather than a gate rejection. That is a grammar
  decision now, not a consequence of what `Ty` can hold.

  The table decides shapes and nothing else, and says so: which spellings of an
  admitted shape exist (`raw<u8>` and `raw<Record>` in `lower_raw_type`, the
  sealed resource kinds in `lower_res_kind`) is decided by the lowering routine
  for that shape, and what a position demands beyond a spelling
  (`local_needs_initializer`, the checker's payload, ownership, and layout
  gates) is decided outside the parser. The option families are the sharpest
  case: `option<[T]>` and `option<raw<R>>` are gated by the `OptionPayload` row
  like any other payload — `lower_option_type` consults it for both — and
  `option<raw<R>>`, one abstract nullable pointer value rather than an option
  over a pointer, is the only payload whose syntax the lowering still reads to
  pick a constructor (`Ty::OptionRaw`). Every other payload becomes itself
  under `Ty::Option`, and whether the result owns is read off that payload
  afterwards (ADR 0065), not from the table.
  `admitted_shapes_match_their_lowering` pins that a position admits only the
  shapes its lowering has a representation for, so a spelling the table admits
  can never reach an unhandled case. Since ADR 0064 that constraint has force
  only where the lowering narrows to something other than `Ty` — `lower_int_ty`,
  `lower_raw_type`, and `lower_res_kind`. For every position that lowers to a
  plain `Ty` the row would restate the table it is checking; what a container
  payload may be is decided by the checker's payload gates and pinned by
  `docs/shape-admission.md`. `BorrowParam` is in that second group since ADR
  0067: `Ty::Borrow` holds every referent, so which referents a borrow may name
  is a rule — stated by the `BorrowParam` row and again by
  `check::parameter_ty`, both under `type.borrow_param_unsupported`.

- **One borrow constructor; ownership is structural** (ADR 0067). `&T` and
  `&mut T` are `Ty::Borrow(Mutability, Box<Ty>)` for every referent, and a bare
  type owns. No constructor carries both a shape and a binding mode: `Ty::Array`
  holds only its element, and `resource &K` is a borrow of `Ty::Res(K)` that
  keeps its own syntactic shape because the spelling puts the marker after the
  keyword. `Mutability` has two cases, `Shared` and `Mut`, because owning is the
  absence of a borrow; a rule that needs the three-way answer asks
  `Ty::binding_mode()`, which computes it.

  `Ty::is_affine` is then structural: a class, a resource, and an array own, an
  option owns exactly when its payload does, and `Ty::Borrow` is a **terminal**
  `false` — never `referent.is_affine()`, which would move a borrow's place into
  the moved set and hand the runtime's owned-storage cleanup the caller's
  buffer. `interp::drop_owned_params` matches the bare constructors for the same
  reason: a borrow's runtime value is the same `Rc` the caller holds, so
  `Ty::Borrow` being a separate constructor is what makes the double free
  unwritable rather than merely unwritten.

  Three named accessors carry what used to be pattern-matching on a constructor:
  `Ty::binding_mode` (owned / shared / unique), `Ty::as_unique_borrow` (the one
  question the `old` snapshots, the loop havoc, and the call-site havoc all
  ask), and `Ty::referent` (what a borrow names, for the stages whose answer
  does not depend on binding mode — `lean_ty` is one, so `&[T]`, `&mut [T]`, and
  `[T]` are all one `Sable.Seq T`). The LLVM *IR type* is blind to mutability
  too; the mangled symbol is not, and `type_code` is where that lives.

- **Generic widening starts fail closed.** G0 is complete as a representation,
  parser, identity, and rejection foundation. `GenericTy` and its opaque
  canonical key recurse over integers, `bool`, parameters, records, classes,
  arrays, and options. Each call or constructor `TypeArg` retains the span of
  its complete outer type. One bounded parser drives lookahead, use-site
  arguments, and every declared type: a recursive path is at most 64 nodes, any
  argument list at most 256 entries, and one type at most 4096 nodes. Imported
  generic-class arities live in a table separate from checked class indices. None of that
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
  `Ty::Param(TypeParamId)`. It no longer makes a parameter look
  intrinsically integer-valued merely because ADR 0009's current proof model
  is integer-only. Array and option payloads are full `Ty` values
  (ADR 0064): which of them a stage gives semantics to is that stage's named
  gate to state, not something the representation decides.
  Before substitution, mono checks every declaration-position
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
  visibility also descended into container payloads — `modules::walk_ty`
  recurses into every container payload and matches exhaustively — so a
  nominal payload
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
  the type, `.is_some`, and `.value` on a path that proves someness. The
  checker and VC generation have since widened one position: an
  `option<u64>`-family or `option<bool>` *parameter* crosses the call boundary
  by value, binding `Option Int` / `Option Bool` with an integer payload's
  range fact over `.value` (the absent case reads `getD default = 0`, in range
  for every integer type). The interpreter executes the position and the
  monitor checks its contracts at the call boundary; SVM lowering transports it
  as an ordinary `Arg.byValue` machine value (the untyped `Val.opt` already
  crosses `call`/`ret`, so no rule, evaluator, or agreement-proof change was
  needed) with `corpus/svm-diff/option_params.sable` pinning some/none
  transport, forwarding, round trips, and the absent-`.value` trap in both
  payload families; the native backend lowers the `option<bool>` parameter
  through the existing `%sable.option.bool` by-value aggregate (pinned against
  Clang at `-O0`/`-O2` by `corpus/llvm-diff/option_param.sable`), keeps
  refusing the integer-payload parameter under `backend.unsupported` — the
  type has no LLVM representation in any position — and a stored option field
  keeps `interp.option_position_unsupported`. Init and method
  parameters admit the same copyable option and `bool` shapes plain calls do
  (`check::member_param_ty`). Not admitted
  anywhere: option parameters with a type-parameter payload
  (`type.option_param`), trait-method option parameters
  (`type.trait_param_unsupported`), option-valued class or record fields,
  trait or impl
  method option returns, Boolean arrays or `alloc_array<bool>`, record or
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
  already checked in G1.1: concrete integer/Boolean option returns, parameters,
  and locals, contextual constructors, assignment and A-normal call-result
  transport, and ordinary accessors. It independently rejects option fields,
  trait option parameters and returns, record and nested payloads, residual or
  Boolean generic arguments, Boolean arrays, classes and method calls, and the
  audited extern ABI. Thus the formal core can grow without an unreviewed compiler path
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
- **Ordinary call transport is wider than class and public ABIs.** G1.4a lets
  ordinary calls consume Boolean arguments by explicitly reifying the
  proposition-valued symbolic expression to a Lean `Bool` at the formal call
  boundary. Ordinary POD record values may cross parameters and
  returns as well; returned records regain their nominal `wf` fact, and loop
  havoc preserves that nominal well-formedness rather than treating the value
  as an untyped tuple. The interpreter and dynamic contract monitor follow the
  same call transport. Class-method record returns and Boolean/record trait
  signatures remain independently rejected.

  LLVM admits only root-owned integer-field POD records as internal named
  aggregates. It lowers construction/projection, locals, branches, internal
  parameters, direct calls, and returns, but no imported record,
  extern/entry/public ABI, pointer or Boolean field, nested/container record,
  or class. Explicit raw layout and offset metadata do not determine this
  semantic aggregate representation. Consequently G1.4a is neither a stable
  record ABI nor true generic-class support.

  The complete one-worker closure passed `cargo check`; 150/150 library tests;
  all 382 corpus subjects (82 verifies, 235 must-fail, 47 dynamic, 18
  dynamic-fail) in 218.30s; focused Boolean-call verification at 16/16
  obligations across ten functions and record-call verification at 13/13
  across four functions, with each dynamic subject at 1/1; LLVM CLI 6/6; and the 1/1
  exact-`VerifiedProgram` interpreter↔Clang differential at `-O0` and `-O2`
  over five subjects including POD records. SVM differential stayed green at
  76/76; the SVM lowerer also hardened semantic operand, source-scope,
  sealed-op, record-geometry, and integer-array coherence at its public AST
  boundary, without admitting Boolean arrays. Randomized allocator,
  grind-budget, LSP, and documentation gates were green. G1.4a is closed.

- **Boolean arrays are owned-local proof/runtime values, not a transport or
  backend representation.** G1.4b admits fresh `[bool]` locals initialized by
  a contextual literal or `alloc_array<bool>(u64, bool)`, including empty
  arrays. Their supported operations are `.len`, checked index reads, element
  stores, loops, assertions, and contracts. The checker keeps Boolean-array
  returns, class/record fields, exposure, whole-array rebinding, Boolean `for`
  indices, and generic arguments closed; borrows and borrowed parameters are
  open under the separate rule below (ADR 0068).

  VC generation uses `Sable.Seq Bool`. Program Boolean expressions remain
  symbolic propositions: literals, allocation fills, and stores explicitly
  reify them to Lean `Bool`, while reads become propositions through
  `sequence.get index = true`. Owned-local loop havoc keeps the sequence type
  and preserves a usable length relation where sound, but adds no integer
  element-range facts. Bounds obligations are unchanged.

  Runtime arrays retain their payload domain even at length zero. The
  interpreter and dynamic monitor use separate integer and Boolean variants,
  support Boolean length/get/store and deep snapshots, and compare arrays only
  within a payload domain. Integer/Boolean cross-domain equality is
  unmonitorable rather than a coercion. Integer-only sequence helpers likewise
  do not reinterpret Boolean elements.

  At the G1.4b checkpoint the Rust SVM lowerer rejected the new local value and
  the formal SVM remained unchanged; LLVM independently rejected it as
  described above. G1.5 changed only that formal-machine boundary; G1.6 later
  supplied the independently reviewed native stage.

  G1.4b closed under `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0
  SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
  --test-threads=1 --nocapture`: 171/171 library tests; all 394 corpus subjects
  (83 verifies, 244 must-fail, 48 dynamic, 19 dynamic-fail), whose all-target
  corpus portion took 208.73s; focused verification at 18/18 obligations across
  four functions; 2/2 dynamic tests and the expected out-of-bounds trap; LLVM
  CLI 6/6; the exact-`VerifiedProgram` interpreter↔Clang differential 1/1 over
  five subjects at `-O0` and `-O2`; and SVM differential 76/76. A standalone
  corpus repeat was green in 195.71s. Randomized allocator, grind-budget, LSP,
  and documentation gates were green. G1.4b is closed.

- **The formal array value is tagged; the source bridge remains local**
  (ADR 0062). The formal array value is `Val.arr (elem : ValTag) (a : Seq Val)`:
  a payload tag beside ordinary machine values. The tag is retained at length zero.
  Relational rules and the proved evaluator give length, index, allocation, and
  store one implementation each, over the tag rather than over the payload,
  without permitting heterogeneous values; all evaluator-agreement,
  determinism, totality, and progress proofs remain theorem-backed. Canonical
  rendering stays `arr [...]`, spelling scalar elements bare.

  Store order is index evaluation, value evaluation and scalar-shape check,
  array lookup, payload-tag compatibility, then bounds. Consequently an
  integer write to an empty Boolean array is `undef`, while a Boolean write to
  the same empty array reaches `indexOOB`; a payload mismatch likewise beats an
  OOB trap at a nonempty array. Allocation evaluates length and initializer
  before negative-length/OOM geometry, so initializer traps retain precedence.
  Direct formal guards pin Boolean allocation/read/store/length, empty tags,
  OOB, OOM, invalid initializers, and these precedence cases.

  Rust lowering admits a Boolean array as a fresh owned-local declaration from
  `alloc_array<bool>` or a contextual literal, plus index/length/store uses,
  and — under the separate rule below (ADR 0069) — as a borrowed parameter and
  a borrow argument. What it refuses is the owner leaving its scope: returns,
  fields, exposure, whole-array movement, and other transport of the owner
  itself. A literal first evaluates its
  elements into reserved temporaries in source order, then allocates a
  false-filled Boolean array and emits ordered stores; an element trap
  therefore precedes allocation/OOM. Expansion is capped at 50,000,000
  elements, and even an empty literal allocates a Boolean-tagged empty value.
  At the G1.5 checkpoint LLVM remained fail closed.

  G1.5 closed under `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
  SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
  --test-threads=1 --nocapture`. `cargo check` and the full 22-target one-job
  Lake build were green; Rust library tests passed 175/175; all 394 corpus
  subjects (83 verifies, 244 must-fail, 48 tests, 19 test-fails) passed in
  266.78s; LLVM CLI passed 6/6 with Clang required; the exact
  `VerifiedProgram`↔Clang O0/O2 differential passed 1/1 over five subjects;
  and the SVM differential passed 86/86.
  `free_list_return_random`, grind-budget, LSP, and doc-tests were
  green. G1.5 is closed.
- **Native Boolean arrays add a lifetime, not a transport ABI.** G1.6 lowers
  only a fresh owned-local `[bool]` produced by `alloc_array<bool>` or a
  contextual literal. Its `{ ptr, i64 }` descriptor and `i8` element bytes are
  internal. Allocation/free cross the external versioned runtime hooks only
  for nonempty storage; zero length bypasses both. The 50,000,000-element cap
  and hook-null failure report kind 9 `(0, len, 0)`, while unsigned bounds
  failure reports kind 10 `(0, index, len)`. Guard dominance, canonical bytes,
  literal/operand order, and the absence of `inbounds` promises are structural
  emitter invariants.

  The compiler tracks successfully initialized array locals in a stack of
  lexical cleanup scopes. Function, branch-arm, and loop-body scopes destroy
  in reverse declaration order; returns preserve expression effects before
  unwinding all active scopes, and loop cleanup precedes the backedge. Unsafe
  blocks do not push a cleanup scope, and trap edges do not clean up. The
  interpreter uses the same boundary: dropping an array place removes its
  runtime binding, including branch and loop locals, while a trapped frame
  retains its places because unwinding is not language semantics.

  G1.6's complete low-concurrency command
  (`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
  SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
  --test-threads=1 --nocapture`) is green. So are `cargo check` and the
  standalone 22-target one-job Lake build. Rust library tests pass 185/185 and
  LLVM units 26/26; all 395 corpus subjects (83 verifies, 245 must-fail, 48
  tests, 19 test-fails) pass in 192.76s; LLVM CLI passes 7/7, including the
  strong-hook fixture at Clang `-O0`/`-O2`; the exact interpreter/native
  differential passes 1/1 over six subjects at both levels; and SVM remains
  86/86. Randomized allocator, grind-budget, LSP, documentation, diff-check,
  and static-audit gates are green. G1.6 is closed.
- **An owned Boolean array is a local value; a borrowed one is a borrowed
  array** (ADR 0068). `&[bool]` and `&mut [bool]` are ordinary parameters in
  the checker and in VC generation. Nothing in the array-parameter proof path
  was ever integer-specific — `lean_array_ty`, the parameter binder and its
  `_old_` twin, the loop-head and call-site havoc, and the element read/store
  bridges all read the payload, and `Sable.Seq` is polymorphic — so the change
  is which question each gate asks: `is_owned_array_of(&Ty::Bool)` where the
  rule is about an owner, and the borrow-transparent `is_array_of` where the
  rule is about a sequence. This is the same terminal distinction ADR 0067 put
  in `Ty::is_affine`.

  The parameter's well-formedness is the length fact
  `0 ≤ m.len ∧ m.len ≤ u64.max` and **no element fact**. That is an answer,
  not a gap: an integer array's element hypothesis says every element inhabits
  its width, and `Bool` is already its complete value domain, so the analogous
  proposition does not exist. Loop havoc leaves a shared borrow untouched (it
  is never a store target, which is what a shared borrow guarantees) and gives
  a unique borrow a fresh binder plus length preservation, justified by
  `Seq.len_set` exactly as for integers.

  `type.bool_array_param` and `type.bool_array_borrow` are deleted rather than
  narrowed, because the parser's `P::Param` row already refuses an owned array
  of every element type and a narrowed refusal would name a rule no source
  program can reach. `type.trait_param_unsupported` now covers an array in any
  binding mode: an abstract trait call substitutes integer arguments into the
  trait's contract, and a sequence is not one.

  The interpreter and the dynamic monitor run one too, and needed no new
  execution code. `RtArray` carries its payload tag beside its values, so
  length, an index read, and an element store are one implementation over the
  tag; `ExprKind::Borrow` clones the `Rc`, so a `&mut [bool]` argument *is* the
  caller's storage and the callee's writes need no write-back; and
  `drop_owned_params` matches the bare constructors, so a lent array dies with
  its owner. The monitor snapshots a unique borrow at entry for `old p`, and
  that snapshot is payload-carrying, with `false` as the Boolean junk value
  Lean's `default` supplies — so a borrowed Boolean array's clauses are
  monitorable at zero skips.

  The native slice is the rule below.

- **A lending argument is the machine's unique borrow** (ADR 0069). A formal
  SVM call argument is `Arg.byValue e` or `Arg.lend x`. Both supply the same
  entry value — `Arg.toExpr` maps a lending to reading the local it names, so
  evaluation order, the ⊥-read, and argument traps are exactly what they were.
  What lending adds is where the value goes back: `Arg.loans` pairs each lent
  argument with the parameter that receives it, `call_enter` records that list
  in the `Frame`, and both ways of leaving a body — `ret_pop` and `nil_pop` —
  apply `Env.restore` before binding the destination.

  Copying in and copying out is faithful because a unique borrow is exclusive:
  the checker rejects any second name reaching that storage while the callee
  runs, and the machine has no concurrency, so nothing can distinguish a cell
  written through from one restored at the pop. A shared borrow therefore needs
  no constructor at all — its promise is that the callee does not write, and a
  value is that promise. `Val` is unchanged: a borrow is an argument form, not
  a machine value, and `Expr` still cannot produce one.

  Because the write-back is a total function both the rules and the evaluator
  name, the two-directional agreement theorem moved arm-for-arm rather than
  gaining a case. `lower_fn_entry` admits a borrowed array parameter of any
  payload, and `lower_arg` decides the argument form from the argument's type
  rather than its syntax, so a `&mut` reborrow passed on by name still lends.
  `corpus/svm-diff/bool_array_borrows.sable` is where the two executables are
  compared on it.
- **A native borrow lends the descriptor** (ADR 0070). `llvm_ty` answers
  `%sable.array.bool` for `[bool]`, `&[bool]`, and `&mut [bool]` alike: a
  borrow is a second name for storage, not a second shape of it, so the
  emitter gained no type, no runtime hook, no trap kind, and no element
  encoding. The split that makes it safe is ADR 0068's, applied here —
  `is_owned_bool_array` decides ownership (which declarations allocate, enter
  the lexical cleanup registry, and call `__sable_rt_array_free_v1`) and the
  borrow-transparent `is_bool_array` decides representation (the IR type, the
  descriptor loads, element addressing, the index and length bases). A
  borrowed parameter never enters a cleanup scope.

  A borrowed descriptor is passed by value, and the copy the callee stores
  holds the caller's data pointer, so a write through a `&mut` parameter lands
  in the caller's bytes during the call and nothing is copied back. That is
  deliberately not the formal machine's mechanism: ADR 0069 records a loan and
  restores it at the pop. Both are faithful because a unique borrow is
  exclusive, and `corpus/llvm-diff/bool_array_borrows.sable` compares the
  interpreter's outcome with Clang `-O0` and `-O2` rather than assuming the
  two agree. The callee cannot change the length or the allocation, because
  the descriptor is a value and reallocation is not in the borrowed surface.

  The argument rule is N0's: the checked argument must be the exact explicit
  named borrow with matching mutability, a `&mut` may not be taken through a
  non-mutable place, and overlapping mutable aliases in one call stay
  rejected. A reborrow of a borrowed parameter is admitted. The store rule
  asks for the exclusive right to the storage, which a `mut` owner and a
  unique borrow have and a shared borrow does not. The mangled component is
  `a` + the element's code + `s`/`m` — `abs`, `abm` beside `au32s`, `au32m` —
  internal and versionable like the named type. Owned array parameters and
  returns, entries, fields, classes, externs, other element widths, whole-array
  transport, exposure, and container containment remain refused.

- **A backend lowering answers rather than aborts** (ADR 0071). `llvm_ty` and
  `type_code` are total: every `Ty` gets an `Option<String>`, and `None`
  becomes a spanned `internal.backend.type_lowering` diagnostic naming the
  shape and the declaration it was written on. They are still not gates — the
  `require_*` gates refuse first, under `backend.*` names a source program can
  match — so that diagnostic reports a gate and a lowering disagreeing, which
  is a compiler bug and is `internal.`-namespaced for that reason.
  `llvm_lowering_is_total_on_admitted_shapes` still checks the implication the
  arrangement wants, admitted implies lowerable; what changed is that its
  failure mode is a bad diagnostic instead of a process abort with no name and
  no span. `IntTy::bits`/`min`/`max` and `integer_type_code` keep their own
  post-monomorphization contract, enforced by `require_concrete_integer`.

- **A borrow is not a local binding** (ADR 0072). VC generation's symbolic
  environment is keyed by *source name*, and every rule that touches storage —
  the store write-back, the call-site and loop-head havoc, the `old p` entry
  states, the checker's ownership `Place`s — is written against that key. The
  model is correct exactly when each name is the only name for its storage,
  which is what a `&mut` parameter is inside its callee. `var view = &mut a;`
  broke that premise: the borrow expression evaluated to a *snapshot* of the
  owner's term and the declaration filed it under a second key, so a store
  through either name moved only that entry and both names stayed believed.

  `check::local_ty` refuses a local whose type is not owned, under
  `type.borrow_local_unsupported`, at the initializer's span. The test is
  `Ty::binding_mode()` and nothing else, so it holds for an array of any
  payload, a class, a class field, a resource, an option, a raw pointer, and a
  bare name that already holds a borrow (`var d = c;`) — the same
  read-it-off-the-binding-mode shape as `Ty::is_affine` (ADR 0067).
  `validate_vc_type_position` states the rule again for
  `VcTypePosition::Local`, and the loop-head havoc's entry-state lookup is a
  named fail-closed refusal rather than a `HashMap` index, because only a
  parameter has an entry state.

  This fences the hole rather than modelling aliasing: there is still no loan
  map and no loan liveness. What holds instead is that a borrow now exists only
  where the compiler already relates it to its owner — written at a call, bound
  to a parameter for the length of the call, with the ADR 0022/0023
  argument-overlap rule enforcing exclusivity across that call — so no second
  name for one storage survives a statement boundary. Borrow locals, if the
  language ever wants them, arrive with an aliasing model and replace this rule.
  `docs/shape-admission.md`'s `check local` column is where the rule is blessed
  per shape; `docs/type-matrix.md` cannot see it, because a borrow has no
  declared local spelling for a source-level probe to write.

- **A havoc path is exhaustive or it is wrong; fresh-state-for-a-type exists
  once** (ADR 0074). `Generator::fresh_state_for(ty, binder, base, len)` is
  the single answer to "what is a fresh symbolic state for a value of this
  type": one binder of the type's Lean shape, the facts every checked
  inhabitant satisfies, and the environment value that holds it. Parameter
  entry, the one call-site havoc (`havoc_mut_borrow_args`, used by ordinary,
  method, and constructor calls alike — `&mut [T]` arguments included), and
  both loop-head havoc branches (the generic name branch and the init-field
  branch) all consume it. The dispatch over `Ty` has no wildcard, so a new
  constructor is a compile error in every havoc path at once, and a shape
  with no fresh-state story latches a named `refuse_vc_type` refusal instead
  of leaving a stale chain the prover would read as post-mutation state —
  the false-proof mechanism behind the audited init-loop class-field and
  loop-mutated raw-pointer holes. Site policy stays at the site: binder
  names, the array length relation (entry states are bounded; havoc
  preserves the replaced state's length), and the binding-mode filters. The
  destructor context joins the method context in the loop havoc's `self`
  branch (fresh state, field facts, no class invariant — ADR 0029), and
  sealed raw/resource/device operations refuse a *field* borrow argument by
  name (`resource.field_borrow_op`) rather than write a view back over the
  whole object, with `sealed_borrow_root` as the arms' fail-closed second
  layer.

- **Affine options have a checked ownership identity and an exact local native
  slice.** G2.0 is the closed representation/fail-closed checkpoint; G2.1's
  checker/proof/interpreter/monitor slice and G2.2's formal-SVM slice are also
  closed. G2.3's matching LLVM slice is closed as well.
  `Ty::Option(Box<Ty>)` is the only option constructor, and whether an option
  owns is computed rather than encoded: `Ty::is_affine` reads
  `Ty::Option(payload) => payload.is_affine()`, so `option<[T]>` is an option
  over an owned array (ADR 0065). The owning family — the shapes the move,
  take, join, and destruction rules are written for — is read back with
  `Ty::as_affine_option_payload`, which asks for an owned-array payload
  specifically: `option<class>` owns too and belongs to the copyable family's
  gates, which refuse it by their own name. Every rule that would duplicate an
  option asks that question explicitly, and wherever a rule dispatches on
  option shape the owning arm comes first.

  The parser preserves Boolean, integer, or in-scope-parameter array payload
  identity rather than pretending every future affine option is Boolean.
  Monomorphization validates and substitutes parameter payloads and rechecks
  concreteness. The checked representation can additionally carry a record
  payload, which the surface grammar spells as `[Pair]`; module
  traversal applies nominal visibility to it, and
  `type.array_payload_unsupported` is the semantic gate that keeps it closed. At
  G2.0 those representation paths authorized no payload and every semantic
  boundary failed closed, including for the Boolean case.

  G2.1 opens only explicit mutable local `option<[bool]>` values. Initialization
  is mandatory and is either `none` or
  `some(alloc_array<bool>(len, init))`; wrapping an existing owned array and
  array-literal construction remain closed. `.is_some` reads the tag without
  consuming the value. Program `.value` is forbidden because it would expose
  the owned descriptor without clearing the container. `.take` is represented
  as a named-place mutation and is accepted only as the direct initializer of
  an explicit owned `[bool]` local. It checks presence and atomically transfers
  the payload while leaving the mutable option container initialized as
  `none`; presence is value state rather than checker typestate.

  The proof value is `Option (Sable.Seq Bool)`. VC generation snapshots the
  pre-take value, emits its someness obligation, returns the sequence payload,
  and changes the source environment entry to typed `none`; loop effect
  collection therefore treats take as a source assignment. The interpreter
  keeps affine options distinct from copy options, atomically takes from the
  named frame slot, and recursively drops a still-present payload exactly once
  at lexical scope exit. The proof monitor operates on immutable snapshots, so
  it never becomes an executable owner. Affine payload clauses use option
  `match`; affine `.value` is deliberately unmonitorable because `Sable.Seq`
  has no global `Inhabited` instance, and the monitor must not accept text that
  Lean cannot elaborate.

  Parameters, returns, calls, fields, traits, generics, borrows, exposure,
  inferred option bindings, whole-option assignment, nested or non-Boolean
  affine options, and discarded affine temporaries remain closed. G2.2 opens
  only the exact local Rust-to-SVM bridge; every other SVM ingress retains
  `svm.affine_option_unsupported`. G2.3 opens only that same local Boolean-array
  option slice in LLVM; every other native ingress retains
  `backend.affine_option_unsupported`. Neither stage implies an aggregate ABI.

  The formal core uses the existing recursive `Val.opt` and adds
  `Stmt.optTake dst src`, deliberately generic at the untyped machine layer.
  The Rust bridge is the exact supported-subset gate: its source must be the
  G2.1 local `option<[bool]>`, its destination an owned `[bool]`, and every
  ABI, call, field, trait, generic, borrow, exposure, and whole-option path
  remains rejected. For distinct names, a present value steps atomically to
  an environment with the source set to `.opt none` and the destination set
  to the former payload. A distinct empty option traps `optionNone`; a missing
  or wrong outer source is `undef`; and source/destination aliasing is
  immediately `undef`. No destination-absence premise is imposed because the
  flat SVM environment reuses lexical-local names across loop iterations and
  must overwrite the stale binding. The tagged `.arr (.bools ...)` payload is
  transferred intact, including the empty-array tag.

  LLVM represents the admitted local as
  `%sable.option.array.bool = type { i8, %sable.array.bool }`. Tag zero is the
  complete zero aggregate. Tag one owns the nested descriptor, including a
  present empty Boolean array whose descriptor is null/zero. Construction is
  still exactly `none` or `some(alloc_array<bool>(len, init))`; `.is_some`
  compares the named local's tag with one. A native take loads and guards that
  tag with trap kind 8, extracts the descriptor only on the success edge,
  stores the full source as `zeroinitializer`, and then installs the
  destination. The source therefore ceases to own before the destination slot
  does.

  The LLVM cleanup registry is typed: it records ordinary Boolean arrays and
  affine Boolean-array options separately, then unwinds both in the established
  reverse declaration and scope order. Option cleanup follows the tag-one edge,
  extracts the payload, and calls `__sable_rt_array_free_v1` only when its data
  pointer is nonnull. Absent, taken, and present-empty options call no free
  hook. Construction reuses the existing allocation/free hooks, zero-length
  bypass, 50,000,000-element cap, kind-9 OOM trap, and kind-10 payload bounds
  trap. Every trap edge remains terminal and performs no cleanup.

  The native bridge remains local-only. Option parameters and returns, calls,
  entries, externs, fields, traits, classes, generics, borrows, exposure,
  whole-option assignment or movement, inferred bindings, discarded affine
  temporaries, non-Boolean payloads, and wrapping existing or literal arrays
  remain rejected. The internal named type is versionable and establishes no
  cross-module, Sable, or C ABI.

  G2.0 closed under the exact one-worker command
  `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
  SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
  --test-threads=1 --nocapture`. `cargo check` and standalone
  `lake -Kjobs=1 build` were green; Lake built 22/22 targets with only the same
  existing linter warnings. Rust library tests passed 192/192; all 396 corpus
  subjects (83 verifies, 246 must-fail, 48 tests, 19 test-fails) passed in
  192.03s; LLVM CLI passed 7/7; the exact interpreter/native differential
  passed 1/1 over six subjects at `-O0` and `-O2`; and SVM differential stayed
  86/86. Randomized allocator, grind-budget, LSP, doc-tests, rustfmt,
  diff-check, and static-audit gates were green. G2.0 is closed.

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

  G2.2 closed under the exact one-worker command
  `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
  SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
  --test-threads=1 --nocapture`. `cargo check` and the standalone Lake build
  were green; Lake built 22/22 targets with only the existing warnings.
  Focused SVM units passed 35/35, Rust library tests 211/211, and the recursive
  corpus all 416 subjects (84 verifies, 263 must-fail, 49 tests, 20 test-fails)
  in 270.58s. LLVM CLI passed 7/7; the native differential passed 1/1 over six
  subjects at `-O0` and `-O2`; and SVM differential passed 92/92. Free-list
  allocator, grind-budget, LSP, documentation, rustfmt, diff-check, and
  static-audit gates were green. G2.2 is closed.

  G2.3 closed under the exact standard command
  `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
  SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
  --test-threads=1 --nocapture`. `cargo check` was green; standalone Lake built
  22/22 targets with only the existing warnings; focused LLVM units passed
  29/29; and Rust library tests passed 213/213. The recursive corpus passed all
  416 subjects (84 verifies, 263 must-fail, 49 tests, 20 test-fails) in
  194.43s. LLVM CLI passed 8/8; the exact interpreter/native differential
  passed 1/1 over seven subjects at Clang `-O0` and `-O2`; and SVM differential
  remained 92/92. Free-list allocator, grind-budget, LSP, documentation,
  rustfmt, diff-check, and static-audit gates were green. G2.3 is closed;
  no widened option ABI follows.

- **N0 is the proof-neutral native `u32`-array foundation for `Nat`.** The
  backend now admits fresh owned local `[u32]` values from a contextual literal
  or `alloc_array<u32>`, followed by length, checked index reads, and stores.
  `%sable.array.u32 = type { ptr, i64 }` retains the logical element count in
  the descriptor. Nonempty allocation passes `len * 4` bytes to the existing
  v1 allocation hook; zero length is the null/zero descriptor and calls neither
  hook. The profile cap remains 50,000,000 elements. OOM kind 9 reports the
  logical length, not the byte count, and OOB kind 10 reports index and logical
  length.

  The v1 hook contract is a byte-allocation contract and makes no promise of
  alignment greater than one. Generated `u32` loads and stores therefore use
  explicit `align 1`, and address formation remains non-`inbounds`. A future
  aligned or typed hook may enable stronger access alignment, but N0 does not
  change the existing runtime ABI to obtain that optimization.

  Internal ordinary functions may take `&[u32]` or `&mut [u32]`. A call is
  accepted only when its checked argument remains the exact explicit named
  borrow node with matching mutability; overlapping mutable aliases remain
  rejected. Both parameter forms borrow a descriptor and never enter the
  cleanup registry. Owned callers retain responsibility for reverse lexical
  cleanup across normal branch exits, each loop iteration, and early return;
  traps still do not unwind.

  N0 does not admit owned-array parameters or returns, array-valued entries,
  fields, classes, methods, externs, public or cross-module ABI, other integer
  widths, whole-array transport/rebinding, exposure, generic containment, or
  option containment. A *Boolean* array borrow is admitted, by the separate
  rule below (ADR 0070); the `u32` and `bool` borrow rows of
  `docs/shape-admission.md` are identical. Its source verification, interpreter,
  and formal integer-array value already existed, so N0 changes no VC or Lean
  semantics.

  N0 closed under the exact one-worker command
  `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
  SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 --
  --test-threads=1 --nocapture`. `cargo check` was green; focused LLVM units
  passed 31/31; Rust library tests passed 215/215; and the recursive corpus
  remained green across 416 files (84 verifies, 263 must-fail, 49 tests, 20
  test-fails) in 213.51s. LLVM CLI passed 9/9; the exact
  interpreter/native differential passed 1/1 over eight subjects at Clang
  `-O0` and `-O2`; and SVM differential remained 92/92. Randomized allocator,
  grind-budget, LSP, documentation, rustfmt, diff-check, and static-audit gates
  were green. N0 is closed.

  N1a closes the first fixed-owner class slice. The exact admitted class has
  one owned `[u32]` field, no methods, and an explicit empty destructor; its
  internal type is `%sable.class.<id> = type { %sable.array.u32 }`. A direct
  constructor initializes a final immutable stack owner through an internal
  destination pointer. Definite-initialization validation requires fresh field
  storage exactly once on every path, and reverse lexical cleanup frees the
  nested limb allocation.

  Shared `&Nat` parameters are non-owning internal pointers. Together with
  class-field length/index lowering, this compiles the real imported
  `Nat::from_prefix` and `cmp`. The standard gate passed 217/217 library tests,
  33/33 focused LLVM units, all 417 corpus subjects, LLVM CLI 9/9, nine-subject
  interpreter/native comparison at `-O0`/`-O2`, and SVM 92/92.

  N1b adds internal destination-passing returns for that same exact shape.
  A class-returning free function receives a caller-owned result pointer;
  direct construction and tail calls write there without an intermediate
  owner. A named local move transfers the aggregate and zeros its source, so
  normal reverse lexical cleanup remains safe. Validation tracks moved owners
  through scopes and control flow: reaching branches must agree exactly, early
  returns terminate a path, and loops may not change owner liveness across a
  backedge. The imported fixture exercises constructor returns, return-call
  forwarding, local moves, moved-local returns, and an early-return branch.

  N2 admits the real imported `add` call closure without adding another native
  representation or lifetime rule. Shared `&Nat` inputs and their reborrows
  are non-owning pointers; scalar helpers select limb values and lengths; one
  fresh local `[u32]` scratch buffer is filled by the carry loop; and trimming
  plus `Nat::from_prefix` constructs the fixed-shape result. N1b's hidden
  destination and named-move rules carry that result to its caller, while the
  existing cleanup registry destroys scratch and nested allocations in reverse
  lexical order. The fixture verifies 40/40 obligations across zero identity,
  `1 + 2`, full carry, and unequal-length cases, and its direct Clang builds
  return 42 at both `-O0` and `-O2`.

  N3 carries the real imported `sub` and schoolbook `mul` closures through the
  same boundary. `sub` fills one fresh `[u32]` scratch array with checked
  borrow arithmetic. `mul` fills one fresh output array using nested scalar
  loops and checked limb-product/carry arithmetic. Both trim the scratch
  prefix, construct the fixed-shape result with `Nat::from_prefix`, return it
  through N1b's hidden destination, and consume the named result local through
  the existing move-neutralization path. Scratch descriptors and nested result
  storage remain ordinary reverse-lexical cleanup entries.

  The N3 fixture verifies 51/51 obligations across 19 functions and directly
  returns 42 under Clang `-O0` and `-O2`. Its cases cover subtraction to zero,
  a borrow chain across two zero limbs, zero multiplication, a maximum limb
  squared, and cross-limb carry. N3 adds no representation, runtime hook,
  ownership rule, or ABI.

  N4 carries the real imported `div`, `rem`, and `gcd` closures through mutable
  locals of the same exact fixed `Nat` type. Every reassignment target has one
  scratch slot allocated in the function entry. The complete right-hand side
  is produced into that slot before the old target is dropped, preserving
  self-borrows in `dd = dd - vn` and `q = shift_in(&q, d)`. Lowering then
  transfers the replacement aggregate to its target and zeros the scratch, so
  ownership remains singular and loops do not execute new stack allocations.

  The existing cleanup scopes already express N4's loop lifetimes: body-local
  owners are destroyed in reverse lexical order before a backedge, outer
  mutable owners remain function-scoped, and zeroed named-move carriers are
  null-safe cleanup no-ops. Reassignment scratch slots are unregistered and
  empty after transfer. Validation permits reassignment to revive a moved
  mutable target while retaining exact reaching-branch and loop-backedge
  owner-liveness agreement.

  The N4 fixture verifies 109/109 obligations across 21 selected functions
  with six small hand discharges and directly returns 42 under Clang `-O0` and
  `-O2`. It covers division by one, exact and inexact quotient/remainder pairs,
  a multi-limb quotient-estimate correction, and basic, zero-input, and coprime
  gcd cases. N4 adds no representation, hook, proof rule, or aggregate ABI.

  N5 implements exactly `Integer { Nat mag; u64 neg; }`. Its internal LLVM
  aggregate nests the already-supported `Nat` representation and an `i64`;
  this does not infer layouts for arbitrary recursive classes. Constructor
  validation keeps an initialization bit per field, so owned `mag` and scalar
  `neg` must each be written exactly once on every reaching path. Class-field
  lowering now supports the scalar reads/stores and exact nested borrows used
  by the imported implementation: `&x.mag` yields a shared pointer to the
  nested owner, while `&a.limbs` yields the established non-owning array
  descriptor pointer.

  The only new owned-parameter convention is an exact `Nat` take. Internal
  calls pass its aggregate by value; named caller owners are zeroed when taken,
  while a class-returning argument is first materialized in a unique
  entry-hoisted, unregistered scratch slot. The completed aggregate is loaded
  by value and the scratch is zeroed immediately before the call. The callee
  installs the aggregate in an owning stack slot and registers it for lexical
  cleanup. Moving that parameter into `Integer.mag` zeros the slot, so either
  the field or the unconsumed parameter—never both—owns the nested allocation
  at cleanup; there is no caller-side post-call drop.

  Mutable `&mut Integer` is a non-owning pointer and is admitted only through
  the exact checked mutable borrow. Method dependency discovery, internal
  mangling, validation, and emission are opened for the private unit-returning
  `Integer::flip_sign(&mut self)` reached by `negate_in_place`; its scalar field
  update does not imply general method lowering. Recursive drop walks supported
  class fields in reverse declaration order: `Integer.neg` is a scalar no-op,
  then `Integer.mag` drops its `Nat.limbs` array through the existing null-safe
  free path. Registered named-owner and parameter slots become cleanup no-ops
  after they are zeroed; the unregistered argument scratch is empty before the
  callee runs.

  The N5 fixture verifies 237/237 obligations across 39 selected functions and
  directly returns 42 under Clang `-O0` and `-O2`. It covers construction,
  unary and in-place sign operations, addition, subtraction, multiplication,
  and Euclidean division/remainder across all operand-sign combinations. A
  strong allocator-hook test is green at both optimization levels with exit 42
  and `live = 0`, and aborts on a leak, unknown free, or double free. The exact
  `VerifiedProgram` differential is green 1/1 over 13 subjects at `-O0` and
  `-O2`, including `Integer` exit 42.

  N5 closed under
  `SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1`. The gentle serial
  run passed 223/223 library tests; corpus 1/1 in 93.64s; randomized allocator
  1/1; grind-budget 1/1; LLVM CLI 10/10; differential 1/1 in 31.35s; LSP 1/1;
  SVM differential 1/1; and documentation tests. `cargo check -j1` and rustfmt
  were green as well. N5 is closed.

  Owned `Integer` parameters, arbitrary owned class parameters, methods beyond
  this exact `flip_sign` closure, mutable borrows of other classes, discarded
  class results, field moves, additional or generic class shapes, nonempty
  destructors, array whole-value transport, and every public, extern, or
  cross-module class ABI stay closed. Generic owner slots and `Vec` remain a
  separate later design.
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
- **A move is one operation, and every sink performs it** (ADR 0030). A declaration, an assignment, a field assignment, a call/constructor/method argument and a return all *take* a value: the source place stops holding it, and whatever the destination held is destroyed. The interpreter has one `take_place`/`drop_place` behind `eval_moved` — overwriting a place runs a full drop (invariant → destructor → remaining fields), a returned local leaves with the caller rather than being destroyed behind it, and an owned parameter dies with the callee's frame after its contract has been checked. The checker has one `transfer` at the matching sinks: it kills the source place, applies the loan-brand rule (recursively, so `raw_offset(p, 1)` cannot launder what `p` may not), and reports whether a `#[must_consume]` obligation travelled with the value. Affinity covers class values, resources, **and owned arrays** — two names reaching the same elements is unsound the same way, and the diagnostic names the category (`class`/`resource`/`array` prefixes on `use_after_move` and `loop_shape`). A member may move a field out but must restore it before it exits (`class.field_not_restored`); only a `deinit` may leave a hole, because only there is the invariant already gone. A contract still reads a moved-from parameter's entry value: a value outlives the transfer of authority over it. Branch joins and loop checks operate over the whole per-place state (`PlaceState`: initialized, branded, obligation) rather than a chosen subset: branches join initialization by AND and brand/obligation by OR over reaching paths, while a loop requires its backedge to preserve affine liveness, brands, and obligations before restoring the zero-iteration entry state. Every `Place` maps to that state by its complete rendered key (`self.f`, not merely `self`). The `#[must_consume]` obligation is a *state of the place*: moving the token clears it, landing sets it, a marked field regains it on assignment, and a live one may not be assigned over.

  G1.6's lifetime audit closed a legacy exception to that rule: array-field
  assignment has a special whole-array consuming path, and it had stamped a
  matching owned type without first checking whether the local source was
  already moved. The checker now performs the moved-place guard explicitly;
  the interpreter's `eval_moved` takes a named owned-array source, while local
  and owned-parameter drops remove arrays from their places. The 245th
  must-fail subject moves one integer array into two fields and pins
  `array.use_after_move`, preventing two logical sequences from sharing one
  mutable backing allocation.

  Two corollaries about *where* a value dies: a discarded class-valued result is a temporary with no place, destroyed at the end of its statement, and **`unsafe { ... }` is a marker while an exposure body is a scope** — the block grants vocabulary and has no lifetime (its locals belong to the enclosing function, and the interpreter runs it through `exec_open_block`), while an exposure *is* a lifetime, so the loan's bindings and everything the body declared end at its closing brace. Scope exit rejects a disappearing local that still holds a must-consume token.
- **Non-memory resources, and an explicit world** (ADR 0028). `resource OpenFile` is the authority to use one descriptor (position in the view, as POSIX has it); `resource PosixWorld` is the outside, and any foreign operation touching global state must receive it explicitly — which is what replaces a `modifies` clause over the universe, and lets a caller see from a signature whether a function can reach outside. Authority for a descriptor is carved from the world (`open_file(&mut w, fd)`) with *availability* as a precondition — open, and not already handed out — and carving **spends** it (`PosixWorldView.claimed`, updated functionally as `w.claim fd`), since affinity governs a token that exists and would not stop a second being minted beside it (ADR 0030). The checker tracks tokens, the VCs track the state of the outside. `posix_world(script)` is confined to `test_` functions — the one place authority appears from nothing — and the script is how a test author controls short reads and I/O errors, which the *view* deliberately does not model because no contract can predict them.
- **Foreign contracts are audited, and the build says so** (ADR 0027). `extern "C" #[audit(id := ..., reason := ...)] fn f(...);` owes no obligations — there is no body to check — but its clauses still get well-formedness defs, and the audit metadata is mandatory. Effects are structural: only a passed `resource &mut R` may change, so there is no `modifies` clause in the language. Resource erasure at this boundary is governed by an explicit ABI whitelist (`RawSpan`, `OpenFile`, and `PosixWorld`), not a permissive “all resources erase” rule; sealed allocator authorities and profile capabilities such as `Uart` cannot cross an extern. **Nonescape sits on the audited side of the boundary**: that a callee unable to *return* storage cannot retain it is compiler-checked for a verified callee (no globals, so the pointer dies with the frame) and an audited promise for a foreign one, since nothing stops C stashing it in a foreign global — part of what the audit id covers (ADR 0030). The trust manifest is emitted **into** the hashed Lean content, so changing an audit id invalidates an artifact exactly as changing a proof does (ADR 0018's hash is over bytes); importers inherit it through the flat merge. Status reads `verified relative to audited boundary`, never `fully verified`, whenever an extern assumption remains. `sable test` supplies deterministic shims keyed on the *audit id*; an unknown id traps rather than running the empty body.
- **A safe `[u8]` reaches raw memory through a lexical construct, not a proof** (ADR 0026). `unsafe expose &a / &mut a as (p, resource m) { ... }` lends the array's bytes for the body and takes them back: entry binds a span whose bytes are the array's elements, exit makes the array what the bytes say, under generated obligations (the whole extent came back; every byte is present and in `u8` range). The owner's name is *frozen* for the body (`expose.owner_frozen`, ADR 0073): reading, writing, indexing, `.len`, borrowing, or re-exposing the exposed array is refused, so the loan is the storage's only name and copy-in/copy-out is faithful; a length the body needs is bound to a local before the exposure. Hidden *loan brands* do nonescape with no lifetime syntax — branded values cannot be returned, assigned outside the body, or passed to a user function — and the brand follows provenance through `raw_offset`/`split_off`/`join` but not onto loaded bytes. Raw operations pair a pointer with a resource borrow (`Ty::Raw`, `Val::Ptr`, `SpanView.namesByte`) and live inside `unsafe`; `unsafe regions: N` is reported in build output. `raw_copy_nonoverlapping` carries **no nonoverlap premise**: two distinct affine tokens *are* separation.
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

Machine values are orthogonal (ADR 0062): an aggregate carries ordinary values,
not a hand-specialized copy of them. Options occupy one recursive value form,
`Val.opt : Option Val`, in both presentations, and it is the *only* option
form: a nullable raw pointer is an ordinary option whose present case carries a
`Val.ptr`. Generic machine
constructors and accessors preserve the payload value, while outer-shape
confusion is `undef` and extracting absence is `Trap.optionNone`. Which
payloads may occupy an option in a given source position stays a checker
question; the machine has one option semantics.

Arrays are `Val.arr (elem : ValTag) (a : Seq Val)` — a payload tag beside a
sequence of ordinary machine values. The tag is what an empty array retains,
so later stores still know which scalar domain is legal; it is a *name* for a
domain rather than a second copy of its values, which is why length, index,
allocation, and store each have one implementation instead of one arm per
payload. `Val.tag?` is the single admission gate, and `Val.arrSet?` refuses
a store whose value does not inhabit the array's tag. Wrong-domain stores are
`undef`, whereas matching out-of-bounds stores produce `Trap.indexOOB`.

The harness (`compiler/tests/svm_diff.rs`, ADR 0017) lowers every function in
`corpus/svm-diff/` to Lean terms (`compiler/src/svm.rs`), runs each on both
`interp.rs` and the appropriate Lean evaluator, and compares those canonical
observations exactly — a divergence is a bug in one of two artifacts that are
otherwise trusted independently. Lowering is strict: a subject outside the
machine's supported subset is a hard failure, never a skip. `test_uart`
selection remains a machine statement through explicit and inferred
declarations, assignment, and discard. Authority-only resource operations erase
only when every operand is syntactically runtime-inert; a potentially trapping
or effectful operand is rejected instead of silently dropped. The focused
differential now covers 86/86 subjects, including Boolean option
absence/presence, local assignment, accessor results, A-normal call transport,
and owned-local Boolean-array allocation, literal construction (including
empty), length, reads, stores, loops, OOB/OOM outcomes, and store trap
precedence. UART success, budget exhaustion, readiness clearing, ordered
traces, invalid writes, profile reselection (including its precedence over
script-expression traps), and all three selection contexts remain covered.
The lowerer treats the formal array representation as an owned-local bridge,
not a call/storage ABI. That boundary's complete one-worker closure was green at the time it was
drawn — library tests, the then-394-subject corpus, the LLVM CLI and native
differentials, the SVM differential, and the allocator, grind-budget, LSP,
and documentation gates; the corpus has since grown well past that count.

## The differential-pair harness

`compiler/tests/pairs.rs` runs a second, Lean-free differential: each `corpus/pairs/` pair `<stem>.a.sable`/`<stem>.b.sable` holds two spellings of one program whose first-line marker says what must agree — `// pair: same-lean` compares front-end diagnostic-name sets and per-file α-normalized obligation multisets from the in-process emission path, `// pair: same-run` compares diagnostic names and the interpreter outcome of every zero-argument function — because treating two spellings of one program differently is the shape a false-proof defect takes before Lean ever sees it.

## Repo layout

```
docs/design/       normative language design + roadmap
docs/PLAN.md       milestones and exit criteria (kept current)
docs/decisions/    ADRs — one settled decision each, with the why
compiler/          Rust package `sable` (single crate until it hurts; split when it does)
lean/              Lake package: Sable prelude; pinned via lean-toolchain
runtime/hosted/    optional C implementation of versioned native runtime hooks
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
corpus/pairs/      differential pairs <stem>.a.sable / <stem>.b.sable: equivalent
                   spellings of one program, compared Lean-free by
                   compiler/tests/pairs.rs per the first-line marker
                   (// pair: same-lean | same-run)
docs/notes/        probe files and audit notes (SVM draft findings, class encoding)
editors/           Neovim setup + VS Code extension
.sable-out/        immutable roots, module artifacts, proof-env source/build
                   snapshots, and daemon socket (gitignored)
```

## Toolchain pins

Lean is pinned by `lean/lean-toolchain` (elan resolves it). Upgrades are deliberate, tested against the corpus, and get a commit of their own. Rust: whatever stable cargo is current; no nightly features.
