# Sable

[![CI](https://github.com/alonamaloh/sable/actions/workflows/ci.yml/badge.svg)](https://github.com/alonamaloh/sable/actions/workflows/ci.yml)

Sable is an imperative, C-flavored language in which **every function carries a machine-checked proof of its contract**. One source file interleaves two languages: a C-like program language with no undefined behavior and an ownership-based memory model, and a Lean 4 proof language that lives entirely on lines beginning with `///`.

**Status: milestones M0–M45 are complete. Unsafe Sable v1 has reached a defensible stopping point, the LLVM IR backend now covers the scalar core, Boolean options, and internal integer-field POD record values, M46/G0's recursive generic-type foundation is complete, G1.0–G1.5 are closed.** Verified today: binary search, insertion sort, **quicksort and the merge kernel** (full `sorted ∧ permutation` specs with frame conditions), **hex and varint codecs** (pointwise specs plus kernel-checked round-trip theorems), classes with invariants (`BoundedStack`), a **generic growable `Vec<T>`** with its reallocation frame condition, a **hash map verified against the linear-probing contract** under a law-carrying `Hashable` trait bound, a **UTF-8 codec with a kernel-checked roundtrip**, a **JSON parser verified against the recursive RFC 8259 grammar** (tokenizer + structural validation), C++-`optional`-style **option accessors** whose syntax works identically in code and contracts, **the bignum pillar — arbitrary-precision `Nat` with cmp/add/sub, schoolbook multiplication, division, and gcd, every operation verified against a one-line spec over the abstraction function** (now written with operators: `q = q + m` under `while (r >= b)`), a **verified UTF-8 `String` with self-proving literals**, file-based **modules**, the escape-hatch assurance ladder, a **verified in-band free-list allocator with mandatory client leases, first-fit allocation, exact return, and proved local coalescing**, a **generic affine resource map** with sealed exact-entry transfer, and an **arena-backed intrusive list over explicitly laid-out typed records** — all in a corpus that doubles as the compiler's regression conscience. M44 adds the first formal UART machine profile; M45 adds verified-to-native scalar LLVM lowering. G0 completes recursive parsing and structural identity; G1.0 separates parameter/payload representation from the integer proof model; G1.1 admits only the first Boolean aggregate path; G1.2 carries its ordinary-function intersection through the formal SVM; G1.3 carries the same intersection into LLVM; G1.4a adds ordinary Boolean argument transport and verified/interpreted/native internal POD record calls without declaring a record ABI; G1.4b adds verified and dynamically monitored owned-local Boolean arrays while keeping both backend boundaries closed; G1.5 carries that exact local slice through the formal SVM and Rust differential bridge while LLVM remains closed. Broader devices, ISA work, and broader aggregate backend support remain deliberately deferred rather than blocking the language's usability roadmap. See [`docs/PLAN.md`](docs/PLAN.md) for milestone-by-milestone detail. The normative design documents (working draft 0.4):

- [`docs/design/sable-language-design.md`](docs/design/sable-language-design.md) — the language: syntax, contracts, ownership, ghost code, termination, escape hatches, the SVM machine model, and the staged trust story.
- [`docs/design/sable-goals-and-roadmap.md`](docs/design/sable-goals-and-roadmap.md) — the benchmark-driven roadmap, from verified sorting through a GMP-style bignum library to the kernel horizon.

## The idea in thirty seconds

```sable
/// pre  ∀ i j, 0 ≤ i → i < j → j < a.len → a.get i ≤ a.get j
/// post match result with
///      | some i => 0 ≤ i ∧ i < a.len ∧ a.get i = key
///      | none   => ∀ k, 0 ≤ k → k < a.len → a.get k ≠ key
fn binary_search(&[i32] a, i32 key) -> option<u64> {
    mut u64 lo = 0;
    mut u64 hi = a.len;
    /// invariant hi ≤ a.len
    /// invariant ∀ k, 0 ≤ k → k < lo → a.get k < key
    /// invariant ∀ k, hi ≤ k → k < a.len → key < a.get k
    /// variant   hi - lo
    while (lo < hi) {
        u64 m = lo + (hi - lo) / 2;
        if      (a[m] < key) { lo = m + 1; }
        else if (a[m] > key) { hi = m; }
        else                 { return some(m); }
    }
    return none;
}
```

This is not pseudocode: [`corpus/verifies/binary_search.sable`](corpus/verifies/binary_search.sable) verifies today — 19 obligations, 17 discharged automatically, 2 by short hand-written `discharge` scripts (the two that genuinely need the sortedness quantifier instantiated). Fold the `///` lines and it reads as plain C with a contract. The contract (`pre`/`post`) is **interface** — always shown, in docs, on hover. The loop annotations are **evidence** — dimmed, foldable, for the checker and the proof maintainer. A reader may ignore proofs; no reader may be shown a function without its contract.

## What works today

```sh
cd compiler && cargo build --release

sable check file.sable                   # verify: every obligation kernel-checked by Lean
sable test  file.sable                   # run test_* functions with dynamic contract checks
sable build --emit-llvm --entry main file.sable  # verify, then print textual LLVM IR
sable check -M lib/ app.sable            # resolve `use` imports against lib/ (ADR 0013)
sable lsp                                # language server (stdio)
sable daemon                             # warm checker: ~0.25s/check instead of ~2.4s

# optional direct formal-package gate; normal checks build an immutable snapshot
cd ../lean && lake -Kjobs=1 build
```

The scalar LLVM v0 backend is complete, G1.3 extends its internal runtime
subset with Boolean options, and G1.4a adds root-owned integer-field POD record
values. Its handwritten, libLLVM-free command is shown
above (full form:
`sable build --emit-llvm [--entry NAME] [-o FILE|-] file.sable`). It consumes
only an opaque `VerifiedProgram` containing the exact AST accepted by Lean,
emits scalar literals/locals/calls/Boolean negation/unit plus `if`, `while`,
signedness-aware comparisons, true short circuiting, checked integer
arithmetic, and explicit integer conversions, and strictly rejects everything
not yet implemented. Signed and unsigned add/subtract/multiply and signed
negation use overflow intrinsics; division/remainder and narrowing are guarded,
signed division/remainder is corrected to Sable's Euclidean convention, and
every failure reaches a versioned weak hook and then `llvm.trap`. The emitter
uses none of LLVM's poison-producing arithmetic promises. Scalar v0's complete
serial gate was green: 26/26 library tests, 6/6 verified LLVM CLI tests, and a
1/1 native differential test comparing the exact `VerifiedProgram` interpreter
outcome with Clang `-O0` and `-O2` for scalar, control-flow, and arithmetic
subjects. The cases include negative divisors, `MIN % -1`, conversion bounds,
and a loop condition whose result would expose unsafe hoisting. All seven
published trap kinds produce the exact pinned payload and still reach the
mandatory trap at both optimization levels. The same run kept the SVM
differential at 69/69, completed the full verifier/dynamic corpus in 220.78s,
and passed the randomized allocator, grind-budget, LSP, and documentation
tests. At that scalar checkpoint aggregate values and their backend ABI
remained future work. G1.3 and G1.4a add only internal Boolean-option and POD
record representations, not public or foreign aggregate ABIs. Broader
aggregates remain future work.
See
[`docs/decisions/0058-llvm-lowering-consumes-a-verified-program.md`](docs/decisions/0058-llvm-lowering-consumes-a-verified-program.md).

M46/G0—the representation, parser, identity, and fail-closed foundation for
broader generics—is complete. Use-site type arguments now parse recursively as
integers, `bool`, in-scope parameters, visible records and classes, `[T]`, and
`option<T>`; a `TypeArg` retains the span of its complete outer type. The parser
bounds every path at 64 type nodes, every argument list at 256 entries, and each
outer argument at 4096 total nodes. Imported generic-class names and arities are
tracked separately from the checked class-index table, so parsing a nested
nominal type cannot perturb downstream indices. This is a syntax and identity
checkpoint, not a semantic widening: every non-integer shape still fails at
`mono.type_arg_unsupported` before checked types are built.

Structural `InstanceKey` identity and deterministic emitted-name collision
detection remain the monomorphizer's authority. Generic-use traversal covers
record literals, `some(...)`, class destructors, and member contracts and
variants. Duplicate traits, impl spec definitions, and impl methods now report
the second source declaration deterministically. Module loading also keeps the
flat linker honest: functions/classes/records share the runtime namespace,
while traits and constants have separate namespaces; restrictive imports now
recognize public constants, and visibility walks both recursive generic types
and every nominal checked type. G1's semantic slices widen Boolean/POD
aggregate values one complete, independently fenced path at a time.

G1.0 establishes the boundary needed for that widening without crossing it.
Declaration parameters are represented as `Ty::Param(TypeParamId)`, while
array/option payloads use `ValueTy::{Int, Bool, Record, Param}` instead of
encoding every case as `IntTy`. Monomorphization validates parameter identities
before substitution and proves afterward that every ordinary declaration is
concrete; only retained ADR 0009 templates may still contain `Param`. Proof
reuse is an explicit `ProofReuse::Adr0009IntModel` capability with an opaque
payload, rejected on input and authored only by monomorphization for the
existing concrete-integer domain. The preparation and VC-generation entry
points are crate-private, closing a direct external-AST route around that
authority. At that checkpoint, checker, VC generator, interpreter, and SVM
lowering each independently rejected Boolean/POD aggregate payloads, and module
visibility followed nominal record references nested inside those payloads.
Thus G1.0 preserved all existing integer behavior and granted no new
source-level aggregate semantics.

G1.0's complete low-concurrency closure command was
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`. It passed
101/101 library tests; all 368 corpus subjects (79 verifies, 228 must-fail, 44
dynamic, 17 dynamic-fail) in 382.78s; LLVM CLI 6/6; the exact
`VerifiedProgram` interpreter↔Clang differential at `-O0` and `-O2` 1/1; and
SVM differential 69/69. The randomized allocator, grind-budget, LSP, and
documentation gates were green as well. G1.0 is closed.

G1.1 implements a deliberately narrow `option<bool>` path through parsing,
checking, Lean VC generation, the Rust interpreter, and the dynamic contract
monitor. Ordinary functions and inherent class methods may return
`option<bool>`; explicit or inferred locals may receive those results or
contextual `some(bool-expression)`/`none` values, be assigned from calls
returning the type, tested with `.is_some`, and read with `.value` under the
usual someness obligation. The proof model is genuinely `Option Bool`: packing
Sable's proposition-valued symbolic Boolean uses an explicit decidable
proposition-to-`Bool` bridge, and reading the payload maps it back through
`o.value = true`. Runtime and monitor values retain the option payload type even
for `none`, so junk-on-none remains Lean's payload-specific `default` (`0` for
integers, `false` for `Bool`) while executable `.value` still traps on absence.

This is not general aggregate support. Boolean arrays (including
`alloc_array<bool>`), all option-typed parameters, option-valued class and
record fields, trait and impl method option returns, record and nested option
payloads, and Boolean generic arguments remain rejected. At the G1.1
checkpoint, the SVM and LLVM lowering boundaries also rejected `option<bool>`
with that work assigned to dedicated follow-on slices. G1.1's complete
low-concurrency closure command was
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`. It passed
116/116 library tests; all 374 corpus subjects (80 verifies, 231 must-fail, 45
dynamic, 18 dynamic-fail) in 409.31s; the focused `option_bool` verification at
21/21 obligations across six functions and its dynamic subject at 1/1; LLVM CLI
6/6; the exact `VerifiedProgram` interpreter↔Clang differential at `-O0` and
`-O2` 1/1; and SVM differential 69/69. The randomized allocator,
grind-budget, LSP, and documentation gates were green. G1.1 is closed.

G1.2 carries the ordinary-function intersection of that source feature through
the formal SVM and its Rust lowerer. The Lean value plane now represents an
ordinary option recursively as `Val.opt : Option Val`; `some`, `none`,
`.is_some`, and `.value` therefore have one payload-generic relational and
executable semantics. Accessing a non-option is the machine's defined `undef`
outcome, while `.value` on `none` is the language trap `optionNone`. Canonical
differential observations preserve the established integer spellings
`opt none` and `opt some 7`, and add the unambiguous Boolean spellings
`opt some false` and `opt some true`.

The formal core is deliberately more uniform than the compiler boundary. Rust
lowering admits only G1.1's ordinary-function returns and locals, contextual
constructors, assignment and call-result transport, and accessors, with
concrete integer or Boolean option payloads. It does not introduce an option
parameter or storage ABI; Boolean arrays, option-valued fields, trait returns,
record/nested payloads, residual or Boolean generic arguments, classes and
method calls, and audited extern calls remain fail closed. LLVM remained the
next independent boundary at the G1.2 checkpoint.

G1.3 implements that LLVM boundary as the internal named type
`%sable.option.bool = type { i8, i8 }`: field zero is the tag and field one is
the canonicalized Boolean payload. `none` is the all-zero value; `some(false)`
and `some(true)` have tag one and payload zero or one. Internal Sable functions
may return and directly call through this value, and explicit/inferred locals
carry it through branches, loads, stores, assignment, and return. `.is_some`
tests the tag. `.value` first branches on absence and reaches trap kind 8 with
zero type metadata and operand payloads; only the success edge extracts and
canonicalizes the payload. The `ob` mangling component and named IR type remain
internal and versionable.

This is still the same narrow language slice. The LLVM emitter accepts no
option parameters, option-valued fields or trait methods, option entry or
extern ABI, residual generic forms, classes/method calls, or non-Boolean option
payloads. The combined G1.2/G1.3 closure command was
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`. It passed
129/129 library tests; all 374 corpus subjects (80 verifies, 231 must-fail, 45
dynamic, 18 dynamic-fail) in 414.80s; LLVM CLI 6/6, including the exact
zero-metadata/zero-payload kind-8 option-none trap followed by mandatory
`llvm.trap`; the 1/1 exact-`VerifiedProgram` interpreter↔Clang differential,
now looping over scalar, control-flow, arithmetic, and Boolean-option subjects
at both `-O0` and `-O2` (the option subject returns 42); and the SVM
differential at 76/76. Randomized allocator, grind-budget, LSP, and
documentation gates were green. G1.2 and G1.3 are closed.

G1.4a closes the first ordinary POD-record call and native-value slice.
Ordinary function calls may now take `bool` arguments: VC generation explicitly
reifies its proposition-valued symbolic Boolean into a Lean `Bool` at the call
boundary. Ordinary POD records may likewise cross parameters and
returns, with their nominal well-formedness facts restored at call results and
loop havoc; the interpreter and dynamic contract monitor exercise the same
transport. This widening is intentionally not inherited by class methods:
class-method record returns and Boolean/record trait signatures remain closed.

LLVM represents each supported root-owned integer-field POD declaration as an
internal named aggregate. Construction, projection, locals, branches, direct
internal parameters, calls, and returns lower as semantic record values. These
types deliberately ignore `#[layout]`/field-offset metadata, which describes
the separately modeled raw-cell geometry rather than an LLVM memory layout.
Imported records, extern/entry/public ABIs, pointer or Boolean fields, nested or
container records, and classes remain rejected. This is an internal lowering
contract, not a C ABI or a claim that general aggregate storage is complete.

The complete one-worker closure gate passed `cargo check`; 150/150 library
tests; all 382 corpus subjects (82 verifies, 235 must-fail, 47 dynamic, 18
dynamic-fail) in 218.30s; focused Boolean-call verification at 16/16 obligations
across ten functions and record-call verification at 13/13 across four
functions, with each dynamic subject at 1/1; LLVM CLI 6/6; and the 1/1 exact
`VerifiedProgram` interpreter↔Clang differential at `-O0` and `-O2`, now over
five subjects including POD records. SVM differential remained green at 76/76,
and its Rust lowerer additionally hardened semantic operand, scope, sealed-op,
record-geometry, and integer-array coherence at the public AST boundary; that
is not Boolean-array support. Randomized allocator, grind-budget, LSP, and
documentation gates were green. G1.4a is closed.

G1.4b admits only fresh owned-local `[bool]` values. Explicit and inferred
locals may be initialized from contextual literals or
`alloc_array<bool>(u64, bool)`, including empty arrays, then use `.len`, checked
index reads, element stores, loops, assertions, and contracts. Whole-array
transport remains closed: no Boolean-array parameters, returns, class/record
fields, borrows, exposure, whole-array rebinding, `for` index types, or generic
Boolean-array arguments are accepted.

Verification models these locals as `Sable.Seq Bool`. Symbolic program
Booleans are propositions, so literal/allocation/store values are explicitly
reified to Lean `Bool`; reads cross back as `get ... = true`. Loop havoc keeps
the Boolean sequence type and length relation without inventing integer element
range facts. The interpreter and monitor likewise carry separate typed integer
and Boolean arrays, including the payload of an empty array. Array equality is
monitorable within one payload domain; an integer/Boolean-array comparison is
unmonitorable rather than coerced. Indexing still has the ordinary proof
obligation and executable out-of-bounds trap.

At the G1.4b checkpoint this was a source-verification/interpreter slice, not
backend support: the Rust SVM lowerer, formal SVM, and LLVM emitter all rejected
Boolean arrays. No native storage or lifetime policy was implied. G1.5 widens
only the formal-machine boundary; native LLVM array lowering remains a later
independent stage.

G1.4b closed under
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture` with
171/171 library tests; all 394 corpus subjects (83 verifies, 244 must-fail, 48
dynamic, 19 dynamic-fail) in the all-target run's 208.73s corpus portion;
focused verification at 18/18 obligations across four functions; 2/2 dynamic
tests and the expected out-of-bounds failure; LLVM CLI 6/6; the 1/1
exact-`VerifiedProgram` interpreter↔Clang differential over five subjects at
`-O0` and `-O2`; and the unchanged SVM differential at 76/76. A separate
standalone corpus repeat was green in 195.71s. Randomized allocator,
grind-budget, LSP, and documentation gates were green. G1.4b is closed.

G1.5 implements the same owned-local intersection in the formal SVM. Machine
arrays are explicitly tagged as `ArrayVal.ints (Seq Int)` or
`ArrayVal.bools (Seq Bool)`, and `Val.arr` contains that tagged value. Length,
index, allocation, and store are payload-generic while remaining homogeneous;
the tag survives at length zero. An indexed read returns the corresponding
integer or Boolean scalar. A store of the wrong scalar domain is `undef`, and
that mismatch is decided before bounds: a wrong-domain write to an empty or
otherwise out-of-bounds array is `undef`, while a matching write traps with
`indexOOB`. Index and value evaluation retain their established left-to-right
precedence, and allocation evaluates length then initializer before
negative-length/OOM geometry.

The Rust bridge is deliberately narrower than the formal value. It admits only
a fresh owned-local Boolean array produced by `alloc_array<bool>` or a
contextual literal, then length/index/store uses; parameters, returns, fields,
borrows, exposure, whole-array rebinding, and other transport remain rejected.
A literal evaluates every element into compiler-reserved temporaries in source
order before allocating a false-filled Boolean array and applying ordered
stores. Thus an element trap wins over allocation/OOM. Literal expansion is
bounded by the SVM profile cap of 50,000,000 elements, and an empty literal
still allocates a Boolean-tagged empty value. Canonical observations retain the
existing `arr [...]` spelling, with lowercase `true`/`false` elements.

G1.5 closed under
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`.
`cargo check` and the full 22-target one-job Lake build were green; Rust library
tests passed 175/175; all 394 corpus subjects (83 verifies, 244 must-fail, 48
tests, 19 test-fails) passed in 266.78s; LLVM CLI passed 6/6 with Clang
required; the exact `VerifiedProgram`↔Clang O0/O2 differential passed 1/1 over
five subjects; and the SVM differential passed
86/86. `free_list_return_random`, grind-budget, LSP, and doc-tests
were green. G1.5 is closed.

The complete G0 gate ran with one Cargo job, one Sable test job, one Lean job,
and one Rust test thread. It passed 82/82 library tests, all 368 verifier,
must-fail, dynamic, and dynamic-failure corpus subjects (424.42s), LLVM CLI
6/6, the exact-`VerifiedProgram` interpreter↔Clang differential at both `-O0`
and `-O2`, and all 69/69 SVM differential subjects.

- **The bignum pillar** (M15–M16, the Tier-3 opener): arbitrary-precision `Nat` over base-2³² limbs with a normalizing representation invariant ([`corpus/verifies/bignum.sable`](corpus/verifies/bignum.sable)). The entire specification is one recursive ghost valuation, `natVal`, and one line per operation: `cmp` decides the order, `add`/`sub`/`mul` post `natVal result.limbs = natVal a.limbs ⊕ natVal b.limbs`, `div`/`rem` post `… = natVal a.limbs / natVal b.limbs` against Lean's own Euclidean division — with division built *compositionally* (double-and-subtract riding the contracts of the other verified ops, closed by one uniqueness lemma) — and `gcd` is Euclid in fifteen lines whose spec is kernel-check-proven to agree with Lean core's `Int.gcd`. **255 obligations across 10 functions, 73 hand discharges, zero escapes**, every clause monitored dynamically — the first benchmark where the mathematics itself was the test.
- **The verified free-list allocator** (M41, ADR 0037–0052): releasable system roots fold into an affine aggregate; first-fit allocation returns an exact mandatory `BlockLease`; public return rejects the wrong allocator, repeated use, or substituted subregion metadata; and predecessor/successor coalescing clears real in-band headers and proves exact span joins ([`corpus/verifies/free_list_return.sable`](corpus/verifies/free_list_return.sable)). Six branch fixtures and a deterministic 144-return reference-model comparison exercise the runtime policy, while final destruction still requires the exact complete root authority. U10's sound loop audit forced the traversal/search proofs to state their restored resource frame explicitly; the walk, insert-location, and first-fit pairs are green at 33/33, 13/13, and 22/22 obligations respectively. The complete serial corpus is green in 297.65s, and the full serial Rust suite is green.
- **Generic aggregate authority** (M42, ADR 0053): `ResourceMap<u64, PointsTo<u64>>` is one affine token over a pure partial-map view. Sealed take/put move exact typed-cell permissions without exposing separation logic; a 22-obligation wrapper-call round trip preserves both values and pointer identity through reverse-order extraction, then reconstructs and releases the original root ([`corpus/verifies/resource_map.sable`](corpus/verifies/resource_map.sable)).
- **Typed intrusive structures** (M43, ADRs 0054–0056): explicitly laid-out POD records support typed raw pointers and nullable raw links without acquiring a byte representation. Record alignment must dominate every field alignment as well as each relative offset, so an aligned record base really aligns every field. A two-node intrusive doubly linked list stores real `IntrusiveNode` values in one arena, moves exact node permissions through `ResourceMap<u64, PointsTo<IntrusiveNode>>`, traverses and unlinks through the stored pointers, then reconstructs and releases the complete root—34 obligations, zero escapes ([`corpus/verifies/intrusive_list.sable`](corpus/verifies/intrusive_list.sable)). The relational SVM, proved evaluator, and Rust interpreter now triangulate the record-cell lifecycle too: 47 direct machine guards and 59 cross-engine subjects cover success, tag/state failures, interior-byte exclusion, and typed overlap.
- **The first formal device profile** (M44, ADR 0057): `resource Uart` is affine authority for the narrow `uart-poll-v1` model. The signature-level authority budget is one: a function, method, initializer, or template may declare at most one UART parameter; UART trait signatures and owned or borrowed UART class fields remain outside this singleton-view slice. `uart_status` and `uart_write` are available only in `unsafe`, but remain fully checked; a write must follow an observed ready status, appends to an ordered MMIO trace, and clears readiness. Only `test_` functions may mint the capability with `test_uart`. [`corpus/verifies/uart.sable`](corpus/verifies/uart.sable) verifies 16/16 obligations, and 4/4 dynamic fixtures cover immediate, delayed, never-ready, and direct erased-resource-argument selection. The Lean `SVMUart` wrapper preserves byte-for-byte bare-core observations while adding profile state, oracle cursor, and trace when selected; all 69/69 Rust/Lean differential subjects agree. Generated artifacts record the formal profile id/hash and used intrinsics as a kernel-checked semantic dependency, not an extern assumption. Each check also binds its generated bytes and exact resolved Sable import graph to one immutable `proof-env-v2` snapshot, so neither the batch checker nor daemon can silently mix source, profile, or prelude versions. The explicit extern resource whitelist excludes `Uart`.
- **The pipeline** (M0–M2): contracts, loops with invariants/variants, `for`/`range` sugar, arrays (`&[T]`, `&mut [T]` with stores and `old` state), `option`, recursion with measures, ghost definitions, `discharge NAME by <tactics>` for the obligations automation can't reach, and inline `/// assert` stepping-stones that turn one proved fact into a hypothesis for everything downstream. Headline artifacts: **in-place insertion sort verified against the full `sorted ∧ permutation` spec**, binary search, gcd. The multiset library lives in [`lean/Sable/Perm.lean`](lean/Sable/Perm.lean), core-only.
- **The assurance ladder** (M3): `defer` (sound runtime trap) and `assume #[audit(reason := "...")]` (audited axiom), tallied in every build report; `status: fully verified` appears only at zero of both.
- **Dynamic checking** (M3): `sable test` executes tests with trap semantics and every monitorable contract — pres, posts, invariants, variant decrease — checked at runtime; variants compare the pre-condition loop-head value with the post-body value, including the final iteration. Resource values erase, but their argument expressions still execute left-to-right. The cheapest way to find a wrong spec is to run it.
- **Editor support** (M4): the LSP serves diagnostics (fast pass on every edit, full verification on save), contract-on-hover, folding, and semantic tokens that dim evidence lines. Setup for Neovim and VS Code in [`editors/`](editors/README.md).
- **Classes with invariants** (M5): `BoundedStack` from the design doc verifies with every obligation automatic — the class invariant is an obligation at init/`&mut`-method exits and an assumption at entries, checked dynamically too (including at RAII drop).
- **The Tier-0 benchmarks** (M6): quicksort (frame conditions across recursion), the merge kernel (count-based multiset spec), hex and varint codecs with kernel-checked round-trip theorems — plus the first slice of the SVM formalization ([`lean/Sable/SVM.lean`](lean/Sable/SVM.lean)) whose design-audit findings live in [`docs/notes/svm-draft.md`](docs/notes/svm-draft.md).
- **Generics v1 and `Vec<T>`** (M7): explicit instantiation over the integer types, expanded by monomorphization before any verification stage runs (ADR 0006). Headline artifact: a growable **`Vec<T>` with amortized-doubling `push` verified with its full frame condition across the reallocation-and-copy path** ([`corpus/verifies/vec.sable`](corpus/verifies/vec.sable)) — the capacity invariant makes doubling overflow-free by construction, and the frame posts are also *monitored* at runtime, not just proven.
- **The UTF-8 codec** (M9, Tier 2 opener): RFC 3629 encoder + validating decoder (overlongs, surrogates, the 0x10FFFF ceiling) with a **kernel-checked roundtrip** and **buffer-level validation proven against a recursive decomposability predicate** ([`corpus/verifies/utf8.sable`](corpus/verifies/utf8.sable)) — 205 obligations, 7 hand discharges; the decoder provably never rejects canonical bytes.
- **`const` + immutability** (M22, ADR 0016): named compile-time constants usable in contracts (`pre b.len ≤ MAX_BYTES`), and **locals are immutable unless declared `mut`** — assignment, stores, `&mut` borrows, and `&mut` methods all require the marker, so every unmarked local is a proven-constant read.
- **String v1** (M21, ADR 0015): `var s = "héllo";` — a verified UTF-8 string as a *library class*, not a builtin: owned bytes under a monitorable validity invariant (`validScan`, kernel-tied to the RFC 3629 decomposability predicate), literals whose validity obligations **discharge automatically** (conditional step lemmas unfold concrete bytes under plain simp), and byte-lexicographic comparison with full iff contracts bound through `operator cmp`.
- **Byte-string literals** (M20, ADR 0014): `b"{\"key\": true}"` is a `[u8]` literal of its UTF-8 bytes (escapes `\n \r \t \0 \\ \" \xNN`; raw non-ASCII text contributes its UTF-8 bytes), replacing the decimal byte arrays the codec tests used to carry. Bare `"..."` is reserved for the future `String` type so no literal ever changes meaning.
- **Modules v1** (M19, ADR 0013): `use bignum;` — file-based, Rust-flavored imports (module = file, resolved against the importing file's directory then `-M` paths), transitive and cycle-checked, with diagnostics that always point into the *right* file. Linking is source-level, so every stage below the loader is module-oblivious; the dynamic-test corpus now imports its subjects instead of carrying 700-line copies.
- **Operator bindings** (M18, ADR 0012): `operator + = add;` binds operators to contracted functions — bignum arithmetic reads `q = q + m; r = r - d;` under `while (r >= b)`, and every operator use carries the bound function's full contract (the program `+` and the proof `+` never meet, so the sugar is purely front-end).
- **First-class class values** (M14, ADR 0010): shared class borrows, class returns, field reads, and (forced by division) class-local reassignment with move-in semantics — `fn union_of(&Range a, &Range b) -> Range` verifies with contracts written directly over class structures (`result.lo ≤ a.lo`), borrowed arguments carrying their invariants in and returned values carrying them out as checked obligations. The bignum surface, delivered exactly when the pillar demanded it.
- **Concepts** (M13, ADR 0009): type preconditions on templates — `/// requires T.max ≥ 100` — with **every generic declaration — functions, classes, trait-bounded templates — verified once against an abstract type model** (trait bounds become abstract spec-function binders) and instantiations owing only the (automatic) precondition facts: `HashMap`'s 27 per-instance discharges are one template set. C++ concepts check syntax; Sable concepts check lemmas. Plus `#[label(name)]`: stable semantic names for obligations and their hypotheses.
- **The JSON parser** (M12): structural validation against the full recursive value grammar ([`corpus/verifies/json_parse.sable`](corpus/verifies/json_parse.sable)) — the grammar is one mode-encoded well-founded ghost predicate with guarded recursion, the parser one self-recursive function with interior loops, and `json_valid` returning true is a kernel-checked proof the buffer is a JSON value: 270 obligations, the largest verified artifact in the corpus.
- **Option accessors** (M11, ADR 0008): `option<T>` locals with `.is_some`/`.value` — no pattern matching in the program language, as a standing principle. `.value` carries a someness obligation (junk-on-none in the model, exactly like `Seq.get` off-range; a trap in `sable test`), and the prelude makes the identical postfix syntax elaborate in clause text: `post result.is_some → result.value = x + 1`.
- **The JSON tokenizer** (M10): the RFC 8259 lexical grammar as ghost predicates — recursive string bodies with variable-width escapes, ∃-split numbers, a guarded-recursion token-stream predicate — with scanners proven against them ([`corpus/verifies/json_lex.sable`](corpus/verifies/json_lex.sable)): 175 obligations, 11 discharges; `json_lex_ok` returning true is a kernel-checked proof the buffer tokenizes.
- **Traits v1 and the hash map** (M8): law-carrying bounds (ADR 0007) — a trait pairs a spec-level function with a program method contracted to compute it, so generic specs can *apply* `K::hash` and get determinism; impls are verified against the law, not trusted. Headline artifact: **`HashMap<K: Hashable, V>` with open addressing verified against the linear-probing contract** ([`corpus/verifies/hashmap.sable`](corpus/verifies/hashmap.sable)) — `get` returning `none` *proves* the key is absent from the whole table, cyclic probing stays in omega's fragment by subtraction instead of variable modulus, and every clause (including the probe-path invariant and existential posts) is monitored dynamically at zero skips.

There is **no SMT solver in the trusted base**: routine obligations are closed by an automation portfolio inside Lean (`omega`, `simp`, and a heartbeat-budgeted `grind` whose expensive successes produce a warning with a minimized-proof suggestion, ADR 0011 — see [`lean/Sable/Auto.lean`](lean/Sable/Auto.lean)), and every proof, automated or hand-written, is checked by the Lean kernel. Division is Euclidean, matching Lean's `/` exactly (ADR 0004). The corpus (`corpus/`) is the compiler's conscience: programs that must verify, programs that must fail with a named diagnostic, dynamic tests that must pass with zero unmonitorable clauses, and dynamic tests that must be caught.

## Design pillars

1. **No undefined behavior.** Every program's meaning is defined by a formal machine model; anything that would be UB in C is either statically excluded by a proof obligation or has defined trap semantics.
2. **A formal machine model is the axiom base.** The Sable Virtual Machine, formalized in Lean, is the language's meaning — a semantic definition, not a runtime. The trusted base shrinks in explicit, honestly labeled stages (design §10.1); today's stage trusts the Rust VC generator and the Lean kernel, nothing else.
3. **Ownership before logic.** Rust-style unique ownership with borrowing, simplified. Because mutable aliasing is impossible in safe code, the verifier reasons about values, not heaps; framing is a type-system fact.
4. **Total verification, visible exceptions.** No build modes. An undischarged obligation is a compile error. The only ways past one are written in the source and tallied in every build: `defer` (sound runtime trap) and `assume` (audited axiom). Zero of both is *fully verified* — a property of code, not of build configuration.

Architecture in one sentence: the Rust compiler (`compiler/`) owns the program language, Lean owns the proof language, and verification is Lean-file generation — see [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) and the ADRs in [`docs/decisions/`](docs/decisions/).

## Where this is headed

The roadmap is benchmark-driven: each goal stresses one design axis, has a spec statable in a few lines, and has precedent in the verification literature bounding its effort. The spine: sorting and codecs → `Vec` and a hash map (forcing the generics design) → UTF-8 / JSON / DEFLATE / crypto kernels → a verified allocator (forcing the `unsafe` design) → the two pillars: a **GMP-style bignum library** verified to implement ℤ (its core arithmetic — through multiplication and division — is done), and the **SVM interpreter written and verified in Sable itself**. With unsafe Sable v1, scalar LLVM v0, G0, **G1.0–G1.5 closed**, the first `option<bool>` slice reaches verification, interpretation, the formal SVM, and native LLVM, root-owned integer-field POD records cross ordinary verified/interpreted/native calls internally, and owned-local Boolean arrays now reach verification, interpretation, dynamic monitoring, and the formal SVM differential. Native lowering remains a later independent stage before broader affine options, generic slots/`Vec`, and `HashMap`. Minimal formatting/`String`, `Result`-shaped errors, real module namespaces/mangling, and domain-forced floating point follow provisionally; [`docs/PLAN.md`](docs/PLAN.md#post-u10-usability-sequence) records the intended boundaries. The long-running horizon is a formally verified OS kernel; the metatheory track (mechanized soundness of the verifier) runs alongside once the language surface stabilizes.

## Provenance

The design and implementation are being developed in conversation with Claude (Anthropic). Everything here is subject to revision as real code generates friction — the design documents already carry corrections that the compiler forced (the doc's own `div_round_up` example had an overflow bug; the corpus keeps it as a must-fail).

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT license](LICENSE-MIT), at your option. Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
