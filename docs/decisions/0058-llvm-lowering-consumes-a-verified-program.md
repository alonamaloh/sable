# ADR 0058 — LLVM lowering consumes the verified program

**Decided and implemented 2026-08-12; scalar v0 complete. G1.3 Boolean-option
and G1.4a POD-record extensions implemented and closed 2026-08-13; G1.5's
formal Boolean-array extension is closed. G1.6's owned-local native-array
extension is implemented and closed 2026-08-13; ADR 0059 pins its runtime and
lifetime contract. N0–N4's exact native-`Nat` foundation, fixed-owner,
internal-return, and arithmetic-through-division-and-gcd extensions are
closed.** Unsafe
Sable v1 had a defensible formal stopping point but no native-code path. This
backend makes verified
programs in its deliberately narrow runtime subset runnable without making LLVM
part of the verifier or introducing a second, subtly different front-end
pipeline.

## Decision

The compiler has a handwritten textual LLVM IR emitter, selected with:

```text
sable build --emit-llvm [--entry NAME] [-o FILE|-] [-M PATH] file.sable
```

The emitter has no `libLLVM` dependency. It writes ordinary LLVM IR which a
separately installed LLVM toolchain may assemble or compile, but emitting IR
itself requires no LLVM installation and is not tied to one libLLVM ABI. The
initial document is target-neutral: it does not promise a target triple, data
layout, object format, or C ABI.

Lowering may consume only a `VerifiedProgram`: the exact checked and
monomorphized `Program` whose generated obligations have just succeeded in
Lean, together with the verification metadata that identifies that result.
This is a capability boundary in the Rust API, not a new proof claim. The
backend must not reopen the source file, resolve modules again, reparse, rerun
monomorphization, or accept an arbitrary `Program`. It retains the exact
`Prepared.program` object used for VC generation, while its metadata binds the
exact source-graph bytes. A later optimization pipeline may transform that
program only through separately defined lowering steps; it may not obtain
authority by constructing `VerifiedProgram` directly.

## Initial scalar executable subset

Version 0 deliberately starts with the scalar core:

- all existing fixed-width integer types, `bool`, and `unit`;
- scalar parameters, locals, returns, and nonrecursive Sable calls;
- declarations, assignments, expression statements, `if`, `while`, and
  `return`;
- short-circuit Boolean operators, explicit `widen`/`narrow`, comparisons,
  and checked integer arithmetic;
- `unsafe` blocks whose contents are otherwise in this scalar subset; the
  audit marker itself emits no runtime instruction.

The first emitter rejects reachable arrays, options, classes, records,
borrows, raw pointers or raw operations, resources, device operations,
foreign calls, deferred obligations, and recursion. It does not emit dynamic
`test_` entry points. Rejection is a source diagnostic, never a panic, guessed
lowering, silent erasure, or implicit fallback to the interpreter.

`--entry NAME` selects a production function and its transitive call closure.
Unsupported declarations outside that closure do not prevent this focused
build. Without `--entry`, whole-module mode considers every production
declaration and rejects the module if any of them is outside the supported
subset. This makes the two policies explicit: entry mode is useful while the
backend grows, while whole-module success means the backend accepted the whole
production module. Recursion is rejected over the same selected call graph.

## Preserving Sable arithmetic

LLVM's convenient undefined/poison-producing flags are not Sable semantics.
The backend therefore emits no `nsw`, `nuw`, `exact`, `inbounds`, or
`llvm.assume` as a substitute for a Sable proof. Checked signed and unsigned addition,
subtraction, and multiplication use the matching LLVM overflow intrinsics and
branch to a trap on the overflow bit; signed negation uses signed-subtract-with-
overflow from zero. Division and remainder guard zero, and signed division
additionally guards `min / -1`, before executing LLVM's instruction.

Sable signed division is Euclidean; LLVM signed division truncates toward
zero. The emitted control flow corrects LLVM's quotient and remainder when the
truncating remainder is negative, rather than changing the source-language
meaning. The representable Sable result `min % -1 = 0` bypasses LLVM's invalid
`srem min, -1` pair entirely. Widening uses the source signedness to choose
`sext` or `zext`; narrowing extends the source value to `i128`, performs an
explicit signed range check there, and truncates only on the success edge.
Boolean short circuiting is control flow with merge values, so an unevaluated
operand cannot trap or produce effects.

Runtime failures use a versioned trap hook plus an internal `noreturn` helper:

```text
void @__sable_rt_trap_v1(i32 kind, i32 type_info,
                         i64 lhs_bits, i64 rhs_bits)
```

The internal helper invokes the weak hook and then unconditionally invokes
`llvm.trap`; a returning replacement hook cannot suppress the failure.
Embedding code may replace the hook for diagnostics. This interface describes
failures, not a stable calling convention for Sable functions.

The `v1` numeric schema is fixed independently of Rust enum layout. Failure
`kind` values are 1 add overflow, 2 subtract overflow, 3 multiply overflow,
4 negation overflow, 5 division/remainder by zero, 6 signed division overflow,
7 narrowing out of range, 8 option value of none, 9 owned-array allocation
failure, and 10 array index out of bounds. Kind 8 has zero
`type_info`, `lhs_bits`, and `rhs_bits`: there is no integer operation to
describe. Array kinds likewise use zero `type_info`: kind 9 carries
`lhs_bits = len`, `rhs_bits = 0`, and kind 10 carries `lhs_bits = index`,
`rhs_bits = len`. Integer type codes are 1 through 8 for
`u8`, `u16`, `u32`, `u64`, `i8`, `i16`, `i32`, and `i64`, respectively.
`type_info` packs the result/destination code in bits 0–7, the left/source code
in bits 8–15, and the optional right code in bits 16–23. Operand payloads are
the original source-width bit patterns zero-extended to `i64` (or unchanged for
64-bit values); signed interpretation therefore comes from the type code, not
from sign extension of the payload.

## Names and output

Backend symbols use an unambiguous length-prefixed internal mangling. The
scheme is intentionally internal and versionable; ADR 0058 does not declare a
stable public ABI, and the present flat source-module merge does not become a
real namespace merely because LLVM needs unique identifiers. Real module
namespacing remains a later language milestone.

File output is atomic: generation completes and validates before a temporary
file in the destination directory replaces the requested path. A failed build
must leave an existing output untouched and must not leave a partial `.ll`
file. `-o -` streams a completed in-memory document to standard output.

## Evidence and staging

Emitter unit tests inspect deterministic IR and source diagnostics. Where
`clang` is available, direct native fixtures compile and run at `-O0` and
`-O2`; the closure gate compares their successful outcomes with the interpreter
and directly observes trap-ABI behavior. These end-to-end checks are optional
for a normal developer environment unless explicitly required (for example by
`SABLE_REQUIRE_CLANG=1`); the ordinary emitter suite never acquires an LLVM
tool dependency.

Scalar v0 was delivered in three slices: the opaque `VerifiedProgram`
boundary, root-bound entry selection, CLI, atomic output, provenance comments,
strict scalar lowering, and a real CFG for branches, loops, comparisons, and
short circuiting. Local allocation is entry-hoisted while initialization stays
at its source point. The third slice adds checked signed/unsigned arithmetic,
signed negation, guarded division/remainder with Euclidean correction, explicit
widening/narrowing, and the versioned weak trap hook plus mandatory
`llvm.trap`. Its structural tests pin guard dominance, the `min % -1` bypass,
raw trap payloads, and the absence of poison promises.

Scalar v0's complete low-concurrency command
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture` is green.
It includes 26/26 library tests, 6/6 verified LLVM CLI tests, and a 1/1 native
differential test comparing the exact `VerifiedProgram` interpreter outcome
with Clang `-O0` and `-O2` for scalar, control-flow, and arithmetic subjects.
The matrix covers negative divisors, the `MIN % -1` bypass, conversion bounds,
and a loop condition designed to detect accidental hoisting out of its header.
Verification failure and audited-assumption rejection leave existing output
untouched.

The scalar native trap fixture exercises its seven published kinds at both
optimization levels, with exact kind, type-info, and raw-operand payloads. Its
strong hook returns, and the following `llvm.trap` still terminates each
process. The same serial regression kept the SVM Rust/Lean differential green
at 69/69, completed the full verifier/dynamic corpus in 220.78s, and passed the
randomized allocator, grind-budget, LSP, and documentation tests. That closes
the scalar v0 milestone. At that checkpoint it did not extend the accepted
subset to aggregates; G1.3 subsequently adds the one internal Boolean-option
representation below without declaring an aggregate ABI.

## G1.3 amendment: internal Boolean options

The first aggregate backend slice is exactly G1.1's ordinary-function
`option<bool>` intersection. LLVM spells the value
`%sable.option.bool = type { i8, i8 }`: the first byte is a presence tag and
the second is a canonical Boolean payload. `none` is `zeroinitializer`, so both
bytes are zero. `some(false)` and `some(true)` set the tag to one and store
payload zero or one after extending the checked `i1` Boolean. The named type is
emitted once, deterministically before function definitions, and the internal
name mangling uses the versionable component `ob`.

Internal Sable functions may return this value and direct calls may transport
it. Explicit and inferred locals use aggregate slots, loads, and stores through
branches and assignment. `.is_some` compares the tag with zero. `.value`
extracts the tag, branches to the common failure helper on absence, and extracts
and truncates the payload only in the dominated success block. The failure is
kind 8 with exact zero type metadata and operand payloads; the weak diagnostic
hook may return, but the internal helper still executes mandatory `llvm.trap`.

This is not a public option ABI. Option parameters and entry points remain
rejected, audited externs cannot return or consume the value, and option-valued
fields or trait methods, classes and method calls, residual generic metadata or
type arguments, and all non-Boolean option payloads remain outside the emitter.
The internal named type and `ob` spelling may change before any stable Sable or
C ABI exists.

The combined G1.2/G1.3 closure command was
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`. It passed
129/129 library tests; all 374 corpus subjects (80 verifies, 231 must-fail, 45
dynamic, 18 dynamic-fail) in 414.80s; LLVM CLI 6/6, with the exact
zero-metadata/zero-payload kind-8 trap and mandatory `llvm.trap`; the 1/1 exact
`VerifiedProgram` interpreter↔Clang differential, now looping over scalar,
control-flow, arithmetic, and Boolean-option subjects at both `-O0` and `-O2`
and observing 42 from the option subject; SVM differential 76/76; and the
randomized allocator, grind-budget, LSP, and documentation gates. G1.2 and
G1.3 are closed.

## G1.4a amendment: internal semantic POD records

G1.4a's backend aggregate is a root-owned POD record whose fields are all
fixed-width integers. Each supported declaration has an internal named LLVM
aggregate, and internal functions may construct it, project its fields, keep it
in local slots across branches, and transport it through parameters, direct
calls, and returns. This follows the checker/VCgen/interpreter widening that
also admits ordinary record arguments and results. Those formal call results
carry the nominal record's `wf` fact, including after loop havoc. Ordinary
Boolean call arguments cross VC generation through an explicit Prop-to-`Bool`
reification rather than treating propositions as machine values. Class-method
record returns and Boolean/record trait signatures remain rejected.

The native aggregate is a semantic value, not the record's raw-cell layout.
The emitter therefore does not apply `#[layout]` or field-offset metadata to
the LLVM type; that metadata belongs to the separately modeled raw-storage
geometry. No imported record, pointer or Boolean field, nested or container
record, class, or record-valued extern/entry/public ABI is accepted. The named
type and its mangling are internal and versionable. In particular this
amendment does not declare a C-compatible record layout, a cross-module Sable
ABI, or general aggregate/generic-class support.

The complete one-worker closure passed `cargo check`; 150/150 library tests;
all 382 corpus subjects (82 verifies, 235 must-fail, 47 dynamic, 18
dynamic-fail) in 218.30s; focused Boolean-call verification at 16/16 obligations
across ten functions and record-call verification at 13/13 across four
functions, with each dynamic subject at 1/1; LLVM CLI 6/6; and the 1/1 exact
`VerifiedProgram` interpreter↔Clang differential at `-O0` and `-O2`, now over
five subjects including POD records. The SVM differential remained green at
76/76; separate public-AST hardening covered semantic operands, source scope,
sealed operations, record geometry, and existing integer arrays, not Boolean
arrays. Randomized allocator, grind-budget, LSP, and documentation gates were
green. G1.4a is closed.

## G1.4b boundary: source-local Boolean arrays are not native arrays

G1.4b widens checking, VC generation, interpretation, and dynamic monitoring
for fresh owned-local `[bool]` values. It does not amend the LLVM representation
decision. The emitter rejects a reachable Boolean-array declaration and every
expression that would carry the value, even though the input is an otherwise
valid `VerifiedProgram`. A focused public-boundary regression pins this local
rejection alongside the existing parameter, entry, extern, field, and payload
fences.

This separation is intentional. The source slice has no parameter or return
transport, field storage, borrow, exposure, whole-array rebinding, or generic
Boolean-array instance. Choosing an LLVM element representation now would not
answer allocation, ownership, lifetime, trap, name-mangling, or future ABI
questions. A dedicated native-array stage must make those choices and add an
interpreter/native differential before ADR 0058 admits the type.

G1.4b closed under `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1
--nocapture`: 171/171 library tests; all 394 corpus subjects (83 verifies, 244
must-fail, 48 dynamic, 19 dynamic-fail) with 208.73s in the all-target corpus
portion; focused Boolean-array verification at 18/18 obligations across four
functions; 2/2 dynamic tests and the expected out-of-bounds trap; LLVM CLI 6/6;
the 1/1 exact-`VerifiedProgram` interpreter↔Clang differential over five
subjects at `-O0` and `-O2`; and the unchanged SVM differential at 76/76. A
standalone corpus repeat was green in 195.71s; randomized allocator,
grind-budget, LSP, and documentation gates were green. This closes G1.4b but
claims no LLVM Boolean-array support. G1.5 has since closed the formal SVM
semantics; G1.6 and ADR 0059 subsequently supply the separate native stage.

## G1.5 boundary: formal arrays are not LLVM arrays

G1.5 adds tagged `ArrayVal.ints` and `ArrayVal.bools` payloads to the formal SVM
and admits the already-authorized owned-local Boolean-array slice to the Rust
differential bridge. At that checkpoint it did not amend this ADR's
representation decision: the LLVM emitter still rejected Boolean arrays,
including empty values whose formal machine tag is observable. No native
allocation, storage, lifetime, trap, or ABI policy followed from the formal
value alone.

The Rust bridge likewise stays smaller than a native aggregate ABI: only a
fresh owned local from `alloc_array<bool>` or a contextual literal, followed by
index, length, and store operations, is admitted. Literal elements are first
evaluated into reserved temporaries in source order, before false-fill
allocation and ordered stores, so an element trap precedes allocation/OOM.
Expansion is capped at 50,000,000 elements and an empty literal retains its
Boolean payload tag.

G1.5 closed under `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1
--nocapture`. `cargo check` and the full 22-target one-job Lake build were
green; Rust library tests passed 175/175; all 394 corpus subjects (83 verifies,
244 must-fail, 48 tests, 19 test-fails) passed in 266.78s; LLVM CLI passed 6/6
with required Clang; the exact `VerifiedProgram`↔Clang differential passed 1/1
over five subjects at `-O0` and `-O2`; and the exact Rust↔Lean SVM
differential passed 86/86. `free_list_return_random`, grind-budget, LSP, and
doc-tests were green. This closes G1.5 while the LLVM Boolean-array boundary
remained closed; G1.6 is the separately reviewed widening below.

## G1.6 amendment: internal owned-local Boolean arrays

G1.6 admits exactly the source intersection established in G1.4b and carried
through the formal machine in G1.5. A fresh owned-local `[bool]` may be
initialized by `alloc_array<bool>` or a contextual literal and then used for
length, checked reads, and element stores. LLVM represents the local as
`%sable.array.bool = type { ptr, i64 }`: opaque data pointer followed by `u64`
length. Each element is one canonical zero/one `i8` byte, never packed `i1`
storage. The internal descriptor and checked source type distinguish the
Boolean payload even when zero length is represented by a null pointer.

Storage is deliberately outside the generated module. Nonempty arrays use the
external versioned hooks `__sable_rt_array_alloc_v1(i64 bytes)` and
`__sable_rt_array_free_v1(ptr)`; a zero-length array calls neither. The
optional hosted shim `runtime/hosted/sable_rt_v1.c` checks that the fixed-width
byte count fits `size_t` and then uses the C allocator. LLVM output never names
`malloc` or `free`, and no weak allocator default is embedded in a module.

Evaluation order is preserved explicitly. Allocation evaluates length and
then the Boolean initializer before checking the 50,000,000-element native
profile cap and the hook result. A literal evaluates all elements
left-to-right before allocating, then writes their canonical bytes in order.
Store evaluates index and then value, performs an unsigned bounds check, and
only afterward forms a non-`inbounds` address and writes; read also guards
before address and load. Exceeding the cap or receiving null reports kind 9
with `(type_info, lhs_bits, rhs_bits) = (0, len, 0)`. An out-of-bounds read or
write reports kind 10 with `(0, index, len)`. The versioned observer is still
followed unconditionally by `llvm.trap`.

The new ownership substrate is lexical. Function bodies, `if` arms, and each
`while` iteration are cleanup scopes. Normal exits destroy owned arrays in
reverse declaration order; loop cleanup runs before the backedge. A return
evaluates its expression first and then unwinds active scopes inner-to-outer.
`unsafe` remains an open marker whose declarations belong to the enclosing
scope. Trap edges do not run cleanup. This mirrors the interpreter rather than
assuming host-language exception unwinding.

This is not an array transport or public ABI. Boolean-array parameters,
returns, fields, borrows, exposure, whole-array rebinding or movement, call
transport, extern/public positions, generic or option containment, and
discarded array temporaries remain rejected. Integer arrays are independently
outside the native slice. Internal `{ ptr, i64 }` spelling and runtime-hook
contract therefore authorize no cross-module or C-compatible Sable array
layout.

The lifetime audit also closed a pre-existing integer-array ownership bug.
Array-field assignment is a special consuming boundary because ordinary
whole-array reads are forbidden; it now explicitly checks whether a named
source was already moved before stamping its contextual type. Interpreter
ownership transfer now takes named array sources, and lexical/frame drops
remove owned-array places. The regression that moves one integer array into two
fields requires `array.use_after_move`, bringing the corpus inventory to 395
subjects (83 verifies, 245 must-fail, 48 tests, 19 test-fails).

G1.6 closed under `CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1
SABLE_LEAN_JOBS=1 SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1
--nocapture`. `cargo check` and the standalone 22-target one-job Lake build
were green; Rust library tests passed 185/185 and LLVM units 26/26; all 395
corpus subjects (83 verifies, 245 must-fail, 48 tests, 19 test-fails) passed in
192.76s; LLVM CLI passed 7/7, including the strong-hook fixture at Clang `-O0`
and `-O2`; the exact interpreter/native differential passed 1/1 over six
subjects at both levels; and SVM differential remained 86/86. Randomized
allocator, grind-budget, LSP, documentation, diff-check, and static-audit gates
were green. G1.6 is closed. ADR 0059 is the detailed representation, runtime,
and lifetime decision.

## N0 amendment: exact local `u32` arrays and internal borrows

N0 is closed. It admits fresh owned local `[u32]` values from a contextual
literal or `alloc_array<u32>`, length, checked
index reads, and stores. The internal descriptor is
`%sable.array.u32 = type { ptr, i64 }`. Nonempty allocation uses the existing
v1 hooks with a byte request of `len * 4`; the descriptor and trap observer
continue to carry logical element counts. The 50,000,000-element cap makes the
scale bounded in the native profile. Zero length remains the complete null/zero
descriptor and bypasses both hooks.

The hook is still specified as byte storage. It makes no `u32`-alignment
promise, so every typed element load and store is emitted with explicit
`align 1`; N0 does not strengthen an existing runtime interface by inference
from a hosted allocator. Address formation remains non-`inbounds`. OOM uses
kind 9 with `(0, len, 0)`, whether the profile cap or a null hook result causes
the failure; OOB uses kind 10 with `(0, index, len)`. Trap edges do not unwind.

Internal ordinary functions may take `&[u32]` and `&mut [u32]`. Calls must
retain the exact explicit named borrow node with checked matching mutability;
overlapping mutable aliases are rejected. These parameters are non-owning and
never enter cleanup. Owned caller locals retain the established reverse
declaration/scope cleanup across branches, loop iterations, and early returns.

This does not define an array ABI. Owned-array parameters or returns,
array-valued entries, fields, classes, methods, externs, public/cross-module
transport, Boolean borrows, other integer widths, whole-array movement or
rebinding, generic/option containment, and exposure remain rejected. Existing
VC generation, interpreter semantics, and formal tagged integer-array values
already cover the source behavior, so N0 changes no Lean proof model.

N0 closed under the exact one-worker command
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`.
`cargo check` was green; focused LLVM units passed 31/31; Rust library tests
passed 215/215; and all 416 recursive corpus files (84 verifies, 263 must-fail,
49 tests, 20 test-fails) passed in 213.51s. LLVM CLI passed 9/9; the exact
interpreter/native differential passed 1/1 over eight subjects at Clang `-O0`
and `-O2`; and SVM differential remained 92/92. Randomized allocator,
grind-budget, LSP, documentation, rustfmt, diff-check, and static-audit gates
were green.

## N1a amendment: fixed-owner `Nat` construction and shared comparison

N1a is closed. It admits one concrete class representation:
`%sable.class.<id> = type { %sable.array.u32 }`, for a class with exactly one
owned `[u32]` field, no methods, and an explicit empty destructor. A direct
constructor initializes a final immutable stack owner through an internal
destination-pointer initializer; constructor symbols include nominal class
identity and remain module-internal. Initializer validation requires the field
to receive fresh array storage exactly once on every path before element stores.
Normal reverse lexical cleanup frees the nested allocation, while traps retain
the established no-unwind behavior.

Internal ordinary functions may accept shared `&Nat` parameters as non-owning
pointers. Call sites retain the exact typed, fieldless named borrow, and class
field length/index operations reuse N0's logical lengths, bounds traps, and
explicit `align 1` limb accesses. The checker records `Expr.ty` on successful
class, resource, and field borrows so LLVM continues to revalidate a checked
node rather than infer backend types.

This exact slice compiles the real imported `Nat::from_prefix` and `cmp`.
Mutable owners, reassignment, moves, returns, owned class parameters, methods,
mutable class borrows, multiple or nested fields, generic classes, nonempty
destructors, extern transport, and public/cross-module class ABIs remain
rejected. N1a closed under the standard one-worker command: `cargo check` and
rustfmt were green; LLVM units passed 33/33; library tests 217/217; all 417
corpus subjects passed (85 verifies, 263 must-fail, 49 tests, 20 test-fails);
LLVM CLI passed 9/9; the exact interpreter/native differential agreed over nine
subjects at Clang `-O0` and `-O2`; and SVM remained 92/92. Randomized allocator,
grind-budget, LSP, documentation, and diff-check gates were green.

## N1b amendment: internal fixed-owner returns and named moves

N1b extends only N1a's exact concrete shape. An internal free function that
returns the class lowers as `void` with a hidden caller-supplied destination
pointer before its ordinary arguments. Direct constructor returns initialize
that pointer through the existing destination-pointer initializer, and a
class-returning internal call forwards an explicit destination. This convention
is module-private and versionable; it declares no source, platform, or C ABI.

A class local or return destination may also consume one live named class local.
Emission loads the fixed aggregate, stores it into the destination, then zeros
the complete source aggregate. The source remains registered for reverse
lexical cleanup, but its nested descriptor is now null/zero, so the existing
null-safe cleanup emits no second free. Direct destination construction and call
forwarding never install a second owner.

Backend validation treats this as affine movement, not an unrestricted class
expression. It rejects any subsequent read or borrow of the moved source. The
moved-owner set follows lexical scopes; reaching `if` arms must agree exactly,
a returning arm has no successor state, and a reaching loop body must restore
the same state at its backedge. Class-returning calls are accepted only where a
local or return destination is available; discarded results remain rejected.

The end-to-end subject still imports the real verified `Nat::from_prefix` and
`cmp`. Its wrappers mirror the constructor preconditions and cover a direct
constructor return, a tail class-returning call, local-to-local movement,
moved-local return, and both the early-return and fallthrough paths. Interpreter
and native success retain exit value 42.

Mutable class owners, reassignment, owned class parameters, methods, mutable
class borrows, moves from fields or arbitrary expressions, multiple or nested
class fields, generic classes, nonempty destructors, extern transport, and
public/cross-module class ABIs remain rejected.

## N2 amendment: the real imported `Nat` addition closure

N2 reuses N0–N1b rather than defining another representation or calling
convention. The selected closure for the real imported bignum `add` contains
shared `&Nat` inputs and reborrows, scalar length and limb helpers, one fresh
owned `[u32]` scratch buffer, a carry loop, prefix trimming, and
`Nat::from_prefix`. The inputs remain non-owning pointers. The scratch buffer
uses N0's descriptor, unaligned accesses, bounds traps, and lexical cleanup;
the constructed `Nat` uses N1a's fixed aggregate and nested destruction; and
N1b's destination pointer and named-move neutralization carry the result back
without fabricating a second live owner.

The dedicated `corpus/verifies/bignum_add_native.sable` subject discharges
40/40 verifier obligations and covers zero identity, `1 + 2`, a full-width
carry, and unequal operand lengths. Its emitted program returns 42 when
compiled directly by Clang at both `-O0` and `-O2`.

This remains an internal call-closure widening, not a class ABI. Mutable class
owners and reassignment stay closed until N4. The subsequent N3 amendment
below closes `sub` and schoolbook `mul`; `div`/`rem`/`gcd` remain N4, and
nested `Integer` ownership remains N5.
Owned class parameters, methods, mutable class borrows, discarded class
results, field moves, broader or generic class shapes, nonempty destructors,
extern transport, and public/cross-module class ABIs remain rejected.

## N3 amendment: the real imported `Nat` subtraction and multiplication closures

N3 admits the selected closures of the real verified `sub` and schoolbook
`mul` without adding a representation, calling convention, ownership rule, or
runtime hook. Both functions receive shared non-owning `&Nat` inputs, allocate
one fresh local `[u32]` scratch array, trim its completed prefix, construct the
fixed N1a result with `Nat::from_prefix`, and return it through N1b's hidden
destination and named-local move neutralization.

The arithmetic remains ordinary scalar lowering. `sub` performs its checked
base-2^32 borrow calculation in one loop. `mul` uses nested scalar loops with
checked widened limb products, scratch accumulation, and carry propagation.
N0's checked indexing and unaligned limb accesses apply throughout. Normal
reverse lexical cleanup frees scratch storage and the eventual destination
frees the constructed result; the zeroed moved-from local is a null-safe no-op.

The dedicated `corpus/verifies/bignum_sub_mul_native.sable` subject discharges
51/51 verifier obligations across 19 functions. It covers subtraction to zero,
a borrow chain across two zero limbs, multiplication by zero, a maximum limb
squared, and cross-limb carry. Its emitted program returns 42 when compiled
directly by Clang at both `-O0` and `-O2`.

This remains an internal call-closure widening, not a class ABI. Mutable class
owners, reassignment, and `div`/`rem`/`gcd` remain N4. Nested `Integer`
ownership, by-value class constructor/function arguments, class-field borrows,
mutable outer borrows and methods, and nested destruction remain N5. At N3,
owned class parameters, methods, mutable class borrows, discarded class
results, field moves, broader or generic class shapes, nonempty destructors,
extern transport, and public/cross-module class ABIs remain rejected.

## N4 amendment: the real imported `Nat` division, remainder, and gcd closures

N4 admits the selected closures of the real verified `div`, `rem`, and `gcd`
without changing N1a's exact fixed `Nat { [u32] limbs; }` representation. Its
new ownership surface is limited to mutable locals of that same class and
whole-local reassignment from an admitted constructor, internal class-returning
call, or live named move. Shared `&Nat` inputs and reborrows remain non-owning.

Every reassignment target receives one scratch slot allocated in the function
entry. Lowering evaluates the complete right-hand side into that scratch before
dropping the target's old value. This ordering is load-bearing for expressions
such as `dd = dd - vn` and `q = shift_in(&q, d)`: the producing call may borrow
the destination until it has finished constructing the replacement. After the
call returns, native cleanup destroys the old owner, the replacement aggregate
moves from scratch into the target, and the scratch is zeroed. No loop executes
a new stack allocation, no transient descriptor becomes a second registered
owner, and reassignment can safely revive a moved mutable target.

N4 needs no new loop lifetime mechanism. Existing lexical cleanup destroys
class owners declared inside a loop body in reverse order before the backedge;
outer mutable owners retain their function-scope cleanup; and zeroed move or
scratch carriers are null-safe no-ops. Path-sensitive validation continues to
reject reads and borrows of moved owners, mismatched reaching branch states,
and any loop backedge that fails to restore the same outer owner-liveness shape.

The dedicated `corpus/verifies/bignum_div_native.sable` subject discharges
109/109 verifier obligations across 21 selected functions with six small hand
discharges. It covers division by one, exact and inexact quotient/remainder
pairs, the multi-limb quotient-estimate correction, and basic, zero-input, and
coprime gcd cases. Its emitted program returns 42 when compiled directly by
Clang at both `-O0` and `-O2`.

This remains an internal call-closure and local-lifetime widening, not a class
ABI. N5 retains nested `Integer` ownership, by-value class constructor/function
arguments, class-field borrows, mutable outer borrows and methods, and recursive
reverse destruction. At N4, owned class parameters, mutable class borrows,
methods, discarded class results, field moves, broader or generic class shapes,
nonempty destructors, extern transport, and public/cross-module class ABIs
remain rejected.

## Consequences

This path gets Sable to native toolchains without expanding the trusted proof
base: Lean still checks contracts, while the new emitter is an additional
compiler component whose correctness is tested rather than assumed proven.
Starting from `VerifiedProgram` prevents verification/code-generation skew.
The cost is a backend intentionally limited to scalar, Boolean-option,
internal integer-POD values, the fenced local array/affine-option slices, and
one internal fixed-owner `Nat` convention through its imported arithmetic
closures from construction and comparison through division and gcd, with
aggregate ABIs still rejected, plus explicit traps/control flow where less
careful LLVM frontends often rely on poison. Broader aggregate representations
and every aggregate ABI, extern interoperability, optimization, debug
information, object emission, and stable cross-module symbols remain separate
decisions.
