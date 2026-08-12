# ADR 0058 — LLVM lowering consumes the verified program

**Decided and implemented 2026-08-12; scalar v0 complete.** Unsafe Sable v1 had
a defensible formal stopping point but no native-code path. This backend makes
verified scalar programs runnable without making LLVM part of the verifier or
introducing a second, subtly different front-end pipeline.

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

## Initial executable subset

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
and 7 narrowing out of range. Integer type codes are 1 through 8 for
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

The complete low-concurrency command
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture` is green.
It includes 26/26 library tests, 6/6 verified LLVM CLI tests, and a 1/1 native
differential test comparing the exact `VerifiedProgram` interpreter outcome
with Clang `-O0` and `-O2` for scalar, control-flow, and arithmetic subjects.
The matrix covers negative divisors, the `MIN % -1` bypass, conversion bounds,
and a loop condition designed to detect accidental hoisting out of its header.
Verification failure and audited-assumption rejection leave existing output
untouched.

The native trap fixture exercises all seven published kinds at both
optimization levels, with exact kind, type-info, and raw-operand payloads. Its
strong hook returns, and the following `llvm.trap` still terminates each
process. The same serial regression kept the SVM Rust/Lean differential green
at 69/69, completed the full verifier/dynamic corpus in 220.78s, and passed the
randomized allocator, grind-budget, LSP, and documentation tests. That closes
the scalar v0 milestone. It does not extend the accepted subset to aggregates:
aggregate storage, lowering, and ABIs remain M46+ decisions.

## Consequences

This path gets Sable to native toolchains without expanding the trusted proof
base: Lean still checks contracts, while the new emitter is an additional
compiler component whose correctness is tested rather than assumed proven.
Starting from `VerifiedProgram` prevents verification/code-generation skew.
The cost is an intentionally narrow scalar backend and explicit traps/control
flow where less careful LLVM frontends often rely on poison. Aggregate ABIs,
extern interoperability, optimization, debug information, object emission,
and stable cross-module symbols remain separate decisions.
