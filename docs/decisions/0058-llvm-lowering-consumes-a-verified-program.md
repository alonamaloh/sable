# ADR 0058 — LLVM lowering consumes the verified program

**Decided 2026-08-12; first implementation slice landed, milestone in progress.** Unsafe Sable v1 has a
defensible formal stopping point, but Sable still has no native-code path. The
first backend should make verified programs runnable without making LLVM part
of the verifier or introducing a second, subtly different front-end pipeline.

## Decision

The compiler will gain a handwritten textual LLVM IR emitter, selected with:

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
The backend therefore emits no `nsw`, `nuw`, `inbounds`, or `llvm.assume` as a
substitute for a Sable proof. Checked addition, subtraction, and multiplication
use LLVM overflow intrinsics and branch to a trap on the overflow bit. Division
and remainder guard zero, and signed division additionally guards
`min / -1`, before executing LLVM's instruction.

Sable signed division is Euclidean; LLVM signed division truncates toward
zero. The emitted control flow corrects LLVM's quotient and remainder when the
truncating remainder is negative, rather than changing the source-language
meaning. Narrowing performs an explicit range check before truncation. Boolean
short circuiting is control flow with merge values, so an unevaluated operand
cannot trap or produce effects.

Runtime failures use a versioned trap hook plus an internal `noreturn` helper:

```text
void @__sable_rt_trap_v1(i32 kind, i32 type_info,
                         i64 lhs_bits, i64 rhs_bits)
```

The default helper invokes the weak hook and then `llvm.trap`; embedding code
may replace the hook for diagnostics. This interface describes failures, not a
stable calling convention for Sable functions.

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
`clang` is available, later differential fixtures will compile and run the
same scalar subjects at `-O0` and `-O2`, comparing return values and traps with
the Sable interpreter. These end-to-end checks are optional for a normal developer
environment unless explicitly required (for example by
`SABLE_REQUIRE_CLANG=1`); the ordinary emitter suite never acquires an LLVM
tool dependency.

The first two slices are now implemented: the opaque `VerifiedProgram`
boundary, root-bound entry selection, CLI, atomic output, provenance comments,
strict scalar lowering, and a real CFG for branches, loops, comparisons, and
short circuiting. Local allocation is entry-hoisted while initialization stays
at its source point. Their focused gates are green at 18/18 library tests and
4/4 CLI tests; both scalar and CFG subjects return 42 when compiled by Clang at
`-O0` and `-O2`, while verification failure and
audited-assumption rejection both leave an existing output untouched. The
complete one-worker verifier/dynamic corpus also remains green through the new
handoff (205.93s). The remaining work should continue in reviewable slices:
exact arithmetic, conversions, and traps; finally
broader strict diagnostics, differential fixtures, and final user
documentation. Until those slices and gates land, the complete v0 backend is
still in progress.

## Consequences

This path gets Sable to native toolchains without expanding the trusted proof
base: Lean still checks contracts, while the new emitter is an additional
compiler component whose correctness is tested rather than assumed proven.
Starting from `VerifiedProgram` prevents verification/code-generation skew.
The cost is an intentionally narrow first backend and explicit traps/control
flow where less careful LLVM frontends often rely on poison. Aggregate ABIs,
extern interoperability, optimization, debug information, object emission,
and stable cross-module symbols remain separate decisions.
