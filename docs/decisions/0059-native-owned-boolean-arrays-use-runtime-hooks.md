# ADR 0059 — native owned Boolean arrays use runtime hooks and lexical cleanup

**Decided and implemented 2026-08-13; G1.6 and the G2.3 affine-option
amendment closed.** G1.5 gives owned-local Boolean arrays a checked, verified,
interpreted, monitored, and formal-SVM meaning. LLVM remained the only
execution boundary that rejected that exact slice at the G1.5 checkpoint. This
decision adds native lowering without declaring an array ABI or widening the
accepted source positions; G2.3 subsequently reuses its hooks and lexical
cleanup for the exact local `option<[bool]>` slice.

## Decision

LLVM represents a Boolean-array local as
`%sable.array.bool = type { ptr, i64 }`: an opaque data pointer followed by a
`u64` length. Elements occupy canonical `i8`
bytes, zero or one; they are not packed LLVM `i1` values. Static checked type
information distinguishes the payload even when an empty array is represented
by a null pointer and zero length. The descriptor and all generated functions
remain internal and versionable.

Allocation is target-neutral at the IR boundary. Generated modules declare:

```text
ptr  @__sable_rt_array_alloc_v1(i64 bytes)
void @__sable_rt_array_free_v1(ptr allocation)
```

The allocation hook returns null on failure and the free hook is nontrapping.
Generated code skips both hooks for a zero-length value. The separately
compiled hosted shim in `runtime/hosted/sable_rt_v1.c` implements the
fixed-width contract with the platform C allocator after checking that the
`u64` byte count fits `size_t`; the emitter does not declare or call `malloc`
or `free` directly. The hooks are external declarations, not weak defaults
silently supplied by every module.

The existing versioned trap observer gains two fixed kinds. Kind 9 is array
allocation failure, with `type_info = 0`, `lhs_bits = len`, and
`rhs_bits = 0`. Kind 10 is array index out of bounds, with `type_info = 0`,
`lhs_bits = index`, and `rhs_bits = len`. The mandatory `llvm.trap` after the
observer remains unchanged. A target allocation failure below the language's
50,000,000-element profile cap is a defined native OOM trap; physical resource
availability is not a verifier theorem.

## Exact source boundary

The native slice is the existing G1.4b/G1.5 intersection: a fresh owned-local
`[bool]` initialized by `alloc_array<bool>` or a contextual literal, followed
by `.len`, checked index reads, and element stores. Parameters, returns,
fields, borrows, exposure, whole-array movement or rebinding, call transport,
discarded temporaries, generic containment, option containment, externs, and
public ABI positions remain rejected independently by the backend. Integer
arrays are not silently admitted by this decision.

Allocation evaluates length, then its Boolean initializer, then the profile
cap and allocation result. A literal evaluates every element left-to-right
before allocation, then writes the resulting canonical bytes in order. A store
evaluates index, then value, then performs the unsigned bounds guard before a
non-`inbounds` address calculation. An indexed read likewise guards before its
load. These orders preserve the interpreter and formal-SVM trap precedence.

## Lifetime

Owned arrays are destroyed at their lexical block boundary, in reverse
declaration order. Function bodies, `if` arms, and each `while` iteration are
cleanup scopes; `unsafe` is an open marker and contributes declarations to its
enclosing scope. A return expression is evaluated first, then every active
scope is unwound from inner to outer before `ret`. Loop-body cleanup runs before
the backedge. Trap edges terminate immediately and do not run cleanup, matching
the language interpreter's explicit rule.

This cleanup substrate was deliberately established before affine options.
G2.3 composes its recursive owner and atomic take with that tested lifetime
rather than inventing a second allocation or destruction contract.

## G2.3 amendment: conditional affine-option cleanup

The exact local affine Boolean-array option uses
`%sable.option.array.bool = type { i8, %sable.array.bool }`. A canonical absent
value is the complete `zeroinitializer`; tag one owns the nested descriptor,
including the null/zero descriptor of a present empty array. Construction by
`some(alloc_array<bool>(...))` therefore uses the same allocation hook, profile
cap, zero-length bypass, and kind-9 OOM order as an ordinary owned Boolean
array. Reads and stores through a successfully taken payload keep the existing
kind-10 bounds rule.

The cleanup registry now records a typed entry for either an ordinary Boolean
array or an affine Boolean-array option. It still unwinds scopes and
declarations in the exact order above. Option destruction first requires tag
one, then extracts the nested pointer, and calls
`__sable_rt_array_free_v1` only when that pointer is nonnull. Absent, taken, and
present-empty options therefore call no free hook. A present nonempty option
owns exactly one allocation and frees it exactly once unless take transfers it
to the destination array, whose ordinary cleanup then performs that one free.
Trap edges remain terminal and perform no cleanup.

Native take checks tag one with the existing kind-8 option-none trap, extracts
the descriptor only in the dominated success block, stores the complete source
as zero, and only then installs the destination. This is an atomic ownership
transition in emitted memory state; no new hook or trap kind is needed.

This amendment is local lowering, not transport. Affine-option parameters,
returns, calls, entries, externs, fields, traits, classes, generics, borrows,
exposure, whole-option movement or assignment, inferred bindings, discarded
temporaries, non-Boolean payloads, and wrapping an existing or literal array
remain rejected. The internal named type establishes no Sable, C, or
cross-module ABI.

## Adjacent owned-array soundness correction

The lifetime audit found a pre-existing integer-array move hole outside the new
native Boolean slice. Assigning an owned array local into a class field is a
special consuming checker path: ordinary whole-array reads are otherwise
illegal. That path checked element/type compatibility but did not first reject
a source place already marked moved, so the same integer array could be moved
into two fields whose logical sequence values were assumed independent.

The checker now performs the moved-place guard explicitly at this boundary.
The interpreter's common moved-expression path takes named owned-array sources,
and local/frame cleanup removes owned arrays from their places, including owned
parameters. Boolean-array whole-value transport remains closed; this correction
restores the already-promised semantics of legacy integer-array moves. The new
`array_double_move_into_fields.sable` must-fail subject pins
`array.use_after_move`. It raises the corpus inventory from 394 to 395 subjects,
with 245 must-fail files (83 verifies, 48 tests, and 19 test-fails unchanged).

## Evidence required for closure

Structural IR coverage for representation, canonical bytes, guard dominance,
operand order, reverse cleanup, zero bypass, and the existing poison-promise
exclusions is green. G1.6 closed under
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`.
`cargo check` and the standalone 22-target one-job Lake build were green; Rust
library tests passed 185/185 and LLVM units 26/26; all 395 corpus subjects (83
verifies, 245 must-fail, 48 tests, 19 test-fails) passed in 192.76s; LLVM CLI
passed 7/7, including the strong-hook allocation/free-count, forced-OOM,
zero-length, exact-payload, early-return, branch, and loop fixture at Clang
`-O0` and `-O2`; the exact interpreter/native differential passed 1/1 across
six subjects at both optimization levels; and SVM differential remained 86/86.
Randomized allocator, grind-budget, LSP, documentation, diff-check, and static
audit gates were green. G1.6 is closed.

G2.3 closed under the exact standard command
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`.
`cargo check` was green; standalone Lake built 22/22 targets with only the
existing warnings; focused LLVM units passed 29/29; and Rust library tests
passed 213/213. The recursive corpus passed all 416 subjects (84 verifies, 263
must-fail, 49 tests, 20 test-fails) in 194.43s. LLVM CLI passed 8/8; the exact
interpreter/native differential passed 1/1 over seven subjects at Clang `-O0`
and `-O2`; and SVM differential remained 92/92. Free-list allocator,
grind-budget, LSP, documentation, rustfmt, diff-check, and static-audit gates
were green. G2.3 is closed. The next aggregate step is generic slots and `Vec`
ownership, not an affine-option ABI widening.
