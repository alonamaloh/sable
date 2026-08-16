# ADR 0059 — native owned Boolean arrays use runtime hooks and lexical cleanup

**Decided and implemented 2026-08-13; G1.6, the G2.3 affine-option amendment,
and N0–N5's `u32`/fixed-`Nat`/nested-`Integer` amendments are closed.** G1.5
gives owned-local
Boolean arrays a checked, verified,
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

## N0 amendment: byte-backed local `u32` arrays

N0 reuses these same v1 hooks and lexical cleanup rules for one exact additional
payload: fresh owned local `[u32]`, plus non-owning internal ordinary-function
borrows. Its named internal descriptor is
`%sable.array.u32 = type { ptr, i64 }`. The length field is a logical element
count; a nonempty allocation passes `len * 4` bytes to the allocation hook and
cleanup passes only the returned pointer to the unchanged free hook. Zero
length is null/zero and invokes neither hook.

The v1 allocation declaration promises bytes, not alignment. Consequently all
`u32` element loads and stores use `align 1`, including accesses through shared
and mutable borrowed parameters. This preserves defined LLVM behavior even for
a conforming hook that returns storage not aligned for native `u32`. A future
typed/aligned hook may be a separate optimization decision; N0 does not amend
the existing ABI implicitly.

The element cap remains 50,000,000. Kind 9 continues to report logical length
as `(type_info, lhs_bits, rhs_bits) = (0, len, 0)` even though the hook sees
bytes, and kind 10 remains `(0, index, len)`. Cap rejection happens before the
hook; a null result after a below-cap byte request also reports kind 9. Trap
edges perform no cleanup. Normal branch, loop-iteration, and early-return paths
destroy owning locals in the existing reverse lexical order. Borrow parameters
are never owners and never free the caller's allocation.

Only exact explicit named `&[u32]` and `&mut [u32]` call arguments with matching
checked mutability are admitted. Owned-array call transport, returns, entries,
fields, classes, methods, externs, Boolean borrows, other payloads, exposure,
and public or cross-module ABI positions stay closed.

ADR 0070 supersedes the Boolean-borrow half of that sentence: `&[bool]` and
`&mut [bool]` are admitted parameters under the same argument rule, lending the
same kind of descriptor. Everything else in it stands.

## N1a–N5 amendment: nested class cleanup and arithmetic scratch storage

N1a embeds one `%sable.array.u32` descriptor in the exact fixed native `Nat`
class. Normal class destruction projects that descriptor and applies the same
null bypass and free hook used by an owning local array. The class owner joins
the existing cleanup registry, so reverse lexical order, early-return unwind,
loop-iteration cleanup, and the no-unwind trap rule do not acquire a parallel
lifetime mechanism.

N1b adds internal class returns and named local moves without changing the hook
contract. Direct construction and class-returning calls write into a unique
destination pointer. A named move stores the complete aggregate into its
destination and immediately replaces the source aggregate with zero. Its
already-registered cleanup therefore sees a null descriptor and performs no
free; the destination remains the sole live owner and performs exactly one
eventual free for a nonempty magnitude. Validation rejects reuse of that moved
source and rejects reaching branch or loop shapes that could make cleanup
liveness ambiguous.

N2 changes neither hook nor cleanup protocol. The real imported `add` closure
borrows both input classes, allocates one fresh local `[u32]` scratch
descriptor, fills it in a carry loop, and passes its trimmed prefix to
`Nat::from_prefix`. The constructor creates the result's separately owned
nested descriptor; normal reverse lexical cleanup frees the scratch allocation,
and the destination owner eventually frees the result allocation. Shared input
borrows and reborrows never enter the cleanup registry, while any intervening
named move still zeros its source before that source's registered cleanup.

N3 likewise changes neither hook nor cleanup protocol. The real imported
`sub` and schoolbook `mul` closures each allocate one fresh `[u32]` scratch
descriptor. Subtraction fills it in one checked borrow loop; multiplication
fills it with nested checked product/carry loops. Each function trims the
scratch prefix, constructs a separate result descriptor with
`Nat::from_prefix`, and moves the named result into its hidden return
destination. Reverse lexical cleanup frees the scratch allocation, the zeroed
moved-from result local is a null-safe no-op, and the destination remains the
sole owner of the result allocation.

N4 also changes neither runtime hook nor the registered-cleanup model. For each
mutable fixed-`Nat` reassignment target, one unregistered scratch slot is
allocated in the function entry. The complete replacement is constructed there
before the old target is destroyed, keeping self-borrows valid while the RHS
runs. Cleanup then frees the old nested descriptor, the replacement aggregate
moves into the target, and the scratch is zeroed. The target's existing cleanup
entry remains the sole eventual owner of the replacement allocation.

Loop-carried ownership continues to use lexical cleanup rather than a new
runtime mechanism. Body-local class owners are destroyed in reverse order
before each backedge, outer mutable owners retain function-scope cleanup, and
zeroed named-move or reassignment scratch carriers bypass the free hook. The
N4 fixture verifies 109/109 obligations across 21 selected functions with six
small hand discharges, covers division by one, exact/inexact quotient and
remainder, multi-limb correction, and basic/zero/coprime gcd, and returns 42
under direct Clang `-O0` and `-O2` builds.

N5 keeps the same runtime hooks and makes destruction recursive for the one
additional supported shape `Integer { Nat mag; u64 neg; }`. Reverse field order
visits scalar `neg` as a no-op and then descends through `mag` to `Nat.limbs`,
where the existing null bypass and `__sable_rt_array_free_v1` call apply. No
new allocator, free function, descriptor, or unwind rule is introduced.

The exact owned-`Nat` take convention preserves single ownership across
constructor and function parameters. A caller passes the aggregate by value
and zeros a named source; a class-returning argument first uses a unique
entry-hoisted, unregistered scratch destination. The completed aggregate is
loaded by value and the scratch is zeroed immediately before the call. The
callee registers its parameter slot for cleanup, and moving that value into
`Integer.mag` zeros the slot. Therefore an unconsumed parameter is freed by the
callee, a consumed one is eventually freed through the outer `Integer`, and no
path registers two live cleanup owners for one allocation. There is no
caller-side post-call drop.

Per-field initializer tracking ensures that `mag` and scalar `neg` are each
initialized exactly once. Shared borrows of `Integer.mag` and `Nat.limbs`, and
the exact mutable `&mut Integer` receiver used by private
`Integer::flip_sign`, are non-owning and never enter the cleanup registry.
Scalar sign reads and stores likewise acquire no cleanup action.

The N5 fixture verifies 237/237 obligations across 39 selected functions and
returns 42 under direct Clang `-O0` and `-O2` builds. A dedicated strong
allocator-hook test is green at both optimization levels with exit 42 and
`live = 0`; it aborts on a leak, unknown free, or double free. The exact
`VerifiedProgram` differential is green 1/1 over 13 subjects at `-O0` and
`-O2`, including `Integer` exit 42.

N5 closed under
`SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1`. The gentle serial
run passed 223/223 library tests; corpus 1/1 in 93.64s; randomized allocator
1/1; grind-budget 1/1; LLVM CLI 10/10; differential 1/1 in 31.35s; LSP 1/1;
SVM differential 1/1; and documentation tests. `cargo check -j1` and rustfmt
were green as well.

This still does not admit owned `Integer` parameters, arbitrary owned class
parameters, methods beyond the exact `flip_sign` closure, mutable borrows of
other classes, discarded class results, field moves, class fields beyond the
exact `Nat` and `Integer` declarations, nonempty destructors, extern transport,
or any public/cross-module class ABI.

N0 closed under the exact one-worker command
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`.
`cargo check` was green; focused LLVM units passed 31/31; Rust library tests
passed 215/215; and all 416 recursive corpus files (84 verifies, 263 must-fail,
49 tests, 20 test-fails) passed in 213.51s. LLVM CLI passed 9/9; the exact
interpreter/native differential passed 1/1 over eight subjects at Clang `-O0`
and `-O2`; and SVM differential remained 92/92. Randomized allocator,
grind-budget, LSP, documentation, rustfmt, diff-check, and static-audit gates
were green. N0 is closed.

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
were green. G2.3 is closed. At that checkpoint generic slots and `Vec`
ownership were recorded as the next aggregate design, not an affine-option ABI
widening. The subsequently implemented N0 amendment above begins an independent
native `Nat` ladder; N1a subsequently closed local-only fixed-owner
construction and the real imported `cmp`, N1b closed internal
destination-pointer returns and single-use named moves, N2 closed the real
imported `add` closure, and N3 now closes the imported `sub` and schoolbook
`mul` closures without changing the hook contract. N4 closes the imported
`div`, `rem`, and `gcd` closures through scratch-before-drop reassignment and
the same lexical cleanup protocol. N5 implements the exact nested signed
`Integer` closure with recursive reverse drop and closes under its
differential/lifetime evidence; broader class transport stays fenced.
