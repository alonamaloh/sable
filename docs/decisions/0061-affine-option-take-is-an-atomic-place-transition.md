# ADR 0061 — affine-option take is an atomic place transition

**Decided 2026-08-13; G2.1–G2.3 closed.** ADR 0060 gave ownership-bearing
options a checked type distinct from ordinary copyable options. This decision
defines the first operation which can transfer their payload without creating
a second owner.

## Decision

The first affine-option payload is exactly an owned Boolean array. Its source
surface is deliberately local and explicit:

```sable
mut option<[bool]> pending = some(alloc_array<bool>(n, false));
if (pending.is_some) {
    [bool] values = pending.take;
}
```

`.take` is not a general projection. The AST records it as a named-place
operation:

```text
OptTake { option: String, option_span: Span }
```

and the checker accepts it only as the direct initializer of an explicit owned
Boolean-array local. The source must name a mutable local of type
`option<[bool]>`. Program `.value` remains forbidden for affine options because
it would expose the descriptor while leaving the option live.

The dynamic transition is atomic:

```text
none        --take--> option-none trap; source remains none
some(value) --take--> source := none; destination := value
```

There is no observable state in which both source and destination own the
payload. The destination is not installed until presence has been established,
and clearing the source cannot itself trap. A still-present payload is destroyed
when its option local leaves scope; a taken option is already empty and therefore
does no payload destruction. As with the existing owned-value rule, trap paths
do not unwind lexical storage.

`.is_some` is a non-consuming observation. It inspects the tag without cloning
or moving the payload. The option container remains initialized after take and
holds `none`; take is not a move of the container place. Presence is ordinary
value state, not a checker typestate lattice. Branch facts and loop invariants
are responsible for proving a take is present on a particular path.

## First-slice boundary

G2.1 admits only:

- explicit mutable local `option<[bool]>` declarations;
- mandatory initialization by `none` or `some(alloc_array<bool>(len, init))`;
- non-consuming `.is_some`; and
- `.take` directly into an explicit owned `[bool]` declaration.

Boolean-array literals inside `some`, wrapping an existing array, inferred
option bindings, whole-option assignment, parameters, returns, calls, fields,
traits, generics, borrows, exposure, nested affine options, non-Boolean
payloads, and discarded affine temporaries remain rejected. Literal wrapping
remains closed until the compiler can construct and lower it without a
temporary becoming an untracked second owner; G2.2 does not broaden that
ingress.

## Proof model

VC generation represents an affine option as
`Option (Sable.Seq Bool)`. Construction and `.is_some` use the ordinary Lean
option value, but no copy-option runtime rule follows from that proof value.

For `source.take`, VC generation:

1. snapshots the symbolic pre-update option;
2. emits the usual someness obligation against that snapshot;
3. obtains its `Sable.Seq Bool` payload using a typed explicit junk default (or
   an equivalent fresh payload binder related to the snapshot);
4. updates the symbolic source to `(none : Option (Sable.Seq Bool))`; and
5. returns the payload expression for the destination binding.

The explicit default avoids requiring a global `Inhabited (Sable.Seq Bool)`
instance. The someness obligation makes the default observationally irrelevant
on verified paths. Loop effect collection treats take as an assignment to the
source option so stale pre-take facts are havocked.

The dynamic proof monitor receives immutable snapshots, not executable owners.
Copying such a `SpecVal` is therefore legitimate; copying the interpreter's
runtime affine-option value through a program expression is not. Source
contracts inspect the payload with option `match`. Affine `.value` is reported
unmonitorable: `Sable.Seq` intentionally has no global `Inhabited` instance,
so accepting that clause dynamically would disagree with Lean elaboration.

## Machine and native consequences

G2.1 left both executable backends fail closed. G2.2 adds
`Stmt.optTake dst src` to the relational SVM and its proved functional
evaluator. The formal core retains recursive, untyped `Val.opt`, so the machine
transition transfers a generic `Val` payload. Rust lowering remains the exact
supported-subset gate: it emits `optTake` only from the G2.1 local
`option<[bool]>` source into an owned `[bool]` destination. Lowering take to a
pure `optValue` followed by a separate assignment is rejected: the intermediate
SVM state would contain two values representing one ownership transfer, so the
formal machine would cease to be an ownership oracle even if the final wire
result happened to match.

For distinct `dst` and `src`, a present source steps directly to the state in
which `src` is `.opt none` and `dst` contains the former payload. A distinct
empty source traps `optionNone`, while a missing binding or wrong outer value
is `undef`. Aliasing the two names is immediately `undef`, before inspecting
the option state. No destination-absence premise is used: flat SVM environments
reuse lexical-local names across loop iterations, so a valid declaration may
overwrite a stale destination binding. The move retains `ArrayVal.bools`
exactly, including the element tag of an empty array.

Parameters, returns, calls, fields, traits, generics, borrows, exposure,
whole-option movement, non-Boolean affine payloads, and every affine-option ABI
remain rejected by the Rust bridge. G2.3 opens only the exact matching local
LLVM path; the same transport and ABI fences remain.

G2.3 lowers the transition as
`%sable.option.array.bool = type { i8, %sable.array.bool }`. Tag zero is the
complete zero aggregate; tag one owns the payload descriptor, including the
null/zero descriptor of a present empty Boolean array. Take loads the source,
guards tag one with existing trap kind 8, extracts the descriptor on the
success edge, stores the complete source as `zeroinitializer`, and only then
lets the destination declaration store the payload. The clear therefore
precedes destination ownership in emitted memory state.

The cleanup registry distinguishes owned arrays from affine Boolean-array
options and unwinds both in reverse declaration/scope order. Option cleanup
follows the tag-one edge and calls `__sable_rt_array_free_v1` only for a
nonnull nested pointer. A taken, absent, or present-empty source does not free;
the destination owns the sole nonempty payload after a successful take. Trap
edges perform no cleanup. Construction and subsequent payload access reuse the
existing hooks, 50,000,000-element cap, zero bypass, and trap kinds 9 and 10.
No parameter, return, call, field, trait, class, generic, borrow, exposure,
extern, entry, or cross-module ABI is implied.

## Closure evidence

G2.1 closed under the exact one-worker command
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`.
`cargo check -j1` was green, and standalone Lake built 22/22 targets with only
the same existing linter warnings. Rust library tests passed 211/211; the
recursive corpus passed all 416 subjects (84 verifies, 263 must-fail, 49 tests,
20 test-fails) in 193.06s; LLVM CLI passed 7/7; the native differential passed
1/1 spanning six subjects at `-O0` and `-O2`; and SVM differential remained
86/86. Randomized free-list allocator, grind-budget, LSP, documentation,
rustfmt, diff-check, and static-audit gates were green.

This closes checker, VC-generator, interpreter, and monitor agreement on
present, absent, post-take, branch, loop, destruction, and trap behavior.

G2.2 closed under the exact one-worker command
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`.
`cargo check` and the standalone Lake build were green; Lake built 22/22
targets with only the existing warnings. Focused SVM units passed 35/35, Rust
library tests 211/211, and the recursive corpus all 416 subjects (84 verifies,
263 must-fail, 49 tests, 20 test-fails) in 270.58s. LLVM CLI passed 7/7; the
native differential passed 1/1 over six subjects at `-O0` and `-O2`; and SVM
differential passed 92/92. Free-list allocator, grind-budget, LSP,
documentation, rustfmt, diff-check, and static-audit gates were green. G2.2 is
closed.

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
were green. G2.3 is closed; generic slots and `Vec` ownership are next, not an
affine-option ABI widening.
