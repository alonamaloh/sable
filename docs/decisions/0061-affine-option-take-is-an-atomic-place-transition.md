# ADR 0061 — affine-option take is an atomic place transition

**Decided 2026-08-13; G2.1 closed.** ADR
0060 gave ownership-bearing options a checked type distinct from ordinary
copyable options. This decision defines the first operation which can transfer
their payload without creating a second owner.

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
waits until the formal machine can wrap a freshly constructed payload without a
compiler temporary becoming an untracked second owner.

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

G2.1 leaves both executable backends fail closed. G2.2 adds one atomic
statement-level `optTake` transition to the formal SVM. Lowering take to a pure
`optValue` followed by a separate assignment is rejected: the intermediate SVM
state would contain two array values representing one ownership transfer, so
the formal machine would cease to be an ownership oracle even if the final
wire result happened to match.

G2.3 then lowers the same transition natively as a canonical tag/live bit plus
the G1.6 Boolean-array descriptor. A successful take clears the complete source
representation before the destination is registered for cleanup. Lexical drop
checks the live tag and conditionally invokes the existing array cleanup. No
parameter, return, field, extern, entry, or cross-module ABI is implied.

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
present, absent, post-take, branch, loop, destruction, and trap behavior while
the formal SVM and LLVM still reject the type explicitly. G2.2's atomic
formal-SVM `optTake` transition is next; G2.3 closes its own native/runtime-hook
gate independently.
