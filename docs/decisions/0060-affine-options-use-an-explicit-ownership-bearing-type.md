# ADR 0060 — affine options use an explicit ownership-bearing type

**Decided 2026-08-13; G2.0–G2.2 closed.** Existing
`Ty::Option(ValueTy)` describes a copyable value option. Its payload identity
is deliberately flat, and checker, verifier, interpreter, SVM, and LLVM code
all rely on that copy boundary. Making one of those payloads affine by
convention would turn every existing `Ty::Option(_)` match into an ownership
soundness audit and make `.value` an accidental aliasing operation.

## Decision

Affine options have a separate checked representation:

```text
AffineOptionTy := Array(ValueTy)
Ty::AffineOption(AffineOptionTy)
```

The representation remains `Copy`; it is a compact type descriptor, not the
runtime value. The first admitted payload is exactly an owned Boolean
array, spelled `option<[bool]>`. Keeping `Array(ValueTy)` rather than a closed
`BoolArray` tag represents future payload identity honestly while every stage
independently rejects non-Boolean instances. Existing `Ty::Option(ValueTy)`,
`option<raw<Record>>`, and all their behavior remain unchanged.

This is intentionally smaller than changing `Ty::Option` to contain a
recursive `Ty`, and much smaller than interning the complete checked type
graph. G0's `GenericTy` remains the recursive source/use-site identity tree;
it is not a checked type because its nominal identities are names rather than
post-merge indices and it does not encode checked ownership or borrows.

## First semantic slice

The first usable surface is local and explicit:

```text
mut option<[bool]> pending = none;
mut option<[bool]> ready = some(alloc_array<bool>(n, false));

if (ready.is_some) {
    [bool] values = ready.take;
}
```

An affine-option local must have an initializer. Initially that initializer is
`none` or `some` of a fresh Boolean-array allocation; wrapping an existing
owned array remains closed. `.is_some` observes without consuming. Program
`.value` is rejected for an affine payload because returning the descriptor
without clearing the container would create two owners. `.take` is a
place-mutating postfix operation on a named mutable option and is accepted only
as the direct initializer of an explicit owned Boolean-array declaration.

Taking is atomic:

1. inspect the option tag;
2. trap with the existing option-none kind when absent, leaving the source
   unchanged;
3. obtain the payload;
4. replace the option with `none`;
5. install the payload in its destination place.

The option container remains initialized and is not itself moved. Presence is
value state, not a second checker typestate lattice: branch paths and loop
invariants already carry the symbolic/runtime option value. A one-shot loop
such as `while (o.is_some) { [bool] a = o.take; }` must not be rejected merely
because the tag changes across the backedge.

Parameters, returns, calls, fields, traits, generics, inferred bindings,
whole-option assignment or movement, nested affine options, borrows, exposure,
discarded temporaries, class/resource payloads, and integer-array payloads stay
closed in the first slice.

## Proof and execution model

VC generation models the value as `Option (Sable.Seq Bool)`. A take emits the
ordinary someness obligation against the pre-update option, obtains the
sequence payload, and then changes the symbolic source to typed `none`. It is a
program ownership operation. Proof clauses observe pure snapshots through
option `match`; affine `.value` remains unmonitorable because `Sable.Seq` has no
global `Inhabited` instance, and the monitor rejects it for Lean parity.

The interpreter stores affine options separately from copy options. Its take
mutates the named frame entry directly, and lexical destruction recursively
drops a present payload exactly once. Trap paths do not unwind, matching the
existing owned-value rule.

G2.2 keeps the formal SVM's recursive `Val.opt (Option Val)` representation and
adds atomic statement-level `Stmt.optTake dst src` to both the relational and
executable semantics. The untyped formal core deliberately transfers a generic
`Val` payload; the Rust bridge is the exact supported-subset gate and emits the
statement only for a G2.1 `option<[bool]>` source and owned `[bool]`
destination. Lowering take to `optValue` followed by a separate assignment
would create an intermediate state with two owners and therefore is not an
acceptable ownership model, even if its final rendered result happened to
match.

For distinct names, present clears the source to `.opt none` and installs the
payload in the destination in one transition. A distinct `.opt none` traps
`optionNone`; a missing or wrong outer source is `undef`; and `dst = src` is
immediately `undef`. The destination need not be absent: the flat SVM
environment reuses lexical-local names across loop iterations, and the new
declaration must overwrite that stale binding. Moving the payload preserves
its `ArrayVal.bools` tag even at length zero. Parameters, returns, calls,
fields, traits, generics, borrows, exposure, whole-option movement, and every
affine-option ABI remain outside this bridge.

Native lowering follows only after the semantic/SVM slice closes. Its planned
internal form is a canonical tag plus the existing Boolean-array descriptor;
the tag is also the payload-live bit. Taking clears the complete source before
the destination owns the descriptor, while lexical destruction conditionally
uses G1.6's array cleanup. No affine-option ABI follows from that internal
representation.

## Staging

1. **G2.0 — representation/fail-closed foundation:** parse `option<[T]>` for a
   Boolean, integer, or in-scope parameter payload as
   `Ty::AffineOption(AffineOptionTy::Array(ValueTy))`; carry validation,
   substitution, and concreteness through monomorphization. The checked
   representation also carries future/synthetic `ValueTy::Record` payloads,
   whose nominal visibility module traversal must enforce even though the
   surface parser does not yet construct them. Every semantic boundary remains
   fail closed. Otherwise-admissible direct ingresses use stable `type`, `vc`,
   `interp`, `svm`, and `backend` `affine_option_unsupported` diagnostics; an
   already-unsupported enclosing construct may diagnose its outer fence first.
2. **G2.1 — local construction and take (complete):** checker, VC generator,
   interpreter, and dynamic monitor implement the exact local slice.
3. **G2.2 — formal machine (complete):** atomic SVM `optTake` and the exact
   Boolean-array differential bridge are present; all other machine transport
   remains fail closed.
4. **G2.3 — native local lowering (next):** conditional destruction and source
   clearing, without transport or ABI widening.
5. Parameters, returns, calls, and fields remain later independent decisions.

Each stage must be independently fail closed and complete its single-worker
Rust/Lean/corpus gate before the next semantic widening.

G2.0 closed under the exact one-worker command
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`.
`cargo check` and standalone `lake -Kjobs=1 build` were green; Lake built 22/22
targets with only the same existing linter warnings. Rust library tests passed
192/192; all 396 corpus subjects (83 verifies, 246 must-fail, 48 tests, 19
test-fails) passed in 192.03s; LLVM CLI passed 7/7; exact interpreter/native
differential passed 1/1 over six subjects at `-O0` and `-O2`; and SVM
differential stayed 86/86. Randomized allocator, grind-budget, LSP, doc-tests,
rustfmt, diff-check, and static-audit gates were green. No semantic behavior
described for G2.1 is part of G2.0.

G2.1 closed under the exact one-worker command
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`.
`cargo check -j1` was green, and standalone Lake built 22/22 targets with only
the same existing linter warnings. Rust library tests passed 211/211; the
recursive corpus passed all 416 subjects (84 verifies, 263 must-fail, 49 tests,
20 test-fails) in 193.06s; LLVM CLI passed 7/7; the native differential passed
1/1 spanning six subjects at `-O0` and `-O2`; and SVM differential remained
86/86. Randomized free-list allocator, grind-budget, LSP, documentation,
rustfmt, diff-check, and static-audit gates were green. G2.1 is closed.

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
closed. LLVM retains the `backend.affine_option_unsupported` fence for G2.3,
the next stage.
