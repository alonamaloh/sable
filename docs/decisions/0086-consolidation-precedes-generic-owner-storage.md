# ADR 0086 — consolidation precedes generic owner storage

**Decided 2026-08-19.** The next feature rung was blocked on a deliberately
boring trust-boundary consolidation gate. That gate is now closed; generic owner
slots and the broader container work that depends on them may proceed.

## Context

Sable's accepted semantic surface now crosses a checker, a trusted Rust VC
generator, a Rust interpreter, a Lean formal machine, and a handwritten LLVM
backend. The corpus and fail-closed stage gates make each frontier unusually
visible, but they do not make duplicated semantic decisions safe. Recent false
proofs came from two such duplications: a manually enumerated havoc path kept
stale symbolic state, and a call-conflict check reconstructed moves from
argument syntax instead of consulting semantic transfer state.

Generic owner storage would multiply the same questions across nesting, calls,
loops, replacement, and recursive destruction. Extending the surface first
would make the trusted implementation harder to audit at exactly the points
where an omission can cause Lean to prove the wrong proposition.

## Decision

Sable has a named consolidation gate, C0, with these exit criteria:

1. Core semantic enums in the trusted checker and VC generator are dispatched
   exhaustively; wildcard arms cannot silently admit a new variant.
2. Place identity and call-transfer facts have shared representations rather
   than being reconstructed from syntax by each consumer.
3. Scope exits, drops, traps, loop edges, and their cleanup obligations are
   represented by one normalized control-flow model consumed by proof and
   execution paths.
4. The admitted native subset has deterministic generated differential tests,
   run against the interpreter and Clang at `-O0` and `-O2` in required public
   CI.
5. The public documentation distinguishes Lean theorem validity, trusted VC
   generation, formal-machine evidence, and native differential evidence.
6. One dangerous symbolic-execution slice has a Lean-checked transition
   certificate, establishing the path for moving the VC generator from trusted
   theorem designer toward untrusted certificate producer.

Current status: all six criteria are closed. ADR 0092 supplies the final shared
cleanup actions and completes criterion 3, so C0 no longer blocks generic owner
storage.

The gate is structural, not a promise to split the Rust crate by file size.
Modules are extracted when they create one authoritative semantic operation or
representation used by multiple stages. Moving code without removing a
duplicated decision does not count.

The landed foundation centralizes place decoding, retains the existing single
checker transfer operation and fresh-state construction, makes trusted enum
dispatch exhaustive, adds per-case-observable generated native differentials,
publishes the assurance profiles, and provides local toolchain diagnostics.

ADR 0090 closes criterion 2 for the admitted checker-to-VC boundary. One
`CheckedOwnershipPlan` records typed value transfers, all admitted call
arguments and receivers, loans, sealed operations, option takes, exposures, and
checker-computed loop mutations. VC generation requires exact immutable records
and at-least-once coverage for each verified callable; the old effect walkers
are removed. Trait-call proof reuse remains scalar-only and has no owning effect
to transfer.

ADRs 0087–0088 retain the narrower Lean-checked certificate for explicit
unique-borrow call havoc. Lean checks fresh place write-back and, for arrays,
the exact length relation in the emitted symbolic state. An adversarial
regression replaces the observed post-state with the real pre-state and requires
Lean to reject the artifact. That certificate does not validate source-to-
symbolic translation or make the broader trusted ownership plan kernel-checked.

ADRs 0089, 0091, and 0092 progressively replace the original two-consumer
cleanup slice. A total `ControlOutline` supplies checker reachability and
structured body identity before checking; successful checking seals retained
block, branch, loop, exposure, route, assignment, trap, and concrete class-drop
plans. Exact `FieldAssignmentAction` and `TemporaryDropAction` records add the
last replacement/temporary-cleanup sites, link them to checker-authored
`ValueTransferKey`s and terminal class-drop recipes, and participate in
callable-wide reconciliation. The checker consumes the outline; VC, SVM,
interpreter, and LLVM consume its retained typed form without reconstructing
syntax flow. That closes criterion 3 under its operational boundary.

Criterion 4 is closed for the current admitted native boundary. A deterministic
typed test-case IR is rendered to Sable source; it is distinct from the retained
production control/action plan that closes criterion 3. The scalar family
exhausts admitted widths and
arithmetic operations over bounded cases and generates comparisons,
conversions, calls, branches, and loops with per-case-observable batch results.
Each result is validated as zero or one before bit-packing; any other native
`i32` takes a reserved exit status outside the valid seven-bit batch range.

The ownership family runs every generated subject in its own process and
compares the exact checked `VerifiedProgram` in the interpreter with Clang
`-O0` and `-O2`. Ordered allocation/free traces cover admitted fixed-owner
class moves and revival, shared and unique Boolean/`u32` array borrows,
three-deep fallthrough and early-return cleanup, loop-carried class
replacement, Boolean-array affine-option present/take/none paths, and the
admitted mutable `Integer` receiver call. Two out-of-bounds probes additionally
pin native trap payloads, live-owner state, and the no-unwind rule; their
interpreter side is explicitly a derived, unverified AST probe and is not
verified-call evidence. The generator also pins fail-closed diagnostics for
the deliberately unadmitted `option<class>` and discarded class-result paths.
Whole-array owner rebinding remains outside LLVM admission rather than an
untested admitted composition.

## Consequences

`docs/PLAN.md` records C0 as complete. Generic owner slots are no longer blocked
by the consolidation gate; their own feature and evidence gates still apply.

The shared place and ownership representations close the admitted
checker-to-VC effect boundary; they are not a mechanized proof that the Rust
translation is correct. The retained structured-control representation now is
consumed across checker, proof, formal, interpreter, and native paths and
contains the cleanup-bearing action sites needed for criterion 3. It is not a
full expression CFG or a mechanized translation proof. Stages may still consume
an exact action and then reject a value shape outside their admitted subsets;
dynamic liveness and concrete representation remain consumer state.

Required CI becomes slightly slower because native generated differential tests
require Clang. Validated scalar Boolean cases are bit-coded in batches of at
most seven, leaving exit status 255 to expose any non-Boolean native return, so
errors cannot cancel in an aggregate result. Ownership cases instead use one
process and one ordered lifetime trace per case, making result disagreement,
leaks, double frees, wrong cleanup routes, and unexpected unwind independently
observable at both optimization levels.
