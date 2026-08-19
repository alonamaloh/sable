# External adversarial review guide

This is an invitation to try to break Sable and a reproducibility guide for
doing so. It is **not** an external audit, evidence that an external reviewer
has participated, or proof that Sable is sound. A green run establishes only
the claim made by that particular test over its admitted subset.

The evidence this guide depends on is versioned: `4b4f93d` closes the latest
known call-evaluation defects, `208a46a` adds the ownership interaction matrix,
`a18ec36` records the incident ledger, `6450253` adds the curated mutation
harness, and `2ad556d` records its first complete baseline. Use a full commit
hash when reporting a new result.

## What to attack

The highest-value target is a program that passes `sable check`, whose
generated obligations Lean accepts, but whose checked interpreter execution
contradicts the proved contract. Also valuable are an ownership or authority
violation accepted before proof, an ordinary source program that reaches a
compiler panic instead of a named refusal, and a disagreement between the
interpreter, Lean SVM evaluator, contract monitor, or admitted native backend.

The current [incident ledger](SOUNDNESS-INCIDENTS.md) makes these the priority
surfaces:

| Surface | Adversarial variations | Prior evidence |
|---|---|---|
| Call evaluation and ownership overlap | free/constructor/method/sealed calls; shared, unique, and move arguments; receiver versus argument; root versus direct field; loan-before-effect, effect-before-loan, and nested effect | VF-08, VF-09, AI-05, AI-08 |
| Mutation discovery and state joins | loop conditions and bodies, branches, early returns, initializers, exposure, whole-owner replacement, field mutation, cleanup, and traps | VF-01, VF-02, VF-04, VF-07, NM-06–NM-09 |
| Admission versus consumer proof domain | traits, generics, externs, resources, raw values, aggregates, unit results, and nested owner storage; prefer positive-domain probes over guesses from old blacklists | AI-03, AI-04, AI-07, ICE-01–ICE-03 |
| Retained-plan reconciliation | remove, duplicate, reorder, or mis-key one ownership/control action; revisit the same source site from multiple symbolic paths | ICE-02, NM-03, NM-04, NM-10 |
| Evidence-channel agreement | choose a result that distinguishes stale from fresh state, run both optimization levels, and make monitor precedence or snapshots observable | RD-01–RD-03 |

For every failing probe, add its reverse-order or disjoint-owner control when
one exists. Alpha-renaming, an unreachable independent owner, and reordering
independent effects are useful metamorphic controls: they should not change an
admission or execution result.

## Trusted base and threat model

Today Sable makes a Stage 1 claim. Lean checks the generated propositions, but
the Rust parser, type/ownership checker, VC generator, Lean emitter, and their
choice of propositions remain trusted engineering. The checker-authored
ownership plan and retained typed control/action plan remove duplicated policy
and fail closed on mismatched consumption; they are trusted Rust data, not a
mechanized proof of source translation.

The formal SVM is the normative machine model for its admitted subset. Its
functional evaluator agrees with its rules by theorem, and the differential
test compares that evaluator with the Rust interpreter. This does not validate
VC generation or cover source shapes outside the SVM gate. LLVM lowering has a
separate fail-closed admitted subset and differential evidence at Clang `-O0`
and `-O2`; the emitter, hosted runtime, and Clang are not kernel-verified.
Foreign contracts and explicit assumptions are audited boundaries, not proved
implementations, and change the reported verification status accordingly.

The kernel-checked transition certificates are deliberately narrower still:

- explicit unique-borrow calls certify selected fresh-state write-back (and
  the recorded length relation for arrays);
- local and direct-`self` slot take/put certify only the observed structural
  sequence update.

They do not prove complete effect discovery, loan or move non-overlap,
evaluation scheduling, index or snapshot provenance, incoming-owner
provenance, loop havoc, general moves, cleanup, traps, or complete source
translation. See [ADR 0087](decisions/0087-call-havoc-has-a-kernel-checked-transition-certificate.md),
[ADR 0090](decisions/0090-ownership-and-mutation-effects-have-one-checked-plan.md),
[ADR 0092](decisions/0092-structured-control-is-sealed-without-claiming-an-expression-cfg.md),
and [ADR 0093](decisions/0093-owner-slots-are-not-copy-arrays.md) for the exact
boundaries.

## Minimized historical witnesses

These files preserve small regressions on current `main`; most now fail before
the historical bad proof can be reproduced. The integration matrix retains
separate proof/runtime twins where the current checker can still admit the
source safely.

| Boundary | Current witness and expected result |
|---|---|
| Mutable call state | [`stale_state_after_call.sable`](../corpus/must-fail/stale_state_after_call.sable): false stale post fails in Lean |
| Loop mutation state | [`owned_loop_stale.sable`](../corpus/must-fail/owned_loop_stale.sable): false stale post fails in Lean |
| Loan plus move in one call | [`borrow_moved_in_call.sable`](../corpus/must-fail/borrow_moved_in_call.sable): `borrow.moved_in_call` |
| Pending loan plus nested mutation | [`borrow_conflict_nested_mutation.sable`](../corpus/must-fail/borrow_conflict_nested_mutation.sable): `borrow.conflict` |
| Reverse evaluation-order control | [`nested_mutation_before_loan.sable`](../corpus/verifies/nested_mutation_before_loan.sable): verifies; the mutation completes before the loan |
| Implicit receiver after move | [`method_receiver_after_move.sable`](../corpus/must-fail/method_receiver_after_move.sable): `class.use_after_move` |
| Sealed loan plus nested move | [`borrow_moved_in_sealed_nested.sable`](../corpus/must-fail/borrow_moved_in_sealed_nested.sable): `borrow.moved_in_call` |
| Trait proof-domain mismatch | [`trait_borrow_call_unsupported.sable`](../corpus/must-fail/trait_borrow_call_unsupported.sable): `type.trait_param_unsupported`, not an ICE |

The four tests in
[`ownership_adversarial.rs`](../compiler/tests/ownership_adversarial.rs) add
bounded pairwise coverage, proof/interpreter oracles, metamorphic controls, and
three isolated direct false-post twins. The ledger is the authority for an
incident's exposure window and evidence classification; do not infer either
from a current must-fail file alone.

## Reproduce the evidence

Run from the repository root. Install the stable Rust toolchain, `elan`, the
pinned toolchain in `lean/lean-toolchain`, and Clang for native tests.

Build the complete Lean prelude and formal machine definitions:

```sh
(cd lean && lake -Kjobs=1 build)
```

Run the pairwise ownership interaction oracles:

```sh
SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1 \
  cargo test --locked --manifest-path compiler/Cargo.toml \
  --test ownership_adversarial -- --test-threads=1
```

Run all 20 curated trusted-semantics mutations against the committed `HEAD`:

```sh
python3 tools/soundness_mutations/runner.py --workers 2 \
  --report /tmp/sable-mutations.json
```

The runner archives the commit and excludes uncommitted files. To reproduce
the recorded 16-semantic/4-structural-kill baseline exactly, add
`--revision 6450253`. Interpret a survivor as an investigation request, not as
evidence of safety; the manifest is curated and has no whole-compiler mutation
score. See the [harness documentation](../tools/soundness_mutations/README.md)
and [baseline](../tools/soundness_mutations/baselines/6450253.json).

Run the complete positive, must-fail, dynamic, and dynamic-fail corpus:

```sh
SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1 \
  cargo test --locked --manifest-path compiler/Cargo.toml \
  --test corpus -- --test-threads=1
```

Run the Rust-interpreter versus Lean-SVM differential:

```sh
SABLE_LEAN_JOBS=1 \
  cargo test --locked --manifest-path compiler/Cargo.toml \
  --test svm_diff -- --test-threads=1
```

Run the required interpreter versus Clang `-O0`/`-O2` native gates, including
generated cases and CLI/ABI/trap checks:

```sh
SABLE_REQUIRE_CLANG=1 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1 \
  cargo test --locked --manifest-path compiler/Cargo.toml \
  --test llvm_diff --test llvm_generated_diff --test llvm_cli \
  -- --test-threads=1
```

Proof timing is release instrumentation, not a deterministic correctness or
performance gate. Prepare the stated cache condition yourself, use a clean
worktree, and give the machine a stable honest label:

```sh
SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1 \
SABLE_PROOF_TIMING_CACHE_MODE=warm-artifacts \
SABLE_PROOF_TIMING_MACHINE="$(hostname)-external-review" \
SABLE_PROOF_TIMING_OUT=/tmp/sable-proof-timing.json \
  cargo test --locked --manifest-path compiler/Cargo.toml \
  --test proof_timing -- --ignored --nocapture --test-threads=1
```

Use `cold-roots` instead of `warm-artifacts` only after honestly preparing that
state. Keep the resolved machine label stable across a series. The runner
records the full revision, toolchains, machine label, cache label, per-subject
timings, and aggregate statistics.

## Report a finding

When filing an issue or proposing a regression patch, include:

1. the full base commit, `git status --short`, platform, `rustc --version`,
   `clang --version` when relevant, and `(cd lean && lake env lean --version)`;
2. one minimized `.sable` witness and the exact command used;
3. the expected and actual diagnostic, proof result, interpreter result, and
   native result—distinguish “accepted invalid” from “Lean accepted a false
   contract”;
4. for a verified-false claim, both Lean acceptance and an independently
   observable contradiction, such as a checked-interpreter result or monitor
   failure; include the contract and concrete value, not only a compiler log;
5. any `unsafe`, `extern`, audit, `defer`, or `assume` boundary in the closure;
6. a reverse-order, disjoint-place, or alpha-renamed control when applicable,
   plus the smallest suspected checker/plan/VC/native boundary.

Preserve a fixed finding as a minimized regression and add it to
[`SOUNDNESS-INCIDENTS.md`](SOUNDNESS-INCIDENTS.md) with its evidence class,
exposure window, root cause, structural fix, discovery mode, and certificate
boundary. A compiler panic, runtime disagreement, or accepted ownership defect
is important evidence, but it must not be relabeled a false theorem without the
proof/runtime pair.
