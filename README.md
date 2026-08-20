# Sable

[![CI](https://github.com/alonamaloh/sable/actions/workflows/ci.yml/badge.svg)](https://github.com/alonamaloh/sable/actions/workflows/ci.yml)

Sable is an imperative, C-flavored language designed so **every function carries
a machine-checked proof of its contract**. One file interleaves two languages: a
C-like program language with no undefined behavior and an ownership-based
memory model, and a Lean 4 proof language living entirely on `///` lines.
The syntax is C-shaped; the semantics are intentionally not C's: evaluation is
defined, integer arithmetic is checked unless explicitly wrapped, division is
Euclidean, and unsupported implementation shapes are rejected.

```sable
/// pre  ∀ i j, 0 ≤ i → i < j → j < a.len → a.get i ≤ a.get j
/// post match result with
///      | some i => 0 ≤ i ∧ i < a.len ∧ a.get i = key
///      | none   => ∀ k, 0 ≤ k → k < a.len → a.get k ≠ key
fn binary_search(&[i32] a, i32 key) -> option<u64> {
    mut u64 lo = 0;
    mut u64 hi = a.len;
    /// invariant hi ≤ a.len
    /// invariant ∀ k, 0 ≤ k → k < lo → a.get k < key
    /// invariant ∀ k, hi ≤ k → k < a.len → key < a.get k
    /// variant   hi - lo
    while (lo < hi) {
        u64 m = lo + (hi - lo) / 2;
        if      (a[m] < key) { lo = m + 1; }
        else if (a[m] > key) { hi = m; }
        else                 { return some(m); }
    }
    return none;
}
```

That is not pseudocode.
[`corpus/verifies/binary_search.sable`](corpus/verifies/binary_search.sable)
verifies today. Fold the `///` lines and it reads as plain C with a contract.

## What “verified” means

> **Known release block (2026-08-20):** user-controlled proof text can currently
> introduce `sorryAx` or an unreported axiom. The immediate fail-safe now prints
> `status: Lean accepted; proof dependencies unaudited` instead of `fully
> verified`, but it does not yet close the ingress. Until
> [plan priority zero](docs/PLAN.md#priority-zero-seal-proof-ingress) completes
> the transitive audit, no release should claim axiom-clean verification.

The intended Stage 1 meaning of `status: fully verified` is that every generated
proof obligation was accepted by the pinned Lean kernel with no deferred
obligation, assumed theorem, audited foreign contract, or hidden proof axiom.
Even after the release block is fixed, this is not an end-to-end proof of the
Rust compiler or native backend:

| Claim | Present assurance |
|---|---|
| The generated Lean declarations are accepted | Lean elaborates them, and the kernel checks the resulting declarations and proof terms relative to their environment. Plan priority zero must account for the complete axiom dependency closure before Sable can claim the resulting theorems are valid relative only to the approved base |
| The obligations faithfully model the Sable program | The Rust checker/VC generator remain trusted engineering. The checker authors one exact ownership/mutation plan for admitted moves, calls, loans, receivers, sealed operations, exposures, and loop havoc, and VC generation consumes it fail-closed. One structural control/action model begins as a checker-consumed outline and is then retained for VC, SVM, interpreter, and LLVM paths, including exact traps, replacements, discarded class temporaries, and concrete class-drop links. Explicit unique-borrow write-back, successful local/direct-`self` slot take/put write-back, and checker-recorded argument-schedule alias safety additionally have narrow Lean-checked certificates; their Rust discovery and source provenance remain trusted. Neither plan is a mechanized proof of source translation |
| The interpreter matches the formal SVM subset | The Lean rules and functional evaluator agree by theorem; Rust and Lean outcomes are compared differentially |
| Native execution matches Sable semantics | Lowering is fail-closed from the exact `VerifiedProgram`; curated subjects, range-checked bit-distinguishable scalar/control batches, and individually traced ownership cases across the current admitted native boundary are compared with the interpreter under Clang `-O0` and `-O2`. The generator is test-only typed case IR rendered to source—not the compiler's retained production control/action plan—and the handwritten LLVM emitter is not kernel-verified |

See [the architecture](docs/ARCHITECTURE.md) and
[design §10.1](docs/design/sable-language-design.md#101-the-trusted-base-in-stages)
for the complete trust model.

All six C0 consolidation criteria are closed. The retained authority is a
structured typed control/action plan, not a full expression CFG or a mechanized
source-translation proof; individual stages still fail closed outside their
admitted subsets.

**A program that does not verify does not build.** Integers are exact — every
overflow, division, and index is an obligation rather than undefined behavior
or a silent wrap. There is no SMT solver: obligations are discharged by an
automation portfolio inside Lean. Lean elaborates every emitted declaration,
and the kernel checks the resulting declaration and proof term relative to its
environment. Priority zero additionally requires Sable to audit the transitive
axiom dependencies of everything the kernel accepts.

## Try it

Prerequisites are a stable Rust toolchain with Cargo and
[elan](https://github.com/leanprover/elan), which installs the repository's
pinned Lean/Lake toolchain. Clang is optional: Sable can emit textual LLVM IR
without it, but compiling that IR and running the native differential suite
requires Clang.

```sh
# from the repository root
export LEAN_NUM_THREADS=0 LEAN_IMPORT_WORKERS=1
test ! -e .sable-out/daemon.sock && test ! -L .sable-out/daemon.sock
(cd lean && lake --quiet build Sable)
CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 \
  cargo build --locked --release -j1 --manifest-path compiler/Cargo.toml
compiler/target/release/sable doctor

compiler/target/release/sable check corpus/verifies/div_round_up.sable
compiler/target/release/sable test -M corpus/verifies corpus/tests/test_arith.sable
compiler/target/release/sable explain-type 'option<[bool]>'
compiler/target/release/sable daemon   # optional warm checker, ~10x faster checks
```

The exported Lean settings disable the hardware-sized task pool and keep import
work to one worker. Supported test commands additionally use one Cargo job, one
Rust test thread, and at most two explicit outer verification workers.

`sable doctor` checks the checkout, Cargo, Lake, the exact version named by
`lean/lean-toolchain`, the built prelude, hosted runtime, and Clang. Missing or
mismatched verification prerequisites fail the command; a missing prelude or
Clang is reported as a warning because the prelude can be built on demand and
native execution is optional. When `SABLE_CLANG` is set, that executable is
authoritative: an unusable value is reported without falling back to another
Clang, matching the native differential harnesses.

`sable explain-type '<type>'` first shows which positions the recursive parser
can lower a closed spelling in, then groups the compiler's actual stage gates
under the verified, executable, formal-machine, and native evidence profiles.
Refusals include their machine-matchable diagnostic name and current reason.
The parser-position section is intentionally not the full language-admission
answer: the generated [type matrix](docs/type-matrix.md) additionally runs
constants, monomorphization, and checking and distinguishes call binding modes.
The profile section queries the same gates as the generated
[shape-admission matrix](docs/shape-admission.md), without a second support
list. Because the command has no module argument, declaration-relative class
and record names are reported as unknown rather than guessed.

**[Start with the tutorial →](docs/TUTORIAL.md)** — a short tour of the
language, whose examples are themselves verified by CI.

## Status

A research project, developed in the open, and further along than that usually
implies. Verified today: sorting (quicksort and the merge kernel with full
`sorted ∧ permutation` specs), binary search, hex/varint/UTF-8 codecs with
kernel-checked round-trip theorems, a JSON parser verified against the RFC 8259
grammar, a generic growable `Vec<T>`, a hash map verified against the
linear-probing contract, an in-band free-list allocator with mandatory client
leases, and the pillar: **arbitrary-precision `Nat` and signed `Integer` —
comparison, addition, subtraction, schoolbook multiplication, division, and
gcd, each verified against a one-line spec over its abstraction function**, and
lowered to native code.

Those achievements cross different implementation boundaries. Each cell names
the evidence for the showcase itself; qualified cells deliberately mark only
partial coverage rather than borrowing credit from a supported primitive:

| Showcase | Lean verification | Dynamic contract test | Formal-SVM differential | Native differential |
|---|---:|---:|---:|---:|
| Quicksort and merge | yes | yes | — | — |
| Binary search | yes | — | — | — |
| Hex, varint, and UTF-8 codecs | yes | yes | — | — |
| JSON lexer/parser | yes | yes | — | — |
| Generic `Vec<T>` and hash map | yes | yes | — | — |
| In-band free-list allocator | yes | yes | primitives only (root/header subjects) | — |
| `Nat` and `Integer` | yes | yes | — | selected exact call closures at `-O0`/`-O2` |

The four evidence profiles are intentionally distinct: `sable check`
is the verified-source profile; `sable test` is a Lean-free development
interpreter; the formal SVM covers a strict machine subset; and
`sable build --emit-llvm` covers a separately gated native subset. Unsupported
formal or native shapes fail instead of being skipped. The generated
[type × context matrix](docs/type-matrix.md) records what source forms are
admitted today; the generated [shape × stage table](docs/shape-admission.md)
shows which of those forms each checker, interpreter, SVM, and LLVM boundary
accepts. Formal device profiles are a separate concept: a selected profile
(currently `uart-poll-v1`) is named and content-hashed in the check report and
proof artifact, and its Lean-checked semantics does not become an audited
foreign assumption.

Not there yet: mechanized source-translation soundness, broad backend coverage
for aggregates, concurrency, floating-point types, and much of a standard
library. See
[`docs/PLAN.md`](docs/PLAN.md) for the provisional priorities and deliberately
deferred scope.

## Reading further

- [`docs/TUTORIAL.md`](docs/TUTORIAL.md) — the language in a dozen examples.
- [`corpus/`](corpus/) — the real documentation: more than 700 verification,
  must-fail, dynamic, paired, SVM-differential, and LLVM-differential programs.
  CI keeps all of it green, so it never goes stale.
- [`docs/design/sable-language-design.md`](docs/design/sable-language-design.md)
  — the normative design: syntax, contracts, ownership, ghost code,
  termination, escape hatches, and the machine model.
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) — how the compiler works, and
  [`docs/decisions/`](docs/decisions/) for the reasoning behind each settled
  question.
- [`docs/SOUNDNESS-INCIDENTS.md`](docs/SOUNDNESS-INCIDENTS.md) — the
  evidence-qualified ledger of false proofs, accepted-invalid programs,
  semantic divergences, fail-open ICEs, and pre-merge near misses.
- [`docs/ADVERSARIAL-REVIEW.md`](docs/ADVERSARIAL-REVIEW.md) — an evidence-first
  guide for external breakage attempts, exact reproducer commands, and honest
  reporting of proof/runtime findings.
- [`tools/soundness_mutations/README.md`](tools/soundness_mutations/README.md)
  — the curated trusted-semantics mutation protocol and immutable result sets.
- [`tools/native_perf/README.md`](tools/native_perf/README.md) — the fail-closed
  native-performance protocol, including canonical blockers and the narrow
  C-comparable subset.
- [`tools/proof_timing/README.md`](tools/proof_timing/README.md) — the exact
  release-only cold-roots/warm-artifacts protocol for comparable
  verification-wall-time evidence, including cache, revision, and
  subject-manifest checks; recorded pairs are indexed
  [here](tools/proof_timing/baselines/index.json).
