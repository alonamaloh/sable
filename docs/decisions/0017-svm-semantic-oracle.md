# ADR 0017 — The SVM semantic oracle: agreement theorems and differential testing

**Decided 2026-08-10 (Alvaro).**

Design §10 claims the machine is "small-step, deterministic", and §10.1's
stage-1 trust posture leans on the formalization being "executably
testable" against the reference interpreter. This ADR records how both
became artifacts instead of intentions.

## 1. Determinism is proven via evaluator agreement, not rule-pair analysis

The obvious determinism proof — pairwise mutual exclusion over every two
rules for the same syntax node — is quadratic in rules and rots as rules
are added. Instead, `lean/Sable/SVMEval.lean` defines functional
presentations (`evalE : Expr → EOut`, `stepF : Config → Option Config`)
and proves agreement with the inductive relations in **both directions**
(`eval_iff_evalE`, `step_iff_stepF`). Determinism, totality, and progress
fall out as one-line corollaries, and the agreement proofs are the
standing regression test of the rule system: an overlapping pair of rules
with different outcomes, or a missing rule, makes one direction
unprovable. All kernel-checked, core-only, no mathlib.

## 2. The machine is total (ADR 0005 res. 1, discharged)

`undef` joins `done` and `trapped` as a terminal outcome (`Abort = trap |
undef` at the expression layer). Every state the static semantics must
exclude — ⊥-reads, type confusion, out-of-range literals, negative
`alloc_array` lengths — has a defined `undef` outcome, so pillar 1 holds
literally and the target soundness statement sharpens to "verified programs
never reach `undef`". This machine theorem does not by itself validate the
trusted Rust VCs selected from source. Operand shape is decided where the operand is *produced*
(left-to-right): once a left operand is known ill-shaped, the right
operand is never evaluated, keeping abnormal-outcome identity
deterministic without new ordering decisions.

## 3. The differential harness compares outcomes, not traces

The two executables disagree on step granularity by design (the machine
unfolds `while`; the interpreter walks trees; contract monitoring exists
only on the interpreter side), so the comparable artifact is the
**terminal outcome with payloads**: `done <val>` / `trap <name> <data>` /
`undef`. The wire format is defined twice and must match character for
character: `Config.render` (Lean) and `svm::canonical_outcome` (Rust).
Mapping the interpreter's human-facing trap messages onto structural
machine traps lives only in `compiler/src/svm.rs` — the interpreter
itself is unchanged.

`compiler/tests/svm_diff.rs` lowers every function in `corpus/svm-diff/`
(strictly: outside-subset constructs are hard failures, never skips),
runs both sides, and generates a single Lean driver so the whole corpus
costs one `lake env lean` (~0.5s in `cargo test`).

## 4. The differential corpus

`corpus/svm-diff/` is a non-verifying corpus directory (like
`corpus/test-fails/`, traps are expected outcomes; the check hook exempts
it). Subjects are zero-argument functions in the machine's core subset,
chosen to pin the decisions ADR 0005 made normative: value trap beats OOB
on stores, index trap beats both, left operand wins, short-circuit
guards, Euclidean `/`/`%` at the signed extremes, OOM at the capacity
parameter (`cap = 50_000_000`, matching the interpreter's limit). Loop
`variant`s are the one asymmetry: mandatory in the surface language and
monitored by the interpreter, erased by the machine — so a diff subject's
variants must hold.

First result: 34 subjects, zero divergences; an injected lowering bug
(`%` rewired to `/`) is caught as two divergences.

## Known, recorded asymmetry

A negative `alloc_array` length is `undef` in the machine (excluded by
`u64` typing, ADR 0005 res. 11) but an OOM trap in `interp.rs`. Both are
unreachable in checked programs and unreachable from the subset (the
front end types the length `u64`), so the harness cannot observe the
difference; recorded here so nobody rediscovers it as a bug.

## Consequences

- "Deterministic" in design §10 now cites theorems, not intent.
- New machine rules must extend `evalE`/`stepF` and the agreement proofs
  in the same change — the build fails otherwise, which is the point.
- Calls + frames (ADR 0005 res. 4) and ghost transitions remain; each
  extension inherits the same obligation: rules, evaluator, agreement,
  and diff subjects together.
