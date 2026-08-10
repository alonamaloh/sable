# ADR 0011 — A heartbeat budget on the grind tier, with an early warning

Date: 2026-08-10. Status: accepted, implemented.

## Context

`sable_auto` ends in `grind`. On goals grind can close, it closes fast;
on goals it cannot close, its E-matching self-instantiates quantified
hypotheses (the ubiquitous `∀ k, 0 ≤ k → k < a.len → …` element-bound
facts are perfect fuel) up to its term-generation threshold — minutes of
CPU per failing obligation. The cost lands exactly where iteration speed
matters most: a file under development, whose obligations do not all
have discharge scripts yet. Measured during the bignum work: single
undischarged obligations burned 10–20 minutes of grind churn; the entire
green corpus, by contrast, verifies in ~2 minutes — and, measured at
budget 1, currently closes **every** obligation before the grind tier.

There is a second, quieter failure mode: an obligation that grind *does*
close, but slowly. It verifies today and falls off a cliff after a
toolchain bump shifts heartbeat costs — with no prior signal.

## Decision

1. **Budget.** `sable_grind` (now the portfolio's last tier) runs grind
   under `sable.grindHeartbeats` — a Lean option, in thousands of
   heartbeats like `maxHeartbeats`, default **50000** (a quarter of
   Lean's per-declaration default; grind's floor on trivial goals is
   ~58). Heartbeats, not wall-clock: deterministic-ish and
   machine-independent, so the corpus can be held to it in CI.
   Exceeding the budget fails *that alternative* (the runtime timeout
   is caught and rethrown as a plain tactic failure), so the obligation
   fails promptly with a message naming the budget and the option.
   `0` disables the cap.

2. **Early warning at budget/5.** A grind success that spent ≥ 1/5 of
   the budget logs a warning. The compiler maps it through the source
   map and reports it as a first-class diagnostic — obligation name,
   `.sable` clause span, heartbeats spent vs. budget — non-fatal, on
   the success path. The 5× margin is the drift absorber: a pinned-Lean
   upgrade that shifts costs by tens of percent moves a warned
   obligation, not a passing one, over the cliff.

3. **Suggested proof.** On the warning path the goal is re-proved as
   `grind?` (budgeted at 3×, falling back to plain grind), whose
   "Try this:" output is a *minimized* invocation (`grind only […]`,
   `grind => ring`, …). The compiler folds the first suggestion into
   the warning as a ready-to-paste `discharge <obligation> by <tactic>`
   note. This is as far as Lean's tooling goes today: grind's proof
   terms are E-graph/SAT-shaped and do not extract to readable tactic
   scripts, but the minimized invocation pins the lemma set and skips
   the search, which is most of the win.

4. **The corpus is warning-clean, enforced.** The corpus harness fails
   any `verifies/` program that verifies with a warning: an obligation
   near the cliff must get a discharge script while its author still
   remembers why it is true.

5. **Plumbing.** `SABLE_GRIND_HEARTBEATS=<n>` makes the emitter prepend
   `set_option sable.grindHeartbeats <n>` to the generated file (tests,
   CI, and quick experiments; the option itself lives in the prelude).
   The LSP surfaces the warnings at WARNING severity. When
   verification *fails*, budget warnings are withheld — they would be
   noise next to real errors.

## Consequences

- The prelude now imports `Lean` (meta APIs for the elab). Still no
  mathlib; `import Lean` is the compiler's own library and adds only
  cold-start import time.
- Discharge scripts that end in `grind` are unbudgeted (they spliced a
  hand-written tactic; the author opted in). Scripts may use
  `sable_grind` to opt back into the budget.
- Failing obligations now cost at most ~the budget per obligation in
  the grind tier instead of unbounded churn — the triage loop during
  development (the expensive path the bignum session had to work
  around) is bounded by construction.
