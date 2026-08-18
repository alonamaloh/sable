# ADR 0084 — facts are declared, not discovered

**Decided 2026-08-18.** A ghost theorem may carry `#[fact]`
(`/// theorem #[fact] valIn_nil …`), which emits it `@[sable_fact]`.
The instantiation tier gains a second stage, `sable_instantiate_all`,
that applies every marked theorem at the argument tuples its conclusion
patterns pick out of the goal and hypotheses — the machine version of a
discharge script's `have h := valIn_nil zarr 0 0 (by omega)` — with the
guards left as implications for omega. Seventy-nine corpus theorems are
marked; the largest remaining mechanical discharge family falls.

## Context

One hundred twenty-eight of the corpus's remaining discharge scripts
reference a ghost theorem, and the recurring shape is instantiation:
apply `valIn_nil`/`intVal_pos`/`ediv_decomp` at specific arguments,
discharge the guard `by omega`, hand omega the fact. `#[unfold]`
(`@[simp]`) cannot express these — they are guarded facts and
inequalities, not rewrites — and `grind` was measured far past the
warning bar on this corpus. The hypothesis half of the shape is already
automated (ADR 0082); the missing half was global theorems, which no
tier could see.

Marking is explicit because visibility is a cost decision: every marked
theorem is matched against every obligation of its module and its
importers, so the author declares which lemmas are automation surface,
the same way `#[unfold]` declares a rewrite.

## Decision

- **Surface**: `#[fact]` after the `theorem` keyword, stripped by the
  scanner like `#[unfold]`; a misplaced or misspelled attribute stays in
  the item's text for Lean to reject at the item's span
  (`corpus/must-fail/fact_on_def.sable` pins this). Emission adds
  `@[sable_fact]`, a core label attribute registered by the prelude.
- **Matching**: for each marked theorem, the leading non-`Prop` binders
  are the instantiation variables and everything behind them must be
  `Prop` guards. The conclusion's constant-headed applications that
  mention those binders are patterns; `isDefEq` against the obligation's
  occurring applications (goal first, then hypotheses newest-first —
  the atoms that decide an obligation live in its own tail, not in the
  ambient invariants) reads off the tuples. No blind enumeration: an
  instantiation exists only where its pattern already occurs.
- **Cost discipline, measured not guessed**: pattern-head interning with
  a per-theorem shape cache (keyed by name and type hash), a
  head-indexed atom pool with capped buckets, a per-theorem trial
  budget, and a per-obligation fact cap. The stage runs as its own
  `solve` alternative behind the hypothesis tier under a separate
  `sable_slice`, so global matching can never starve the hypothesis
  tier's slice — the first integration did exactly that and took
  working obligations down with it. `SABLE_DEBUG_INST=1` prints the
  asserted facts for a failing obligation.

## Consequences

- Discharge scripts of the instantiate shape delete; the audit is the
  measure, and the files verifying without them is what pins the
  feature.
- A marked theorem whose conclusion has no constant-headed application
  over its binders can never match and is dead weight; the shape cache
  reports it as unusable silently. Rewrite-chain scripts whose residue
  is nonlinear (`Int.zero_mul` after the rewrite) stay hand-proved:
  omega cannot multiply atoms.
- Two do-notation lessons are now paid for twice and recorded once:
  a monadic bind inside `&&`/`while` conditions hoists ahead of the
  guard (a panic on `bindingDomain!`), and walking a telescope by
  instantiating dummies destroys the binder-looseness a later collector
  keys on.
