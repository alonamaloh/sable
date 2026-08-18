# ADR 0082 — quantifier instantiation with omega as the engine

**Decided 2026-08-18.** `sable_auto` gains a second dedicated tier,
`sable_instantiate`: apply every hypothesis with leading `Int` binders
at the index atoms in scope, keep the instances a relevance filter
accepts, and let `omega` finish. Together with `Seq` normalization, ite
splitting, and `subst_eqs`, it closes the pointwise array-update class
— the `have h := hyp i (by omega) …; omega` scripts that were the
largest mechanical family left in the corpus.

## Context

A loop that stores through `a.set p v` owes pointwise obligations at
exit: `∀ i, guards → P ((a.set p v).get i)`, split by `i = p`. The
facts that close both branches are already hypotheses — the loop
invariant instantiated at `i`, the store-slot facts at `p` — and every
hand proof of the shape is the same three moves: normalize `get`/`set`,
case on `i = p`, instantiate a quantified hypothesis and hand the rest
to `omega`.

`grind` closes some of these — measured at ~33M heartbeats on the
hashmap exemplars, two thirds of its budget and past the
expensive-automation bar, so the warning policy itself routes them to
`discharge` scripts. The obvious cheap variant is not cheap: `grind
only` (no global E-matching) costs the *same* 30–50M on the same goals
— the expense is E-matching the fifteen quantified local hypotheses,
not the global lemma set. A budgeted `grind only` tier was built,
measured, and removed in favor of this design.

Two facts make the replacement small:

- `omega` consumes implications and disjunctions over opaque `Int`
  atoms, so a guarded instance `0 ≤ i → i < cap → occ.get i = 0 ∨ …`
  can be asserted *whole* — no guard discharging, no witness surgery;
  an instance whose guard is false is inert, not wrong.
- The instantiation ground set is visible in the goal: the closed index
  arguments of `Seq.get`/`Seq.set` applications, plus the `Int`
  variables in scope.

## Decision

The tier, sitting before the `simp_all` tiers, under its own slice:

```
sable_slice 20000
  ((try sable_norm) <;> (intros) <;>
   (try simp only [Sable.Seq.len_set] at *) <;>
   (try simp only [Sable.Seq.get_set]) <;>
   (repeat split) <;> (try subst_eqs) <;> sable_instantiate)
```

- `get_set` rewrites the goal only: hypothesis matches would gain ites
  omega cannot read; the hypotheses' original-array atoms are exactly
  what instantiation produces. `len_set` is ite-free and rewrites
  everywhere, connecting bound guards across states.
- `repeat split`, not `split`: a store touches several arrays, one ite
  per array on the same `i = p`; cross-branches are contradictory and
  die in omega. `subst_eqs` then substitutes the positive-branch
  equation — the only congruence this tier ever needs.
- `sable_instantiate` applies each ∀-`Int` hypothesis at up to sixteen
  atoms (two leading binders, cartesian, capped), leaves trailing
  guards as implications, and asserts an instance only if it is a
  `Prop` mentioning a `get` atom of the goal *or of a ground
  hypothesis* — the link often runs through a premise like
  `old.occ.get i = 1`, not through the goal. Unfiltered instantiation
  was measured to bury omega (minutes, then failure); filtered, the
  hashmap exemplars close in under a second each and pass at a 2000k
  grind budget, the audit's cheap-pass bar.

## Consequences

- The pointwise family of discharges deletes; the corpus pins the tier
  the way it pins `sable_cases`.
- What stays: proofs needing real congruence (`f i = f j` from a
  *derived* `i = j`, as in the probe-chain invariants) and existential
  posts needing witnesses. Both are `grind`-or-discharge territory, and
  the probe exemplar closes only at ~33M — correctly a discharge under
  the warning policy.
- A failing obligation pays at most the tier's 20000k slice extra —
  milliseconds on the small contexts where failures live. The slice is
  `sable_slice`, a portfolio combinator: baseline reset so earlier
  tiers' spending does not count against it, hard cap, and the runtime
  timeout demoted to a failure `solve` can catch. It exists because the
  worst case here is data-dependent — on quicksort's chained stores
  (`(a.set i x).set j y`) the per-array ite split fans out and every
  branch runs an omega over the full context, which was measured
  blowing not just this tier but the whole elaboration allowance.
- That measurement forced the standing fragility to a head: tiers ran
  under one shared elaborator cap, so adding a tier made obligations
  that used to finish near the limit die with an uncatchable timeout.
  The portfolio now owns the cost policy — expensive tiers run under
  their own budgets (`sable_slice`, `sable_grind`) — and emitted files
  set `maxHeartbeats 400000`, twice the default, keeping the outer cap
  as a backstop rather than the metering instrument.
