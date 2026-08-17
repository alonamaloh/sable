# ADR 0081 — a case-split tier in sable_auto

**Decided 2026-08-18.** `sable_auto` gains a tier that case-splits every
`match` whose scrutinee automation cannot reduce — an abstract variable
or a projection, in the goal or in a hypothesis — and closes the branches
with `contradiction`, then simp/omega. The tier is packaged as a
standalone tactic, `sable_cases`, usable in `discharge` scripts. It
deleted all eighteen corpus discharges of the match-post shape.

## Context

A postcondition written as a `match` over an option parameter or field
generates one obligation per control path, and on the present path the
obligation has this shape: goal `match o with | some v => P v | none => Q`,
hypotheses `o ≠ none` (or `o.is_some`) and `result = o.value`. Nothing in
the portfolio could close it: the match does not reduce on an abstract
scrutinee, `omega` sees no arithmetic, `simp_all` cannot pick an arm, and
`grind` exhausts its heartbeat budget case-splitting everything *except*
the one term that matters. Every such obligation cost a hand `discharge`
with the identical script — `cases o with | none => exact absurd rfl
h_path | some v => simp_all` — written eighteen times across the option
corpus, and again for every new option-shaped cell the type-matrix
campaign opens. The same shape appears hypothesis-side when a callee's
match-form post instantiates at an abstract argument chain.

Two attacks were considered:

- **Reshape the obligation at emission** — turn a match-form post into a
  guarded clause pair (`x.is_some → …` / `x = none → …`) that the
  existing portfolio handles. Rejected: the match is the *user's clause
  text*, spliced into generated Lean verbatim. Rewriting it means the
  Rust side interpreting proof language, which the design forbids
  (design §6; the invariant that there is one proof-language semantics,
  Lean's). Users may still choose the guarded spelling; the compiler
  will not impose it.
- **Teach the portfolio the case split.** A prelude-only change: emitted
  Lean is byte-identical, the type-snapshot oracle sees nothing, and the
  kernel still checks every proof, so the tier cannot mask a false post
  (`corpus/must-fail/nested_option_wrong_post.sable` pins the failure
  path through the new tier).

## Decision

`lean/Sable/Auto.lean` defines `sable_cases`:

1. **Collect** the scrutinees of every matcher application in the goal
   and hypotheses. A scrutinee qualifies only if it is a closed term (a
   match under a quantifier whose scrutinee mentions the bound variable
   cannot be split), is not constructor-headed (those reduce by
   themselves), and its type is a non-Prop inductive with at least two
   constructors — never a proof, never a one-constructor structure.
2. **Split** the first qualifying scrutinee: `cases x` for a variable
   (substituting, so hypotheses specialize), `cases h_scrut : e` for a
   projection (the equation lets `simp_all` specialize hypothesis
   matches). Recurse — a split can expose a nested match, as in
   `option<option<T>>` posts.
3. **Guard against re-splitting.** A projection scrutinee survives its
   own split in hypothesis matches (`cases h :` generalizes only the
   goal), so a scrutinee already pinned by an equation hypothesis
   `e = ctor …` is skipped; without this the recursion never terminates.

The tier sits after the simp_all tiers and before `sable_grind`:

```
sable_cases <;> (first | contradiction | ((try simp) <;> (try simp_all) <;> (try omega)))
```

`contradiction` first because the refuted arm's path fact (`none ≠ none`)
is *frozen for simp_all* in that branch: after `cases`, the branch goal is
a dependent matcher application that mentions the path hypothesis as a
discriminant, and `simp_all` will not rewrite a hypothesis the goal
depends on. A goal-only `simp` reduces the matcher (unfreezing the
hypotheses) before `simp_all` finishes the live arm; `omega` catches
arithmetic residue.

Lean's own `split` tactic was measured and rejected for this portfolio:
on these goals it duplicates the dependent hypothesis telescope
(general + specialized copies, no connecting equation), which sends
`simp_all` into unbounded rewrite recursion.

## Consequences

- The eighteen match-post discharges are deleted; their files verify
  through the portfolio, so the corpus itself pins the tier — a
  regression re-fails `option_param`, `option_field`,
  `member_value_params`, `member_param_import`, and `nested_option`.
- New option-shaped cells stop paying the per-slice discharge tax, and
  the fact-vs-motive emission ordering (ADR 0074) loses its remaining
  sting: hypothesis-side matches split the same way.
- A genuinely false match post costs two extra branch attempts before
  `grind` reports it; measured cost is negligible against the grind
  budget.
- `sable_cases` splits *any* qualifying inductive scrutinee, not just
  `Option` — `Bool` and future sum shapes ride along.
