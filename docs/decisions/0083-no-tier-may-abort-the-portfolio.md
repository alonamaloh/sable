# ADR 0083 — no tier may abort the portfolio

**Decided 2026-08-18.** Every data-dependent tier of `sable_auto` runs
under `sable_slice`. A tier that dies on a *runtime* error — heartbeat
exhaustion, or a simp rewrite cycle hitting the recursion limit — fails
its alternative and the next tier runs; it no longer aborts the whole
obligation. `sable_grind` distinguishes a genuine budget exhaustion
from a runtime death below budget and reports the latter as itself.

## Context

Free-list obligations were failing with `maximum recursion depth has
been reached` out of the bare `simp_all` tier. The mechanism, reduced
to four hypotheses: resource code carries view equations
(`view6 = initial alloc5 mem`, `state = take view6 0`,
`free8 = takeFree view6 0`) beside projection facts
(`free8.allocator = state.allocator`), and the prelude's
projection-composition simp lemmas (`((initial a r).takeFree 0)
.allocator = a`) rewrite composites back to *bare variables*. Oriented
as rewrite rules by `simp_all`, the two directions meet in a cycle —
`alloc5 → state.allocator → (take view6 0).allocator →
view6.allocator → (initial alloc5 mem).allocator → alloc5` — that
simp's own loop detection does not see through the multi-step
reduction. The goal must mention the looping variable for the cycle to
arm, which is why it strikes call-precondition obligations
(`canPutFree state _`) and not the minimal contexts.

The deeper defect: that recursion error is a runtime exception, and
`solve`/`first` do not catch runtime exceptions. The portfolio's later
tiers — in particular the `subst_eqs`-first tier, which is *immune*
(substitution eliminates the variables, leaving nothing to cycle) —
never ran. An obligation was reported unprovable by a tier crash while
a tier that handles it sat behind the crash. The same escape hatch
explained the earlier heartbeat deaths (ADR 0082); this closes it for
every error class at once.

## Decision

- `sable_slice` wraps tiers 3–8 (everything data-dependent; `sable_grind`
  keeps its own budget machinery). The slice already demotes runtime
  exceptions to ordinary failures; the omega and simp tiers get 100000k
  slices — a quarter of the emitted elaboration allowance, above any
  measured success — and the instantiate tier keeps its 20000k.
- `sable_grind`'s catch checks spent heartbeats: below budget, the
  failure is reported as `grind failed: <original error>` rather than
  as budget exhaustion — a recursion death inside grind's own simp is
  not "too expensive", and saying so misdirects the user toward a
  budget knob that will not help.

## Consequences

- The bare-`simp_all` recursion on view-equation contexts becomes a
  clean tier failure; obligations behind it get their full portfolio.
- The prelude's projection-composition lemmas stay `@[simp]`: they are
  correct and load-bearing; the fix is containment, not lemma surgery.
  A future portfolio change could pre-`subst_eqs` even the bare
  simp_all tier, but that reorders long-standing tier semantics for no
  measured win.
- A tier success that needs more than its slice would now fail where it
  once (dubiously) succeeded near the shared cap; the corpus gate is
  the arbiter that no such obligation exists.
