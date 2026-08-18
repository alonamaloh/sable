import Lean
import Sable.Bounds
import Sable.Seq

/-
Sable prelude: the automation portfolio.

Every VC the compiler emits is a theorem proved `by sable_auto` (unless a
`discharge` block overrides it). The portfolio is deliberately ordered:
cheap closers first, then normalization + omega (the workhorse for range
and overflow VCs), then `sable_instantiate` for pointwise array goals,
then simp_all, then `sable_cases` for match-shaped goals and
hypotheses, then a heartbeat-budgeted `grind`.

`sable_norm` unfolds the Sable bound constants (`u32.max` etc.) to literals
everywhere, since `omega` treats unknown constants as opaque.

`sable_cases` case-splits every `match` whose scrutinee is abstract — a
variable or a projection the match cannot reduce on, in the goal or in a
hypothesis. This is the shape of a match-form postcondition proved on one
control path: the path fact (`o ≠ none`, `o.is_some`) refutes the other
arm, but nothing before the split can see that. Splitting substitutes
variables (`cases o`) and equates projections (`cases h : self.f`), so the
branch closers — `contradiction` for the refuted arm, simp/omega for the
live one — see constructor-form scrutinees. It is also available in
`discharge` scripts directly.

`sable_instantiate` is quantifier instantiation with omega as the
engine: every hypothesis with leading `Int` binders is applied at the
index atoms in scope (`Seq.get`/`Seq.set` indices and `Int` variables),
guards are left as implications — omega consumes those — and a
relevance filter keeps only facts that mention a `get` atom of the goal
or of a ground hypothesis. This closes the pointwise array shape (`∀ i,
… → P ((a.set p v).get i)`, after `Seq` normalization and ite splits)
that `grind` can only close well past the warning bar: the hand proofs
it replaces were all `have h := hyp i (by omega) … <;> omega`. What it
deliberately cannot do is congruence — a goal needing `f i = f j` from
`i = j` (beyond what `subst_eqs` gives after an ite split) stays with
`grind` or a discharge.

`sable_grind` is `grind` under a heartbeat budget
(`sable.grindHeartbeats`, in thousands like `maxHeartbeats`; 0 disables
the cap). Exceeding the budget fails the alternative — bounding what a
*failing* obligation can cost — and a success that spends a fifth of the
budget or more warns and re-runs as `grind?` so the warning arrives with
a minimized `grind only [...]` suggestion, ready to become a `discharge`
script.
-/

namespace Sable

register_option sable.grindHeartbeats : Nat := {
  defValue := 50000
  descr := "heartbeat budget for the `grind` tier of `sable_auto`, in \
    thousands of heartbeats (like `maxHeartbeats`); 0 disables the cap. \
    A goal that grind closes using ≥ 1/5 of the budget produces a \
    warning with a minimized-proof suggestion."
}

open Lean Elab Tactic in
/-- Run a tactic under its own heartbeat slice (in thousands, like
`maxHeartbeats`), with the baseline reset so preceding tiers' spending
does not count against it, and a runtime timeout demoted to an ordinary
failure the portfolio's `solve` can catch. Tiers whose worst case is
data-dependent (branch fan-out over chained stores, omega over a wide
context) run inside this so one obligation's pathology costs a bounded
slice, not the whole elaboration allowance. -/
elab "sable_slice " budget:num tac:tacticSeq : tactic => do
  let start ← IO.getNumHeartbeats
  let run : TacticM Unit :=
    withTheReader Core.Context
      (fun ctx => { ctx with maxHeartbeats := budget.getNat * 1000,
                             initHeartbeats := start }) do
        evalTactic tac
  tryCatchRuntimeEx run fun e => do
    if e.isInterrupt then throw e
    throwError "tier exceeded its heartbeat slice ({budget.getNat}k)"

open Lean Elab Tactic in
elab "sable_grind" : tactic => do
  let budgetK := sable.grindHeartbeats.get (← getOptions)
  if budgetK == 0 then
    evalTactic (← `(tactic| grind))
    return
  let start ← IO.getNumHeartbeats
  let saved ← saveState
  let run (limitK : Nat) (tac : TSyntax `tactic) : TacticM Unit :=
    withTheReader Core.Context
      (fun ctx => { ctx with maxHeartbeats := limitK * 1000, initHeartbeats := start }) do
        evalTactic tac
  tryCatchRuntimeEx (run budgetK (← `(tactic| grind))) fun e => do
    if e.isInterrupt then throw e
    -- a runtime death below the budget (a simp rewrite cycle hitting the
    -- recursion limit, an internal error) is a failure, not exhaustion;
    -- report it as itself, demoted to an ordinary catchable error
    if ((← IO.getNumHeartbeats) - start) / 1000 < budgetK then
      throwError "`grind` failed: {e.toMessageData}"
    throwError "`grind` exceeded its heartbeat budget \
      ({budgetK}k; `sable.grindHeartbeats`)"
  let spent := ((← IO.getNumHeartbeats) - start) / 1000
  if spent * 5 ≥ budgetK then
    -- Expensive success: redo the goal as `grind?` so the "Try this:"
    -- suggestion (a minimized `grind only [...]`) lands next to the
    -- warning. Budget the retry too — worst case we keep the plain
    -- success we already had.
    let warn (suggested : Bool) : TacticM Unit :=
      logWarning m!"expensive automation: `grind` closed this goal using \
        {spent}k of its {budgetK}k-heartbeat budget — \
        {if suggested then "a minimized `discharge` suggestion accompanies \
        this warning" else "consider a `discharge` script"}"
    let retry : TacticM Unit := do
      saved.restore
      run (budgetK * 3) (← `(tactic| grind?))
      warn true
    tryCatchRuntimeEx retry fun e => do
      if e.isInterrupt then throw e
      saved.restore
      run (budgetK * 3) (← `(tactic| grind))
      warn false

section SableInstantiate

open Lean Meta Elab Tactic


/-- Closed `Seq.get`/`Seq.set` index arguments and the full get-applications
in `e`. -/
private partial def collectSeq (idxs : IO.Ref (Array Expr))
    (gets : IO.Ref (Array Expr)) (e : Expr) : MetaM Unit := do
  if !e.hasLooseBVars && e.isApp then
    if let .const n _ := e.getAppFn then
      if n == ``Sable.Seq.get || n == ``Sable.Seq.set then
        let args := e.getAppArgs
        if h : 2 < args.size then
          let idx := args[2]
          if !idx.hasLooseBVars && !idx.hasExprMVar then
            unless (← idxs.get).contains idx do idxs.modify (·.push idx)
          if n == ``Sable.Seq.get then
            unless (← gets.get).contains e do gets.modify (·.push e)
  match e with
  | .app f a => collectSeq idxs gets f; collectSeq idxs gets a
  | .lam _ t b _ => collectSeq idxs gets t; collectSeq idxs gets b
  | .forallE _ t b _ => collectSeq idxs gets t; collectSeq idxs gets b
  | .letE _ t v b _ => collectSeq idxs gets t; collectSeq idxs gets v; collectSeq idxs gets b
  | .mdata _ b => collectSeq idxs gets b
  | .proj _ _ b => collectSeq idxs gets b
  | _ => pure ()

private def isIntTy (t : Expr) : MetaM Bool := do
  let t ← whnf t
  return t.isConstOf ``Int

private def containsAny (e : Expr) (needles : Array Expr) : Bool :=
  Option.isSome <| e.find? fun sub => needles.contains sub

elab "sable_instantiate" : tactic => do
  let g ← getMainGoal
  let news ← g.withContext do
    let idxs ← IO.mkRef (#[] : Array Expr)
    let gets ← IO.mkRef (#[] : Array Expr)
    let goalGets ← IO.mkRef (#[] : Array Expr)
    collectSeq idxs goalGets (← g.getType)
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        collectSeq idxs gets d.type
        -- ground hypotheses (no quantifier) contribute active atoms: the
        -- link to an instantiation may run through a premise like
        -- `old.occ.get i = 1` rather than through the goal
        unless d.type.isForall do
          collectSeq idxs goalGets d.type
    -- goal gets participate in the atom pool too
    for e in ← goalGets.get do
      unless (← gets.get).contains e do gets.modify (·.push e)
    -- candidate index atoms: get/set indices plus Int fvars
    let mut atoms := (← idxs.get)
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        if ← isIntTy d.type then
          unless atoms.contains d.toExpr do
            atoms := atoms.push d.toExpr
    let atomsCut := atoms[0:16].toArray
    let goalAtoms ← goalGets.get
    let mut news : Array (Expr × Expr) := #[]
    let mut seenTys : Array Expr := #[]
    let budget := 96
    for d in ← getLCtx do
      if news.size ≥ budget then break
      unless d.isImplementationDetail do
        let ty ← instantiateMVars d.type
        if ty.isForall then
          if ← isIntTy ty.bindingDomain! then
            let mut frontier : Array Expr := #[d.toExpr]
            for _ in [0:2] do
              let mut next : Array Expr := #[]
              for tm in frontier do
                let tty ← whnf (← inferType tm)
                let mut extended := false
                if tty.isForall then
                  if ← isIntTy tty.bindingDomain! then
                    extended := true
                    for a in atomsCut do
                      if next.size < 64 then
                        next := next.push (mkApp tm a)
                if !extended && tm != d.toExpr then
                  -- an instantiated fact (possibly still guarded by Prop
                  -- implications, which omega consumes); keep it if it is a
                  -- Prop mentioning one of the goal's get-atoms
                  let nty ← inferType tm
                  if (← inferType nty).isProp then
                    if goalAtoms.isEmpty || containsAny nty goalAtoms then
                      unless seenTys.contains nty do
                        seenTys := seenTys.push nty
                        if news.size < budget then
                          news := news.push (tm, nty)
              frontier := next
    pure news
  let hyps : Array Hypothesis := news.map fun (pf, ty) =>
    { userName := `h_inst, type := ty, value := pf }
  let g2 ← (·.2) <$> g.assertHypotheses hyps
  replaceMainGoal [g2]
  evalTactic (← `(tactic| omega))

end SableInstantiate

section SableCases

open Lean Meta Elab Tactic

private def isCtorHead (env : Environment) (d : Expr) : Bool :=
  match d.getAppFn with
  | .const n _ =>
    match env.find? n with
    | some (.ctorInfo _) => true
    | _ => false
  | _ => false

/-- A term worth case-splitting: its type is a non-Prop inductive with at
least two constructors (an `Option`, a `Bool`, …) — never a proof, never a
one-constructor structure. -/
private def splittable (d : Expr) : MetaM Bool := do
  let ty ← whnf (← inferType d)
  let .const tyName _ := ty.getAppFn | return false
  let some (.inductInfo info) := (← getEnv).find? tyName | return false
  if info.ctors.length < 2 then return false
  return !(← inferType ty).isProp

/-- Collect the scrutinees of every `match` in `e` that automation cannot
reduce: closed terms (the match may sit under a binder, but a scrutinee
mentioning a bound variable cannot be split) that are not
constructor-headed. -/
private partial def collectScruts (acc : IO.Ref (Array Expr)) (e : Expr) :
    MetaM Unit := do
  if e.isApp && !e.hasLooseBVars then
    if let some app ← matchMatcherApp? e then
      let env ← getEnv
      for d in app.discrs do
        if !d.hasLooseBVars && !d.hasExprMVar && !isCtorHead env d then
          if ← splittable d then
            let seen ← acc.get
            if !seen.contains d then
              acc.modify (·.push d)
  match e with
  | .app f a => collectScruts acc f; collectScruts acc a
  | .lam _ t b _ => collectScruts acc t; collectScruts acc b
  | .forallE _ t b _ => collectScruts acc t; collectScruts acc b
  | .letE _ t v b _ => collectScruts acc t; collectScruts acc v; collectScruts acc b
  | .mdata _ b => collectScruts acc b
  | .proj _ _ b => collectScruts acc b
  | _ => pure ()

/-- `d` is already pinned by an equation hypothesis `d = ctor …` or
`ctor … = d` (from a previous `cases h_scrut :` split); a non-variable
scrutinee survives its own split in hypothesis matches, so without this
guard the split would repeat forever. -/
private def pinned (d : Expr) : MetaM Bool := do
  let env ← getEnv
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      if let some (_, lhs, rhs) := decl.type.eq? then
        if (lhs == d && isCtorHead env rhs) || (rhs == d && isCtorHead env lhs) then
          return true
  return false

/-- One split: find the first abstract match scrutinee in the goal or a
hypothesis and `cases` it — substituting form for a variable, equation form
(`cases h_scrut : e`) otherwise. Fails when there is nothing to split. -/
elab "sable_cases_step" : tactic => do
  let g ← getMainGoal
  let cand ← g.withContext do
    let acc ← IO.mkRef (#[] : Array Expr)
    collectScruts acc (← g.getType)
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        collectScruts acc d.type
    let mut pick := none
    for d in ← acc.get do
      if pick.isNone && !(← pinned d) then
        pick := some d
    pure pick
  match cand with
  | none => throwError "sable_cases: no abstract match scrutinee"
  | some d => do
    if d.isFVar then
      let name ← g.withContext do
        pure (← d.fvarId!.getDecl).userName
      evalTactic (← `(tactic| cases $(mkIdent name):ident))
    else
      let stx ← g.withContext do Lean.PrettyPrinter.delab d
      evalTactic (← `(tactic| cases h_scrut : $stx:term))

/-- Case-split every abstract `match` scrutinee reachable in the goal and
hypotheses, recursively — a split can expose a nested match. Leaves the
branch goals open; fails if there was nothing to split. Depth-capped: the
pinned-equation guard relies on the split equation matching the collected
scrutinee structurally, and a scrutinee that failed to round-trip through
delaboration must exhaust fuel, not heartbeats. -/
syntax "sable_cases" : tactic
syntax "sable_cases_go" num : tactic
macro_rules
  | `(tactic| sable_cases) => `(tactic| sable_cases_go 8)
  | `(tactic| sable_cases_go $n:num) =>
    match n.getNat with
    | 0 => `(tactic| fail "sable_cases: split depth exhausted")
    | k + 1 =>
      `(tactic| sable_cases_step <;> (try sable_cases_go $(Lean.quote k):num))

end SableCases

syntax "sable_norm" : tactic

macro_rules
  | `(tactic| sable_norm) =>
    `(tactic| simp only [Sable.u8.max, Sable.u16.max, Sable.u32.max, Sable.u64.max,
        Sable.i8.min, Sable.i8.max, Sable.i16.min, Sable.i16.max,
        Sable.i32.min, Sable.i32.max, Sable.i64.min, Sable.i64.max] at *)

syntax "sable_auto" : tactic

macro_rules
  | `(tactic| sable_auto) =>
    -- `solve`, not `first`: an alternative that merely makes progress
    -- (e.g. a partial simp_all) must not commit — every alternative
    -- either closes the goal or the next one runs.
    -- Every data-dependent tier runs under `sable_slice`: a tier that
    -- dies on a runtime error — heartbeat exhaustion or a simp rewrite
    -- cycle blowing the recursion limit — must fail the alternative,
    -- not abort the portfolio. The view-equation contexts of resource
    -- code do produce such cycles in the bare `simp_all` tier, and the
    -- `subst_eqs`-first tier behind it is immune; without the slice the
    -- error escapes `solve` and the immune tiers never run.
    `(tactic| solve
        | assumption
        | rfl
        | (sable_slice 100000 ((try sable_norm) <;> omega))
        | (sable_slice 100000
            ((try sable_norm) <;> (try simp only [Sable.Seq.len_set] at *) <;> omega))
        | (sable_slice 20000
            ((try sable_norm) <;> (intros) <;>
             (try simp only [Sable.Seq.len_set] at *) <;>
             (try simp only [Sable.Seq.get_set]) <;>
             (repeat split) <;> (try subst_eqs) <;> sable_instantiate))
        | (sable_slice 100000 ((try sable_norm) <;> simp_all))
        | (sable_slice 100000
            ((try sable_norm) <;> (try subst_eqs) <;> simp_all <;> omega))
        | (sable_slice 100000
            ((try sable_norm) <;> sable_cases <;>
             (first
               | contradiction
               | ((try simp) <;> (try simp_all) <;> (try omega)))))
        | sable_grind)

end Sable
