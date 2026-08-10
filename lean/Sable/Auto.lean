import Lean
import Sable.Bounds
import Sable.Seq

/-
Sable prelude: the automation portfolio.

Every VC the compiler emits is a theorem proved `by sable_auto` (unless a
`discharge` block overrides it). The portfolio is deliberately ordered:
cheap closers first, then normalization + omega (the workhorse for range
and overflow VCs), then simp_all, then a heartbeat-budgeted `grind`.

`sable_norm` unfolds the Sable bound constants (`u32.max` etc.) to literals
everywhere, since `omega` treats unknown constants as opaque.

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
    `(tactic| solve
        | assumption
        | rfl
        | ((try sable_norm) <;> omega)
        | ((try sable_norm) <;> (try simp only [Sable.Seq.len_set] at *) <;> omega)
        | ((try sable_norm) <;> simp_all)
        | ((try sable_norm) <;> (try subst_eqs) <;> simp_all <;> omega)
        | sable_grind)

end Sable
