/-
The first machine-profile wrapper for the SVM: `uart-poll-v1`.

The core `SVM.Config` remains unchanged. This wrapper carries the selected
profile state beside it, intercepts exactly the three profile statements,
and delegates every other running head to the core relation. Consequently
terminal core configurations retain the oracle cursor and trace.
-/

import Sable.MMIO
import Sable.SVMEval

namespace Sable
namespace SVMUart

open SVM

inductive Profile where
  | uartPollV1
  deriving Repr, DecidableEq

def Profile.render : Profile → String
  | .uartPollV1 => "uart-poll-v1"

structure State where
  profile : Profile
  uart : UartView

/-- A wrapped core configuration. `state = none` is the production-bare
machine; a platform constructor may eventually install an audited state.
For now only the test-only statement `.testUartProfile` selects one. -/
structure Config where
  core : SVM.Config
  state : Option State

def Config.bare (core : SVM.Config) : Config :=
  ⟨core, none⟩

/-- The deterministic input oracle selected by a test script:
* 0: ready (`1`) forever;
* 1: `0, 0, 1`, then ready forever;
* every other integer: not ready (`0`) forever. -/
def scriptedOracle (script : Int) (cursor : Nat) : Int :=
  if script = 0 then
    1
  else if script = 1 then
    if cursor < 2 then 0 else 1
  else
    0

def scriptedUart (script : Int) : UartView :=
  { ready := false
    oracle := scriptedOracle script
    cursor := 0
    trace := [] }

def scriptedState (script : Int) : State :=
  ⟨.uartPollV1, scriptedUart script⟩

theorem scriptedOracle_u8 (script : Int) (cursor : Nat) :
    0 ≤ scriptedOracle script cursor ∧ scriptedOracle script cursor ≤ 255 := by
  by_cases h₀ : script = 0 <;>
    by_cases h₁ : script = 1 <;>
      by_cases hc : cursor < 2 <;>
        simp [scriptedOracle, h₀, h₁, hc]

@[simp] theorem scriptedUart_wf (script : Int) :
    (scriptedUart script).wf := by
  intro cursor
  exact scriptedOracle_u8 script cursor

@[simp] theorem scriptedOracle_immediate (cursor : Nat) :
    scriptedOracle 0 cursor = 1 := by
  simp [scriptedOracle]

@[simp] theorem scriptedOracle_delayed_zero {cursor : Nat} (h : cursor < 2) :
    scriptedOracle 1 cursor = 0 := by
  simp [scriptedOracle, h]

@[simp] theorem scriptedOracle_delayed_one {cursor : Nat} (h : 2 ≤ cursor) :
    scriptedOracle 1 cursor = 1 := by
  simp [scriptedOracle, Nat.not_lt.mpr h]

theorem scriptedOracle_never {script : Int} (h₀ : script ≠ 0) (h₁ : script ≠ 1)
    (cursor : Nat) : scriptedOracle script cursor = 0 := by
  simp [scriptedOracle, h₀, h₁]

/-- The heads owned by this wrapper. Keeping this predicate explicit is
what prevents the core's deliberate profile-operation fallback rules from
overlapping the selected-profile transition. -/
def stmtIsUartProfileHead : SVM.Stmt → Bool
  | .testUartProfile _ => true
  | .uartStatus _ => true
  | .uartWrite _ => true
  | _ => false

def Config.isUartProfileHead : Config → Bool
  | ⟨.run (stmt :: _) _ _ _, _⟩ => stmtIsUartProfileHead stmt
  | _ => false

private def Config.withCore (c : Config) (core : SVM.Config) : Config :=
  { c with core }

private def Config.withState (c : Config) (core : SVM.Config) (state : State) : Config :=
  { core, state := some state }

/-- Functional meaning of a profile-owned head. It is total because the
wrapper calls it only when `isUartProfileHead` is true; the final case is
a defensive `undef` for direct, out-of-contract calls.

`uartStatus` stores the raw `u8` status value in its destination. Surface
`ready` operations may compare that value with zero when lowering. -/
def profileStepF (P : SVM.Prog) (cap : Int) : Config → Config
  | c@⟨.run (.testUartProfile script :: k) ρ σ μ, selected⟩ =>
      match selected with
      | some _ => c.withCore .undef
      | none =>
          match SVM.evalE cap ρ script with
          | .ok (.int n) => c.withState (.run k ρ σ μ) (scriptedState n)
          | .ok _ => c.withCore .undef
          | .abort ab => c.withCore ab.toConfig
  | c@⟨.run (.uartStatus dst :: k) ρ σ μ, selected⟩ =>
      match selected with
      | none => c.withCore .undef
      | some state =>
          let value := state.uart.status
          if IntTy.u8.inRange value then
            c.withState (.run k (ρ.update dst (.int value)) σ μ)
              { state with uart := state.uart.afterStatus value }
          else
            c.withCore .undef
  | c@⟨.run (.uartWrite valueExpr :: k) ρ σ μ, selected⟩ =>
      match selected with
      | none => c.withCore .undef
      | some state =>
          match SVM.evalE cap ρ valueExpr with
          | .abort ab => c.withCore ab.toConfig
          | .ok (.int value) =>
              if IntTy.u8.inRange value then
                if state.uart.ready then
                  c.withState (.run k ρ σ μ)
                    { state with uart := state.uart.afterWrite value }
                else
                  c.withCore .undef
              else
                c.withCore .undef
          | .ok _ => c.withCore .undef
  | c => c.withCore .undef

/-- The relational presentation. Profile and core transitions are
syntactically disjoint: delegation requires an explicit non-profile head. -/
inductive Step (P : SVM.Prog) (cap : Int) : Config → Config → Prop where
  | profile {c : Config} (head : c.isUartProfileHead = true) :
      Step P cap c (profileStepF P cap c)
  | core {core core' : SVM.Config} {state : Option State}
      (head : (Config.mk core state).isUartProfileHead = false)
      (step : SVM.Step P cap core core') :
      Step P cap ⟨core, state⟩ ⟨core', state⟩

/-- The executable one-step oracle. -/
def stepF (P : SVM.Prog) (cap : Int) (c : Config) : Option Config :=
  match c.isUartProfileHead with
  | true => some (profileStepF P cap c)
  | false =>
      match SVM.stepF P cap c.core with
      | some core' => some ⟨core', c.state⟩
      | none => none

/-- Relational-to-functional agreement. -/
theorem Step.stepF_eq {P : SVM.Prog} {cap : Int} {c c' : Config}
    (h : Step P cap c c') : stepF P cap c = some c' := by
  cases h with
  | profile head => simp [stepF, head]
  | core head step => simp [stepF, head, step.stepF_eq]

/-- Functional-to-relational agreement. -/
theorem stepF_sound {P : SVM.Prog} {cap : Int} {c c' : Config}
    (h : stepF P cap c = some c') : Step P cap c c' := by
  rcases c with ⟨core, state⟩
  cases head : (Config.mk core state).isUartProfileHead with
  | true =>
      simp only [stepF, head, Option.some.injEq] at h
      exact h ▸ .profile head
  | false =>
      simp only [stepF, head] at h
      cases hs : SVM.stepF P cap core with
      | none => simp [hs] at h
      | some core' =>
          simp only [hs, Option.some.injEq] at h
          exact h ▸ .core head (SVM.stepF_sound hs)

theorem step_iff_stepF {P : SVM.Prog} {cap : Int} {c c' : Config} :
    Step P cap c c' ↔ stepF P cap c = some c' :=
  ⟨Step.stepF_eq, stepF_sound⟩

theorem Step.deterministic {P : SVM.Prog} {cap : Int} {c c₁ c₂ : Config}
    (h₁ : Step P cap c c₁) (h₂ : Step P cap c c₂) : c₁ = c₂ :=
  Option.some.inj (h₁.stepF_eq.symm.trans h₂.stepF_eq)

/-- Every wrapped running core configuration progresses. -/
theorem Step.progress (P : SVM.Prog) (cap : Int) (k : List SVM.Stmt)
    (ρ : SVM.Env) (σ : List SVM.Frame) (μ : SVM.RawHeap) (state : Option State) :
    ∃ c', Step P cap ⟨.run k ρ σ μ, state⟩ c' := by
  cases head : (Config.mk (.run k ρ σ μ) state).isUartProfileHead with
  | true => exact ⟨_, .profile head⟩
  | false =>
      obtain ⟨core', hs⟩ := SVM.Step.progress P cap k ρ σ μ
      exact ⟨⟨core', state⟩, .core head hs⟩

inductive Steps (P : SVM.Prog) (cap : Int) : Config → Config → Prop where
  | refl {c : Config} : Steps P cap c c
  | head {c₁ c₂ c₃ : Config} (h : Step P cap c₁ c₂)
      (hs : Steps P cap c₂ c₃) : Steps P cap c₁ c₃

/-- Fuel-bounded profile execution. Terminal core configurations stop,
while their selected state and observations remain in the result. -/
def run (P : SVM.Prog) (cap : Int) : Nat → Config → Config
  | 0, c => c
  | fuel + 1, c =>
      match stepF P cap c with
      | some c' => run P cap fuel c'
      | none => c

theorem run_steps (P : SVM.Prog) (cap : Int) (fuel : Nat) (c : Config) :
    Steps P cap c (run P cap fuel c) := by
  induction fuel generalizing c with
  | zero => exact .refl
  | succ n ih =>
      cases hs : stepF P cap c with
      | some c' => simpa [run, hs] using Steps.head (stepF_sound hs) (ih c')
      | none => simp [run, hs]; exact .refl

private def renderTrace (trace : List MmioEvent) : String :=
  String.intercalate "," (trace.map MmioEvent.render)

/-- Observed wire format. Bare executions are byte-for-byte the core
format. Selected executions add the profile id, consumed-oracle cursor,
and chronological MMIO trace, even after a terminal outcome. -/
def Config.render (c : Config) : String :=
  match c.state with
  | none => c.core.render
  | some state =>
      c.core.render ++ " | profile=" ++ state.profile.render ++
        " cursor=" ++ toString state.uart.cursor ++
        " trace=[" ++ renderTrace state.uart.trace ++ "]"

def observedRun (P : SVM.Prog) (cap : Int) (fuel : Nat) (c : Config) : String :=
  (run P cap fuel c).render

end SVMUart
end Sable
