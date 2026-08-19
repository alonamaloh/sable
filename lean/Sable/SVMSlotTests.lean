/-
Direct executable regressions for the phase-one owner-slot SVM fragment.

This file proves and executes the local operational boundary only: affine
slot storage, scalar values, and a directly constructed owned-array witness.
It makes no claim about source classes, `Vec<T>`, member access, destructors,
or a class-aware call ABI; those remain outside the SVM bridge.
-/

import Sable.SVMEval
import Sable.OwnershipFrame

namespace Sable
namespace SVM

private def outcome (cap : Int) (k : List Stmt) : String :=
  (run Prog.empty cap 1000 (.run k Env.empty [] .empty)).render

private def u64 (n : Int) : Expr := .intLit .u64 n

/- Empty allocation retains a distinct slot tag and exposes only length. -/
#guard outcome 100
  [ .slotAlloc "s" .bool (u64 3), .ret (.len "s") ]
  = "done int 3"

/- The compiler bridge stages a scalar before put.  Put consumes that local;
take clears the cell and installs the payload in its destination atomically. -/
#guard outcome 100
  [ .slotAlloc "s" .bool (u64 2),
    .assign "$stage" (.boolLit true),
    .slotPut "s" .bool (u64 1) "$stage",
    .slotTake "x" "s" .bool (u64 1),
    .ret (.var "x") ]
  = "done bool true"

#guard outcome 100
  [ .slotAlloc "s" .bool (u64 1),
    .slotTake "x" "s" .bool (u64 0) ]
  = "trap slotEmpty 0"

#guard outcome 100
  [ .slotAlloc "s" .bool (u64 1),
    .assign "$first" (.boolLit false),
    .slotPut "s" .bool (u64 0) "$first",
    .assign "$second" (.boolLit true),
    .slotPut "s" .bool (u64 0) "$second" ]
  = "trap slotOccupied 0"

#guard outcome 100
  [ .slotAlloc "s" .bool (u64 1),
    .slotTake "x" "s" .bool (u64 2) ]
  = "trap indexOOB 2 1"

#guard outcome 1 [ .slotAlloc "s" .bool (u64 2) ] = "trap oom 2"

/- A staged value is authenticated before the index is evaluated.  This is
the statement-level half of source-order staging in the compiler bridge. -/
#guard outcome 100
  [ .slotAlloc "s" .bool (u64 0),
    .assign "$stage" (u64 1),
    .slotPut "s" .bool (.optValue .noneE) "$stage" ]
  = "undef"

/- Direct owned witness: the formal machine can move an owned array into and
back out of a slot without ever duplicating its binding.  The Rust bridge in
this tranche intentionally admits only `slots<bool>`; this witness exercises
the generic affine rule without claiming source-level nested-slot coverage. -/
#guard outcome 100
  [ .slotAlloc "s" (.array .bool) (u64 1),
    .assign "a" (.allocArray (u64 2) (.boolLit false)),
    .moveLocal "$stage" "a",
    .slotPut "s" (.array .bool) (u64 0) "$stage",
    .slotTake "out" "s" (.array .bool) (u64 0),
    .ret (.index "out" (u64 1)) ]
  = "done bool false"

/-! ## Successful local frame theorems

These results are deliberately local and success-path only.  Given an
*arbitrary observed step* plus the premises of the successful rule,
determinism pins that observation to the exact ownership post-state.  The
configuration equality also says that the continuation, call stack, and raw
heap are unchanged; `Env.AgreesOn` states preservation of every unrelated
local.  No theorem here claims that arbitrary source programs are safe. -/

theorem Env.slotAlloc_agreesOn {ρ : Env} {dst : String} {elem : SlotTag}
    {n : Int} {frame : List String} (hdst : dst ∉ frame) :
    Env.AgreesOn ρ (ρ.update dst (.slots elem (Seq.replicate n none))) frame := by
  intro x hx
  have hxd : x ≠ dst := by
    intro h
    subst x
    exact hdst hx
  simp [Env.update, hxd]

theorem Env.slotTake_agreesOn {ρ : Env} {dst container : String}
    {elem : SlotTag} {n : Int} {cells : Seq (Option Val)} {value : Val}
    {frame : List String} (hdst : dst ∉ frame) (hcontainer : container ∉ frame) :
    Env.AgreesOn ρ
      ((ρ.update container (.slots elem (cells.set n none))).update dst value) frame := by
  intro x hx
  have hxd : x ≠ dst := by
    intro h
    subst x
    exact hdst hx
  have hxc : x ≠ container := by
    intro h
    subst x
    exact hcontainer hx
  simp [Env.update, hxd, hxc]

theorem Env.slotPut_agreesOn {ρ : Env} {container staged : String}
    {elem : SlotTag} {n : Int} {cells : Seq (Option Val)} {value : Val}
    {frame : List String} (hcontainer : container ∉ frame) (hstaged : staged ∉ frame) :
    Env.AgreesOn ρ
      ((ρ.clear staged).update container (.slots elem (cells.set n (some value)))) frame := by
  intro x hx
  have hxc : x ≠ container := by
    intro h
    subst x
    exact hcontainer hx
  have hxs : x ≠ staged := by
    intro h
    subst x
    exact hstaged hx
  simp [Env.clear, Env.update, hxc, hxs]

/-- Successful allocation changes exactly `dst`, installs an all-empty slot
owner there, and leaves the continuation, stack, heap, and disjoint locals
unchanged. -/
theorem slotAlloc_local_frame {P : Prog} {cap : Int} {ρ : Env} {dst : String}
    {elem : SlotTag} {len : Expr} {n : Int} {k : List Stmt} {σ : List Frame}
    {μ : RawHeap} {c' : Config} {frame : List String}
    (hi : Eval cap ρ len (.ok (.int n))) (h₀ : 0 ≤ n) (hc : n ≤ cap)
    (hstep : Step P cap (.run (.slotAlloc dst elem len :: k) ρ σ μ) c')
    (hdst : dst ∉ frame) :
    c' = .run k (ρ.update dst (.slots elem (Seq.replicate n none))) σ μ ∧
      Env.AgreesOn ρ (ρ.update dst (.slots elem (Seq.replicate n none))) frame ∧
      (ρ.update dst (.slots elem (Seq.replicate n none))) dst =
        some (.slots elem (Seq.replicate n none)) := by
  have hout :
      c' = .run k (ρ.update dst (.slots elem (Seq.replicate n none))) σ μ :=
    Step.deterministic hstep (.slotAlloc_ok hi h₀ hc)
  exact ⟨hout, Env.slotAlloc_agreesOn hdst, by simp [Env.update]⟩

/-- Successful take vacates the selected source cell, installs its unique
payload at `dst`, and preserves the complete environment outside those two
local names. -/
theorem slotTake_local_frame {P : Prog} {cap : Int} {ρ : Env}
    {dst container : String} {elem : SlotTag} {idx : Expr} {n : Int}
    {cells : Seq (Option Val)} {value : Val} {k : List Stmt} {σ : List Frame}
    {μ : RawHeap} {c' : Config} {frame : List String}
    (hne : dst ≠ container) (hi : Eval cap ρ idx (.ok (.int n)))
    (hc : ρ container = some (.slots elem cells))
    (h₀ : 0 ≤ n) (h₁ : n < cells.len) (hv : cells.get n = some value)
    (hstep : Step P cap (.run (.slotTake dst container elem idx :: k) ρ σ μ) c')
    (hdst : dst ∉ frame) (hcontainer : container ∉ frame) :
    c' = .run k
        ((ρ.update container (.slots elem (cells.set n none))).update dst value) σ μ ∧
      Env.AgreesOn ρ
        ((ρ.update container (.slots elem (cells.set n none))).update dst value) frame ∧
      ((ρ.update container (.slots elem (cells.set n none))).update dst value) dst =
        some value ∧
      ((ρ.update container (.slots elem (cells.set n none))).update dst value) container =
        some (.slots elem (cells.set n none)) ∧
      (cells.set n none).get n = none := by
  have hout :
      c' = .run k
        ((ρ.update container (.slots elem (cells.set n none))).update dst value) σ μ :=
    Step.deterministic hstep (.slotTake_ok hne hi hc h₀ h₁ hv)
  exact ⟨hout, Env.slotTake_agreesOn hdst hcontainer,
    by simp [Env.update], by simp [Env.update, hne.symm], by simp⟩

/-- Successful put consumes its staging local, fills the selected container
cell, and preserves the complete environment outside those two local names. -/
theorem slotPut_local_frame {P : Prog} {cap : Int} {ρ : Env}
    {container staged : String} {elem : SlotTag} {idx : Expr} {n : Int}
    {cells : Seq (Option Val)} {value : Val} {k : List Stmt} {σ : List Frame}
    {μ : RawHeap} {c' : Config} {frame : List String}
    (hne : container ≠ staged) (hs : ρ staged = some value)
    (ht : value.slotTag? = some elem) (hi : Eval cap ρ idx (.ok (.int n)))
    (hc : ρ container = some (.slots elem cells))
    (h₀ : 0 ≤ n) (h₁ : n < cells.len) (he : cells.get n = none)
    (hstep : Step P cap (.run (.slotPut container elem idx staged :: k) ρ σ μ) c')
    (hcontainer : container ∉ frame) (hstaged : staged ∉ frame) :
    c' = .run k
        ((ρ.clear staged).update container (.slots elem (cells.set n (some value)))) σ μ ∧
      Env.AgreesOn ρ
        ((ρ.clear staged).update container (.slots elem (cells.set n (some value)))) frame ∧
      ((ρ.clear staged).update container
        (.slots elem (cells.set n (some value)))) staged = none ∧
      ((ρ.clear staged).update container
        (.slots elem (cells.set n (some value)))) container =
          some (.slots elem (cells.set n (some value))) ∧
      (cells.set n (some value)).get n = some value := by
  have hout :
      c' = .run k
        ((ρ.clear staged).update container (.slots elem (cells.set n (some value)))) σ μ :=
    Step.deterministic hstep (.slotPut_ok hne hs ht hi hc h₀ h₁ he)
  exact ⟨hout, Env.slotPut_agreesOn hcontainer hstaged,
    by simp [Env.clear, Env.update, hne.symm],
    by simp [Env.update], by simp⟩

end SVM
end Sable
