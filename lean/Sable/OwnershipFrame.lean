/-
The first local theorem on the Stage-2 ownership/frame-rule track.

This file deliberately proves one small semantic fact about an operation the
SVM already admits. `Stmt.moveLocal` is the machine's atomic affine-owner
transfer: under its ownership preconditions, the source slot is cleared, the
destination slot receives the value, and every independent local frame is
preserved.

Exact non-claims: this is not yet the roadmap's separation-logic frame theorem
for all safe code. It does not connect the Rust checker or VC generator to the
SVM; model nested places, destructor effects, or borrow liveness; split or join
the raw heap; or lift the result from one `moveLocal` step to arbitrary
multi-step executions. Those remain Stage-2 work.
-/

import Sable.SVM

namespace Sable
namespace SVM

/-- Two local environments agree on every name in `frame`. This includes both
present and absent bindings, so the predicate frames the complete observable
state of those slots rather than only preserving values that happen to exist. -/
def Env.AgreesOn (before after : Env) (frame : List String) : Prop :=
  ∀ x, x ∈ frame → before x = after x

/-- Clearing `src` and installing `value` at `dst` leaves an arbitrary local
frame unchanged when neither transfer endpoint belongs to that frame. -/
theorem Env.moveLocal_agreesOn
    {ρ : Env} {dst src : String} {value : Val} {frame : List String}
    (hsrc : src ∉ frame) (hdst : dst ∉ frame) :
    Env.AgreesOn ρ ((ρ.clear src).update dst value) frame := by
  intro x hx
  have hxs : x ≠ src := by
    intro h
    subst x
    exact hsrc hx
  have hxd : x ≠ dst := by
    intro h
    subst x
    exact hdst hx
  simp [Env.clear, Env.update, hxs, hxd]

/-- **One-step ownership frame rule for `moveLocal`.**

If `src` owns `value`, `dst` is empty, and the two slots are distinct, every
SVM step from the corresponding ownership-transfer statement reaches the
specified transfer state. The continuation, call stack, and raw heap are
unchanged, while every local in a frame disjoint from `{src, dst}` agrees with
its pre-state.

The ownership premises make the theorem substantive: its conclusion includes
both halves of the transfer (`src` is cleared and `dst` receives `value`), not
only the preservation of unrelated state. -/
theorem Step.moveLocal_owned_frame
    {P : Prog} {cap : Int} {ρ : Env} {dst src : String} {value : Val}
    {k : List Stmt} {σ : List Frame} {μ : RawHeap} {c' : Config}
    {frame : List String}
    (hne : dst ≠ src) (hdstEmpty : ρ dst = none)
    (hsrcOwns : ρ src = some value)
    (hstep : Step P cap (.run (.moveLocal dst src :: k) ρ σ μ) c')
    (hsrcFrame : src ∉ frame) (hdstFrame : dst ∉ frame) :
    c' = .run k ((ρ.clear src).update dst value) σ μ ∧
      Env.AgreesOn ρ ((ρ.clear src).update dst value) frame := by
  have hout : c' = .run k ((ρ.clear src).update dst value) σ μ := by
    cases hstep <;> simp_all
  exact ⟨hout, Env.moveLocal_agreesOn hsrcFrame hdstFrame⟩

/-- The transfer post-state really vacates the source slot. -/
theorem Env.moveLocal_source_empty
    {ρ : Env} {dst src : String} {value : Val} (hne : dst ≠ src) :
    ((ρ.clear src).update dst value) src = none := by
  simp [Env.clear, Env.update, hne.symm]

/-- The transfer post-state really installs the owner at the destination. -/
theorem Env.moveLocal_destination_owns
    {ρ : Env} {dst src : String} {value : Val} :
    ((ρ.clear src).update dst value) dst = some value := by
  simp [Env.update]

end SVM
end Sable
