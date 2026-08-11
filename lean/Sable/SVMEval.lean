/-
The SVM's functional evaluator and its agreement with the rule system.

`Sable/SVM.lean` gives the machine's meaning as inductive relations
(`Eval`, `Step`) — the normative artifact, one rule per design decision.
This file gives the same meaning as *functions* (`evalE`, `stepF`) and
proves the two presentations agree, which yields as corollaries the
§10 claims that were previously only intended:

- **determinism** (`Eval.deterministic`, `Step.deterministic`),
- **totality / progress** (`Eval.total`, `Step.progress` — the machine
  is total, so pillar 1 holds literally, ADR 0005),
- an **executable oracle** (`run`, with `run_steps` tying every run to
  a `Steps` derivation) — the Lean side of the differential harness
  against the compiler's `interp.rs`.

The agreement proofs are the regression test of the rule system: a pair
of overlapping rules with different outcomes, or a missing rule, makes
one of the two directions unprovable.
-/
import Sable.SVM

namespace Sable
namespace SVM

/-! ## Sequencing helpers

Left-to-right evaluation with shape checks at operand production
(ADR 0005): an abnormal outcome propagates; an ill-shaped value is
`undef` before anything to its right is evaluated. -/

/-- Continue with the operand's integer value; ill-shaped is undef. -/
def EOut.bindInt (o : EOut) (f : Int → EOut) : EOut :=
  match o with
  | .ok (.int n) => f n
  | .ok _        => .abort .undef
  | .abort a     => .abort a

/-- Continue with the operand's boolean value; ill-shaped is undef. -/
def EOut.bindBool (o : EOut) (f : Bool → EOut) : EOut :=
  match o with
  | .ok (.bool b) => f b
  | .ok _         => .abort .undef
  | .abort a      => .abort a

@[simp] theorem EOut.bindInt_int (n : Int) (f : Int → EOut) :
    (EOut.ok (.int n)).bindInt f = f n := rfl

@[simp] theorem EOut.bindInt_abort (a : Abort) (f : Int → EOut) :
    (EOut.abort a).bindInt f = .abort a := rfl

theorem EOut.bindInt_ok_of_ne {v : Val} (f : Int → EOut)
    (hv : ∀ n, v ≠ .int n) : (EOut.ok v).bindInt f = .abort .undef := by
  cases v <;> first | exact absurd rfl (hv _) | rfl

@[simp] theorem EOut.bindBool_bool (b : Bool) (f : Bool → EOut) :
    (EOut.ok (.bool b)).bindBool f = f b := rfl

@[simp] theorem EOut.bindBool_abort (a : Abort) (f : Bool → EOut) :
    (EOut.abort a).bindBool f = .abort a := rfl

theorem EOut.bindBool_ok_of_ne {v : Val} (f : Bool → EOut)
    (hv : ∀ b, v ≠ .bool b) : (EOut.ok v).bindBool f = .abort .undef := by
  cases v <;> first | exact absurd rfl (hv _) | rfl

/-! ## The functional expression evaluator -/

/-- `evalE cap ρ e`: the outcome `Eval` relates `e` to — computed. -/
def evalE (cap : Int) (ρ : Env) : Expr → EOut
  | .intLit t n => if t.inRange n then .ok (.int n) else .abort .undef
  | .boolLit b  => .ok (.bool b)
  | .var x =>
      match ρ x with
      | some v => .ok v
      | none   => .abort .undef
  | .neg t e =>
      (evalE cap ρ e).bindInt fun n =>
        if t.inRange (-n) then .ok (.int (-n)) else .abort (.trap (.overflow t))
  | .not e =>
      (evalE cap ρ e).bindBool fun b => .ok (.bool (!b))
  | .arith op t e₁ e₂ =>
      (evalE cap ρ e₁).bindInt fun a =>
        (evalE cap ρ e₂).bindInt fun b =>
          if t.inRange (op.denote a b) then .ok (.int (op.denote a b))
          else .abort (.trap (.overflow t))
  | .wrapArith op t e₁ e₂ =>
      (evalE cap ρ e₁).bindInt fun a =>
        (evalE cap ρ e₂).bindInt fun b => .ok (.int (t.wrap (op.denote a b)))
  | .checkedArith op t e₁ e₂ =>
      (evalE cap ρ e₁).bindInt fun a =>
        (evalE cap ρ e₂).bindInt fun b =>
          if t.inRange (op.denote a b) then .ok (.opt (some (op.denote a b)))
          else .ok (.opt none)
  | .div t e₁ e₂ =>
      (evalE cap ρ e₁).bindInt fun a =>
        (evalE cap ρ e₂).bindInt fun b =>
          if b = 0 then .abort (.trap .divByZero)
          else if t.inRange (a.ediv b) then .ok (.int (a.ediv b))
          else .abort (.trap (.overflow t))
  | .mod _ e₁ e₂ =>
      (evalE cap ρ e₁).bindInt fun a =>
        (evalE cap ρ e₂).bindInt fun b =>
          if b = 0 then .abort (.trap .divByZero)
          else .ok (.int (a.emod b))
  | .cmp op e₁ e₂ =>
      (evalE cap ρ e₁).bindInt fun a =>
        (evalE cap ρ e₂).bindInt fun b => .ok (.bool (op.denote a b))
  | .and e₁ e₂ =>
      (evalE cap ρ e₁).bindBool fun b =>
        if b then (evalE cap ρ e₂).bindBool fun c => .ok (.bool c)
        else .ok (.bool false)
  | .or e₁ e₂ =>
      (evalE cap ρ e₁).bindBool fun b =>
        if b then .ok (.bool true)
        else (evalE cap ρ e₂).bindBool fun c => .ok (.bool c)
  | .len x =>
      match ρ x with
      | some (.arr a) => .ok (.int a.len)
      | _             => .abort .undef
  | .index x e =>
      (evalE cap ρ e).bindInt fun n =>
        match ρ x with
        | some (.arr a) =>
            if 0 ≤ n ∧ n < a.len then .ok (.int (a.get n))
            else .abort (.trap (.indexOOB n a.len))
        | _ => .abort .undef
  | .widen _ e => (evalE cap ρ e).bindInt fun n => .ok (.int n)
  | .narrow dst e =>
      (evalE cap ρ e).bindInt fun n =>
        if dst.inRange n then .ok (.int n)
        else .abort (.trap (.narrowOOB dst n))
  | .allocArray e₁ e₂ =>
      (evalE cap ρ e₁).bindInt fun n =>
        (evalE cap ρ e₂).bindInt fun v =>
          if n < 0 then .abort .undef
          else if n ≤ cap then .ok (.arr ⟨n, fun _ => v⟩)
          else .abort (.trap (.oom n))
  | .someE e => (evalE cap ρ e).bindInt fun n => .ok (.opt (some n))
  | .noneE => .ok (.opt none)

/-! ## Agreement, direction 1: every derivation computes -/

/-- A derivation's outcome is what `evalE` computes — so the rule side
conditions really are mutually exclusive (two overlapping rules with
different outcomes would make this unprovable). -/
theorem Eval.evalE_eq {cap : Int} {ρ : Env} {e : Expr} {out : EOut}
    (h : Eval cap ρ e out) : evalE cap ρ e = out := by
  induction h with
  | intLit h => simp [evalE, h]
  | intLit_undef h => simp [evalE, h]
  | boolLit => rfl
  | var h => simp [evalE, h]
  | var_undef h => simp [evalE, h]
  | neg_ok h hr ih => simp [evalE, ih, hr]
  | neg_overflow h hr ih => simp [evalE, ih, hr]
  | neg_undef h hv ih => simp [evalE, ih, EOut.bindInt_ok_of_ne _ hv]
  | neg_abort h ih => simp [evalE, ih]
  | not_ok h ih => simp [evalE, ih]
  | not_undef h hv ih => simp [evalE, ih, EOut.bindBool_ok_of_ne _ hv]
  | not_abort h ih => simp [evalE, ih]
  | arith_ok h₁ h₂ hr ih₁ ih₂ => simp [evalE, ih₁, ih₂, hr]
  | arith_overflow h₁ h₂ hr ih₁ ih₂ => simp [evalE, ih₁, ih₂, hr]
  | arith_undef₁ h₁ hv ih₁ => simp [evalE, ih₁, EOut.bindInt_ok_of_ne _ hv]
  | arith_abort₁ h ih => simp [evalE, ih]
  | arith_undef₂ h₁ h₂ hv ih₁ ih₂ => simp [evalE, ih₁, ih₂, EOut.bindInt_ok_of_ne _ hv]
  | arith_abort₂ h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | wrap_ok h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | wrap_undef₁ h₁ hv ih₁ => simp [evalE, ih₁, EOut.bindInt_ok_of_ne _ hv]
  | wrap_abort₁ h ih => simp [evalE, ih]
  | wrap_undef₂ h₁ h₂ hv ih₁ ih₂ => simp [evalE, ih₁, ih₂, EOut.bindInt_ok_of_ne _ hv]
  | wrap_abort₂ h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | checked_some h₁ h₂ hr ih₁ ih₂ => simp [evalE, ih₁, ih₂, hr]
  | checked_none h₁ h₂ hr ih₁ ih₂ => simp [evalE, ih₁, ih₂, hr]
  | checked_undef₁ h₁ hv ih₁ => simp [evalE, ih₁, EOut.bindInt_ok_of_ne _ hv]
  | checked_abort₁ h ih => simp [evalE, ih]
  | checked_undef₂ h₁ h₂ hv ih₁ ih₂ => simp [evalE, ih₁, ih₂, EOut.bindInt_ok_of_ne _ hv]
  | checked_abort₂ h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | div_ok h₁ h₂ hz hr ih₁ ih₂ => simp [evalE, ih₁, ih₂, hz, hr]
  | div_zero h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | div_overflow h₁ h₂ hz hr ih₁ ih₂ => simp [evalE, ih₁, ih₂, hz, hr]
  | div_undef₁ h₁ hv ih₁ => simp [evalE, ih₁, EOut.bindInt_ok_of_ne _ hv]
  | div_abort₁ h ih => simp [evalE, ih]
  | div_undef₂ h₁ h₂ hv ih₁ ih₂ => simp [evalE, ih₁, ih₂, EOut.bindInt_ok_of_ne _ hv]
  | div_abort₂ h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | mod_ok h₁ h₂ hz ih₁ ih₂ => simp [evalE, ih₁, ih₂, hz]
  | mod_zero h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | mod_undef₁ h₁ hv ih₁ => simp [evalE, ih₁, EOut.bindInt_ok_of_ne _ hv]
  | mod_abort₁ h ih => simp [evalE, ih]
  | mod_undef₂ h₁ h₂ hv ih₁ ih₂ => simp [evalE, ih₁, ih₂, EOut.bindInt_ok_of_ne _ hv]
  | mod_abort₂ h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | cmp_ok h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | cmp_undef₁ h₁ hv ih₁ => simp [evalE, ih₁, EOut.bindInt_ok_of_ne _ hv]
  | cmp_abort₁ h ih => simp [evalE, ih]
  | cmp_undef₂ h₁ h₂ hv ih₁ ih₂ => simp [evalE, ih₁, ih₂, EOut.bindInt_ok_of_ne _ hv]
  | cmp_abort₂ h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | and_false h ih => simp [evalE, ih]
  | and_true h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | and_undef₁ h hv ih => simp [evalE, ih, EOut.bindBool_ok_of_ne _ hv]
  | and_abort₁ h ih => simp [evalE, ih]
  | and_undef₂ h₁ h₂ hv ih₁ ih₂ => simp [evalE, ih₁, ih₂, EOut.bindBool_ok_of_ne _ hv]
  | and_abort₂ h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | or_true h ih => simp [evalE, ih]
  | or_false h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | or_undef₁ h hv ih => simp [evalE, ih, EOut.bindBool_ok_of_ne _ hv]
  | or_abort₁ h ih => simp [evalE, ih]
  | or_undef₂ h₁ h₂ hv ih₁ ih₂ => simp [evalE, ih₁, ih₂, EOut.bindBool_ok_of_ne _ hv]
  | or_abort₂ h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | len h => simp [evalE, h]
  | len_undef h =>
      simp only [evalE]
  | index_ok hi ha h₀ h₁ ih => simp [evalE, ih, ha, h₀, h₁]
  | index_oob hi ha hoob ih =>
      simp only [evalE, ih, EOut.bindInt_int, ha]
      rw [if_neg (by omega)]
  | index_undef_idx hi hv ih => simp [evalE, ih, EOut.bindInt_ok_of_ne _ hv]
  | index_abort h ih => simp [evalE, ih]
  | index_undef_arr hi ha ih =>
      simp only [evalE, ih, EOut.bindInt_int]
  | widen_ok h ih => simp [evalE, ih]
  | widen_undef h hv ih => simp [evalE, ih, EOut.bindInt_ok_of_ne _ hv]
  | widen_abort h ih => simp [evalE, ih]
  | narrow_ok h hr ih => simp [evalE, ih, hr]
  | narrow_oob h hr ih => simp [evalE, ih, hr]
  | narrow_undef h hv ih => simp [evalE, ih, EOut.bindInt_ok_of_ne _ hv]
  | narrow_abort h ih => simp [evalE, ih]
  | alloc_ok h₁ h₂ h₀ hc ih₁ ih₂ =>
      simp only [evalE, ih₁, ih₂, EOut.bindInt_int]
      rw [if_neg (by omega), if_pos hc]
  | alloc_oom h₁ h₂ h₀ hc ih₁ ih₂ =>
      simp only [evalE, ih₁, ih₂, EOut.bindInt_int]
      rw [if_neg (by omega), if_neg (by omega)]
  | alloc_neg h₁ h₂ h₀ ih₁ ih₂ =>
      simp only [evalE, ih₁, ih₂, EOut.bindInt_int]
      rw [if_pos h₀]
  | alloc_undef₁ h₁ hv ih₁ => simp [evalE, ih₁, EOut.bindInt_ok_of_ne _ hv]
  | alloc_abort₁ h ih => simp [evalE, ih]
  | alloc_undef₂ h₁ h₂ hv ih₁ ih₂ => simp [evalE, ih₁, ih₂, EOut.bindInt_ok_of_ne _ hv]
  | alloc_abort₂ h₁ h₂ ih₁ ih₂ => simp [evalE, ih₁, ih₂]
  | someE_ok h ih => simp [evalE, ih]
  | someE_undef h hv ih => simp [evalE, ih, EOut.bindInt_ok_of_ne _ hv]
  | someE_abort h ih => simp [evalE, ih]
  | noneE => rfl

/-! ## Agreement, direction 2: everything `evalE` computes derives

Scaffolding: to show `Eval` covers a `bindInt`/`bindBool` composition,
provide the propagation rules and the ok-continuation. -/

private theorem eval_bindInt {cap : Int} {ρ : Env} {e tgt : Expr} {f : Int → EOut}
    (ih : Eval cap ρ e (evalE cap ρ e))
    (Habort : ∀ a, Eval cap ρ e (.abort a) → Eval cap ρ tgt (.abort a))
    (Hundef : ∀ v, Eval cap ρ e (.ok v) → (∀ n, v ≠ .int n) →
      Eval cap ρ tgt (.abort .undef))
    (Hok : ∀ n, Eval cap ρ e (.ok (.int n)) → Eval cap ρ tgt (f n)) :
    Eval cap ρ tgt ((evalE cap ρ e).bindInt f) := by
  cases ho : evalE cap ρ e with
  | abort a => rw [ho] at ih; simpa using Habort a ih
  | ok v =>
    rw [ho] at ih
    cases v with
    | int n => simpa using Hok n ih
    | unit => simpa [EOut.bindInt] using Hundef _ ih nofun
    | bool b => simpa [EOut.bindInt] using Hundef _ ih nofun
    | arr a => simpa [EOut.bindInt] using Hundef _ ih nofun
    | opt o => simpa [EOut.bindInt] using Hundef _ ih nofun
    | ptr a k => simpa [EOut.bindInt] using Hundef _ ih nofun

private theorem eval_bindBool {cap : Int} {ρ : Env} {e tgt : Expr} {f : Bool → EOut}
    (ih : Eval cap ρ e (evalE cap ρ e))
    (Habort : ∀ a, Eval cap ρ e (.abort a) → Eval cap ρ tgt (.abort a))
    (Hundef : ∀ v, Eval cap ρ e (.ok v) → (∀ b, v ≠ .bool b) →
      Eval cap ρ tgt (.abort .undef))
    (Hok : ∀ b, Eval cap ρ e (.ok (.bool b)) → Eval cap ρ tgt (f b)) :
    Eval cap ρ tgt ((evalE cap ρ e).bindBool f) := by
  cases ho : evalE cap ρ e with
  | abort a => rw [ho] at ih; simpa using Habort a ih
  | ok v =>
    rw [ho] at ih
    cases v with
    | bool b => simpa using Hok b ih
    | unit => simpa [EOut.bindBool] using Hundef _ ih nofun
    | int n => simpa [EOut.bindBool] using Hundef _ ih nofun
    | arr a => simpa [EOut.bindBool] using Hundef _ ih nofun
    | ptr a k => simpa [EOut.bindBool] using Hundef _ ih nofun
    | opt o => simpa [EOut.bindBool] using Hundef _ ih nofun

private theorem eval_bindInt₂ {cap : Int} {ρ : Env} {e₁ e₂ tgt : Expr}
    {f : Int → Int → EOut}
    (ih₁ : Eval cap ρ e₁ (evalE cap ρ e₁))
    (ih₂ : Eval cap ρ e₂ (evalE cap ρ e₂))
    (Habort₁ : ∀ a, Eval cap ρ e₁ (.abort a) → Eval cap ρ tgt (.abort a))
    (Hundef₁ : ∀ v, Eval cap ρ e₁ (.ok v) → (∀ n, v ≠ .int n) →
      Eval cap ρ tgt (.abort .undef))
    (Habort₂ : ∀ n a, Eval cap ρ e₁ (.ok (.int n)) → Eval cap ρ e₂ (.abort a) →
      Eval cap ρ tgt (.abort a))
    (Hundef₂ : ∀ n v, Eval cap ρ e₁ (.ok (.int n)) → Eval cap ρ e₂ (.ok v) →
      (∀ m, v ≠ .int m) → Eval cap ρ tgt (.abort .undef))
    (Hok : ∀ a b, Eval cap ρ e₁ (.ok (.int a)) → Eval cap ρ e₂ (.ok (.int b)) →
      Eval cap ρ tgt (f a b)) :
    Eval cap ρ tgt ((evalE cap ρ e₁).bindInt fun a =>
      (evalE cap ρ e₂).bindInt fun b => f a b) := by
  refine eval_bindInt ih₁ Habort₁ Hundef₁ fun n h₁ => ?_
  exact eval_bindInt ih₂ (fun a h₂ => Habort₂ n a h₁ h₂)
    (fun v h₂ hv => Hundef₂ n v h₁ h₂ hv) (fun m h₂ => Hok n m h₁ h₂)

/-- `evalE`'s outcome always derives — so `Eval` is total: every
expression has a meaning (pillar 1, ADR 0005). -/
theorem evalE_eval (cap : Int) (ρ : Env) : ∀ e, Eval cap ρ e (evalE cap ρ e) := by
  intro e
  induction e with
  | intLit t n =>
      by_cases h : t.inRange n
      · simpa [evalE, h] using Eval.intLit h
      · simpa [evalE, h] using Eval.intLit_undef h
  | boolLit b => exact .boolLit
  | var x =>
      cases hx : ρ x with
      | some v => simpa [evalE, hx] using Eval.var hx
      | none => simpa [evalE, hx] using Eval.var_undef hx
  | neg t e ih =>
      simp only [evalE]
      refine eval_bindInt ih (fun a h => .neg_abort h) (fun v h hv => .neg_undef h hv)
        fun n h => ?_
      by_cases hr : t.inRange (-n)
      · rw [if_pos hr]; exact .neg_ok h hr
      · rw [if_neg hr]; exact .neg_overflow h hr
  | not e ih =>
      simp only [evalE]
      exact eval_bindBool ih (fun a h => .not_abort h) (fun v h hv => .not_undef h hv)
        fun b h => .not_ok h
  | arith op t e₁ e₂ ih₁ ih₂ =>
      simp only [evalE]
      refine eval_bindInt₂ ih₁ ih₂ (fun a h => .arith_abort₁ h)
        (fun v h hv => .arith_undef₁ h hv) (fun n a h₁ h₂ => .arith_abort₂ h₁ h₂)
        (fun n v h₁ h₂ hv => .arith_undef₂ h₁ h₂ hv) fun a b h₁ h₂ => ?_
      by_cases hr : t.inRange (op.denote a b)
      · rw [if_pos hr]; exact .arith_ok h₁ h₂ hr
      · rw [if_neg hr]; exact .arith_overflow h₁ h₂ hr
  | wrapArith op t e₁ e₂ ih₁ ih₂ =>
      simp only [evalE]
      exact eval_bindInt₂ ih₁ ih₂ (fun a h => .wrap_abort₁ h)
        (fun v h hv => .wrap_undef₁ h hv) (fun n a h₁ h₂ => .wrap_abort₂ h₁ h₂)
        (fun n v h₁ h₂ hv => .wrap_undef₂ h₁ h₂ hv) fun a b h₁ h₂ => .wrap_ok h₁ h₂
  | checkedArith op t e₁ e₂ ih₁ ih₂ =>
      simp only [evalE]
      refine eval_bindInt₂ ih₁ ih₂ (fun a h => .checked_abort₁ h)
        (fun v h hv => .checked_undef₁ h hv) (fun n a h₁ h₂ => .checked_abort₂ h₁ h₂)
        (fun n v h₁ h₂ hv => .checked_undef₂ h₁ h₂ hv) fun a b h₁ h₂ => ?_
      by_cases hr : t.inRange (op.denote a b)
      · rw [if_pos hr]; exact .checked_some h₁ h₂ hr
      · rw [if_neg hr]; exact .checked_none h₁ h₂ hr
  | div t e₁ e₂ ih₁ ih₂ =>
      simp only [evalE]
      refine eval_bindInt₂ ih₁ ih₂ (fun a h => .div_abort₁ h)
        (fun v h hv => .div_undef₁ h hv) (fun n a h₁ h₂ => .div_abort₂ h₁ h₂)
        (fun n v h₁ h₂ hv => .div_undef₂ h₁ h₂ hv) fun a b h₁ h₂ => ?_
      by_cases hz : b = 0
      · subst hz; rw [if_pos rfl]; exact .div_zero h₁ h₂
      · rw [if_neg hz]
        by_cases hr : t.inRange (a.ediv b)
        · rw [if_pos hr]; exact .div_ok h₁ h₂ hz hr
        · rw [if_neg hr]; exact .div_overflow h₁ h₂ hz hr
  | mod t e₁ e₂ ih₁ ih₂ =>
      simp only [evalE]
      refine eval_bindInt₂ ih₁ ih₂ (fun a h => .mod_abort₁ h)
        (fun v h hv => .mod_undef₁ h hv) (fun n a h₁ h₂ => .mod_abort₂ h₁ h₂)
        (fun n v h₁ h₂ hv => .mod_undef₂ h₁ h₂ hv) fun a b h₁ h₂ => ?_
      by_cases hz : b = 0
      · subst hz; rw [if_pos rfl]; exact .mod_zero h₁ h₂
      · rw [if_neg hz]; exact .mod_ok h₁ h₂ hz
  | cmp op e₁ e₂ ih₁ ih₂ =>
      simp only [evalE]
      exact eval_bindInt₂ ih₁ ih₂ (fun a h => .cmp_abort₁ h)
        (fun v h hv => .cmp_undef₁ h hv) (fun n a h₁ h₂ => .cmp_abort₂ h₁ h₂)
        (fun n v h₁ h₂ hv => .cmp_undef₂ h₁ h₂ hv) fun a b h₁ h₂ => .cmp_ok h₁ h₂
  | and e₁ e₂ ih₁ ih₂ =>
      simp only [evalE]
      refine eval_bindBool ih₁ (fun a h => .and_abort₁ h)
        (fun v h hv => .and_undef₁ h hv) fun b h₁ => ?_
      cases b with
      | false => simpa using Eval.and_false h₁
      | true =>
          simp only [if_true]
          exact eval_bindBool ih₂ (fun a h₂ => .and_abort₂ h₁ h₂)
            (fun v h₂ hv => .and_undef₂ h₁ h₂ hv) fun c h₂ => .and_true h₁ h₂
  | or e₁ e₂ ih₁ ih₂ =>
      simp only [evalE]
      refine eval_bindBool ih₁ (fun a h => .or_abort₁ h)
        (fun v h hv => .or_undef₁ h hv) fun b h₁ => ?_
      cases b with
      | true => simpa using Eval.or_true h₁
      | false =>
          simp only [Bool.false_eq_true, if_false]
          exact eval_bindBool ih₂ (fun a h₂ => .or_abort₂ h₁ h₂)
            (fun v h₂ hv => .or_undef₂ h₁ h₂ hv) fun c h₂ => .or_false h₁ h₂
  | len x =>
      cases hx : ρ x with
      | none => simpa [evalE, hx] using Eval.len_undef (fun a h => by simp [hx] at h)
      | some v =>
          cases v with
          | arr a => simpa [evalE, hx] using Eval.len hx
          | unit => simpa [evalE, hx] using Eval.len_undef (fun a h => by simp [hx] at h)
          | int n => simpa [evalE, hx] using Eval.len_undef (fun a h => by simp [hx] at h)
          | bool b => simpa [evalE, hx] using Eval.len_undef (fun a h => by simp [hx] at h)
          | ptr a k => simpa [evalE, hx] using Eval.len_undef (fun a h => by simp [hx] at h)
          | opt o => simpa [evalE, hx] using Eval.len_undef (fun a h => by simp [hx] at h)
  | index x e ih =>
      simp only [evalE]
      refine eval_bindInt ih (fun a h => .index_abort h)
        (fun v h hv => .index_undef_idx h hv) fun n h => ?_
      split
      next a ha =>
        by_cases hb : 0 ≤ n ∧ n < a.len
        · rw [if_pos hb]; exact .index_ok h ha hb.1 hb.2
        · rw [if_neg hb]; exact .index_oob h ha (by omega)
      next hne =>
        exact .index_undef_arr h fun a ha => hne a ha
  | widen dst e ih =>
      simp only [evalE]
      exact eval_bindInt ih (fun a h => .widen_abort h)
        (fun v h hv => .widen_undef h hv) fun n h => .widen_ok h
  | narrow dst e ih =>
      simp only [evalE]
      refine eval_bindInt ih (fun a h => .narrow_abort h)
        (fun v h hv => .narrow_undef h hv) fun n h => ?_
      by_cases hr : dst.inRange n
      · rw [if_pos hr]; exact .narrow_ok h hr
      · rw [if_neg hr]; exact .narrow_oob h hr
  | allocArray e₁ e₂ ih₁ ih₂ =>
      simp only [evalE]
      refine eval_bindInt₂ ih₁ ih₂ (fun a h => .alloc_abort₁ h)
        (fun v h hv => .alloc_undef₁ h hv) (fun n a h₁ h₂ => .alloc_abort₂ h₁ h₂)
        (fun n v h₁ h₂ hv => .alloc_undef₂ h₁ h₂ hv) fun n v h₁ h₂ => ?_
      by_cases hneg : n < 0
      · rw [if_pos hneg]; exact .alloc_neg h₁ h₂ hneg
      · rw [if_neg hneg]
        by_cases hc : n ≤ cap
        · rw [if_pos hc]; exact .alloc_ok h₁ h₂ (by omega) hc
        · rw [if_neg hc]; exact .alloc_oom h₁ h₂ (by omega) (by omega)
  | someE e ih =>
      simp only [evalE]
      exact eval_bindInt ih (fun a h => .someE_abort h)
        (fun v h hv => .someE_undef h hv) fun n h => .someE_ok h
  | noneE => exact .noneE

/-- The two presentations of expression evaluation agree. -/
theorem eval_iff_evalE {cap : Int} {ρ : Env} {e : Expr} {out : EOut} :
    Eval cap ρ e out ↔ evalE cap ρ e = out :=
  ⟨Eval.evalE_eq, fun h => h ▸ evalE_eval cap ρ e⟩

/-- Expression evaluation is deterministic (§10). -/
theorem Eval.deterministic {cap : Int} {ρ : Env} {e : Expr} {out₁ out₂ : EOut}
    (h₁ : Eval cap ρ e out₁) (h₂ : Eval cap ρ e out₂) : out₁ = out₂ :=
  h₁.evalE_eq.symm.trans h₂.evalE_eq

/-- Expression evaluation is total (pillar 1, ADR 0005). -/
theorem Eval.total (cap : Int) (ρ : Env) (e : Expr) : ∃ out, Eval cap ρ e out :=
  ⟨_, evalE_eval cap ρ e⟩

/-! ## Argument lists -/

/-- `evalArgs cap ρ es`: the outcome `EvalArgs` relates `es` to —
computed. -/
def evalArgs (cap : Int) (ρ : Env) : List Expr → AOut
  | [] => .ok []
  | e :: es =>
      match evalE cap ρ e with
      | .ok v =>
          match evalArgs cap ρ es with
          | .ok vs => .ok (v :: vs)
          | .abort a => .abort a
      | .abort a => .abort a

theorem EvalArgs.evalArgs_eq {cap : Int} {ρ : Env} {es : List Expr} {out : AOut}
    (h : EvalArgs cap ρ es out) : evalArgs cap ρ es = out := by
  induction h with
  | nil => rfl
  | cons_ok h hs ih => simp [evalArgs, h.evalE_eq, ih]
  | cons_abort h => simp [evalArgs, h.evalE_eq]
  | cons_abort_tail h hs ih => simp [evalArgs, h.evalE_eq, ih]

theorem evalArgs_evalArgs (cap : Int) (ρ : Env) :
    ∀ es, EvalArgs cap ρ es (evalArgs cap ρ es) := by
  intro es
  induction es with
  | nil => exact .nil
  | cons e es ih =>
      simp only [evalArgs]
      cases he : evalE cap ρ e with
      | abort a => exact .cons_abort (he ▸ evalE_eval cap ρ e)
      | ok v =>
          cases hes : evalArgs cap ρ es with
          | ok vs => exact .cons_ok (he ▸ evalE_eval cap ρ e) (hes ▸ ih)
          | abort a => exact .cons_abort_tail (he ▸ evalE_eval cap ρ e) (hes ▸ ih)

theorem evalArgs_iff {cap : Int} {ρ : Env} {es : List Expr} {out : AOut} :
    EvalArgs cap ρ es out ↔ evalArgs cap ρ es = out :=
  ⟨EvalArgs.evalArgs_eq, fun h => h ▸ evalArgs_evalArgs cap ρ es⟩

/-! ## The functional statement stepper -/

/-- Continue a statement with the expression's integer value. -/
def EOut.stepInt (o : EOut) (f : Int → Config) : Config :=
  match o with
  | .ok (.int n) => f n
  | .ok _        => .undef
  | .abort a     => a.toConfig

/-- Continue a statement with the expression's boolean value. -/
def EOut.stepBool (o : EOut) (f : Bool → Config) : Config :=
  match o with
  | .ok (.bool b) => f b
  | .ok _         => .undef
  | .abort a      => a.toConfig

@[simp] theorem EOut.stepInt_int (n : Int) (f : Int → Config) :
    (EOut.ok (.int n)).stepInt f = f n := rfl

@[simp] theorem EOut.stepInt_abort (a : Abort) (f : Int → Config) :
    (EOut.abort a).stepInt f = a.toConfig := rfl

theorem EOut.stepInt_ok_of_ne {v : Val} (f : Int → Config)
    (hv : ∀ n, v ≠ .int n) : (EOut.ok v).stepInt f = .undef := by
  cases v <;> first | exact absurd rfl (hv _) | rfl

@[simp] theorem EOut.stepBool_bool (b : Bool) (f : Bool → Config) :
    (EOut.ok (.bool b)).stepBool f = f b := rfl

@[simp] theorem EOut.stepBool_abort (a : Abort) (f : Bool → Config) :
    (EOut.abort a).stepBool f = a.toConfig := rfl

theorem EOut.stepBool_ok_of_ne {v : Val} (f : Bool → Config)
    (hv : ∀ b, v ≠ .bool b) : (EOut.ok v).stepBool f = .undef := by
  cases v <;> first | exact absurd rfl (hv _) | rfl

/-- `stepF P cap c`: the configuration `Step` relates `c` to — computed.
`none` exactly on terminal configurations. -/
def stepF (P : Prog) (cap : Int) : Config → Option Config
  | .run [] _ [] _ => some (.done .unit)
  | .run [] _ (fr :: σ) μ => some (.run fr.k (fr.ρ.bindDst fr.dst .unit) σ μ)
  | .run (.assign x e :: k) ρ σ μ =>
      some (match evalE cap ρ e with
        | .ok v => .run k (ρ.update x v) σ μ
        | .abort a => a.toConfig)
  | .run (.store x ei ev :: k) ρ σ μ =>
      some ((evalE cap ρ ei).stepInt fun n =>
        (evalE cap ρ ev).stepInt fun w =>
          match ρ x with
          | some (.arr a) =>
              if 0 ≤ n ∧ n < a.len then .run k (ρ.update x (.arr (a.set n w))) σ μ
              else .trapped (.indexOOB n a.len)
          | _ => .undef)
  | .run (.ite c thn els :: k) ρ σ μ =>
      some ((evalE cap ρ c).stepBool fun b =>
        if b then .run (thn ++ k) ρ σ μ else .run (els ++ k) ρ σ μ)
  | .run (.while c body :: k) ρ σ μ =>
      some ((evalE cap ρ c).stepBool fun b =>
        if b then .run (body ++ .while c body :: k) ρ σ μ else .run k ρ σ μ)
  | .run (.ret e :: _) ρ σ μ =>
      some (match evalE cap ρ e with
        | .ok v =>
            match σ with
            | [] => .done v
            | fr :: σ' => .run fr.k (fr.ρ.bindDst fr.dst v) σ' μ
        | .abort a => a.toConfig)
  | .run (.check name c :: k) ρ σ μ =>
      some ((evalE cap ρ c).stepBool fun b =>
        if b then .run k ρ σ μ else .trapped (.deferViolation name))
  | .run (.call dst f args :: k) ρ σ μ =>
      some (match P f with
        | none => .undef
        | some fd =>
            match evalArgs cap ρ args with
            | .abort a => a.toConfig
            | .ok vs =>
                if fd.params.length = vs.length then
                  .run fd.body (Env.empty.bind fd.params vs) (⟨dst, k, ρ⟩ :: σ) μ
                else .undef)
  | .done _ => none
  | .trapped _ => none
  | .undef => none

/-! ## Step agreement -/

/-- Every step computes. -/
theorem Step.stepF_eq {P : Prog} {cap : Int} {c c' : Config} (h : Step P cap c c') :
    stepF P cap c = some c' := by
  cases h with
  | assign_ok h => simp [stepF, h.evalE_eq]
  | assign_abort h => simp [stepF, h.evalE_eq]
  | store_ok hi hv ha h₀ h₁ => simp [stepF, hi.evalE_eq, hv.evalE_eq, ha, h₀, h₁]
  | store_oob hi hv ha hoob =>
      simp only [stepF, hi.evalE_eq, hv.evalE_eq, EOut.stepInt_int, ha]
      rw [if_neg (by omega)]
  | store_abort_idx hi => simp [stepF, hi.evalE_eq]
  | store_undef_idx hi hv => simp [stepF, hi.evalE_eq, EOut.stepInt_ok_of_ne _ hv]
  | store_abort_val hi hv => simp [stepF, hi.evalE_eq, hv.evalE_eq]
  | store_undef_val hi hv hw =>
      simp [stepF, hi.evalE_eq, hv.evalE_eq, EOut.stepInt_ok_of_ne _ hw]
  | store_undef_arr hi hv ha =>
      simp only [stepF, hi.evalE_eq, hv.evalE_eq, EOut.stepInt_int]
  | ite_true h => simp [stepF, h.evalE_eq]
  | ite_false h => simp [stepF, h.evalE_eq]
  | ite_undef h hv => simp [stepF, h.evalE_eq, EOut.stepBool_ok_of_ne _ hv]
  | ite_abort h => simp [stepF, h.evalE_eq]
  | while_true h => simp [stepF, h.evalE_eq]
  | while_false h => simp [stepF, h.evalE_eq]
  | while_undef h hv => simp [stepF, h.evalE_eq, EOut.stepBool_ok_of_ne _ hv]
  | while_abort h => simp [stepF, h.evalE_eq]
  | check_pass h => simp [stepF, h.evalE_eq]
  | check_fail h => simp [stepF, h.evalE_eq]
  | check_undef h hv => simp [stepF, h.evalE_eq, EOut.stepBool_ok_of_ne _ hv]
  | check_abort h => simp [stepF, h.evalE_eq]
  | call_undef_fn hf => simp [stepF, hf]
  | call_abort hf ha => simp [stepF, hf, ha.evalArgs_eq]
  | call_undef_arity hf ha hn => simp [stepF, hf, ha.evalArgs_eq, hn]
  | call_enter hf ha hn => simp [stepF, hf, ha.evalArgs_eq, hn]
  | ret_ok h => simp [stepF, h.evalE_eq]
  | ret_pop h => simp [stepF, h.evalE_eq]
  | ret_abort h =>
      cases ‹List Frame› with
      | nil => simp [stepF, h.evalE_eq]
      | cons fr σ => simp [stepF, h.evalE_eq]
  | nil_ret => rfl
  | nil_pop => rfl

private theorem step_stepInt {P : Prog} {cap : Int} {ρ : Env} {e : Expr} {c₀ : Config}
    {f : Int → Config}
    (Habort : ∀ a, Eval cap ρ e (.abort a) → Step P cap c₀ a.toConfig)
    (Hundef : ∀ v, Eval cap ρ e (.ok v) → (∀ n, v ≠ .int n) → Step P cap c₀ .undef)
    (Hok : ∀ n, Eval cap ρ e (.ok (.int n)) → Step P cap c₀ (f n)) :
    Step P cap c₀ ((evalE cap ρ e).stepInt f) := by
  have ih := evalE_eval cap ρ e
  cases ho : evalE cap ρ e with
  | abort a => rw [ho] at ih; simpa using Habort a ih
  | ok v =>
    rw [ho] at ih
    cases v with
    | int n => simpa using Hok n ih
    | unit => simpa [EOut.stepInt] using Hundef _ ih nofun
    | bool b => simpa [EOut.stepInt] using Hundef _ ih nofun
    | ptr a k => simpa [EOut.stepInt] using Hundef _ ih nofun
    | arr a => simpa [EOut.stepInt] using Hundef _ ih nofun
    | opt o => simpa [EOut.stepInt] using Hundef _ ih nofun

private theorem step_stepBool {P : Prog} {cap : Int} {ρ : Env} {e : Expr} {c₀ : Config}
    {f : Bool → Config}
    (Habort : ∀ a, Eval cap ρ e (.abort a) → Step P cap c₀ a.toConfig)
    (Hundef : ∀ v, Eval cap ρ e (.ok v) → (∀ b, v ≠ .bool b) → Step P cap c₀ .undef)
    (Hok : ∀ b, Eval cap ρ e (.ok (.bool b)) → Step P cap c₀ (f b)) :
    Step P cap c₀ ((evalE cap ρ e).stepBool f) := by
  have ih := evalE_eval cap ρ e
  cases ho : evalE cap ρ e with
  | abort a => rw [ho] at ih; simpa using Habort a ih
  | ok v =>
    rw [ho] at ih
    cases v with
    | bool b => simpa using Hok b ih
    | unit => simpa [EOut.stepBool] using Hundef _ ih nofun
    | int n => simpa [EOut.stepBool] using Hundef _ ih nofun
    | ptr a k => simpa [EOut.stepBool] using Hundef _ ih nofun
    | arr a => simpa [EOut.stepBool] using Hundef _ ih nofun
    | opt o => simpa [EOut.stepBool] using Hundef _ ih nofun

/-- Everything `stepF` computes is a step. -/
theorem stepF_sound {P : Prog} {cap : Int} {c c' : Config}
    (h : stepF P cap c = some c') : Step P cap c c' := by
  cases c with
  | done v => simp [stepF] at h
  | trapped t => simp [stepF] at h
  | undef => simp [stepF] at h
  | run k ρ σ =>
    cases k with
    | nil =>
        cases σ with
        | nil =>
            simp only [stepF, Option.some.injEq] at h
            exact h ▸ .nil_ret
        | cons fr σ' =>
            simp only [stepF, Option.some.injEq] at h
            exact h ▸ .nil_pop
    | cons s k =>
      cases s with
      | assign x e =>
          simp only [stepF, Option.some.injEq] at h
          subst h
          cases ho : evalE cap ρ e with
          | ok v => exact .assign_ok (ho ▸ evalE_eval cap ρ e)
          | abort a => exact .assign_abort (ho ▸ evalE_eval cap ρ e)
      | store x ei ev =>
          simp only [stepF, Option.some.injEq] at h
          subst h
          refine step_stepInt (fun a hi => .store_abort_idx hi)
            (fun v hi hv => .store_undef_idx hi hv) fun n hi => ?_
          refine step_stepInt (fun a hv => .store_abort_val hi hv)
            (fun v hv hw => .store_undef_val hi hv hw) fun w hv => ?_
          split
          next a ha =>
            by_cases hb : 0 ≤ n ∧ n < a.len
            · rw [if_pos hb]; exact .store_ok hi hv ha hb.1 hb.2
            · rw [if_neg hb]; exact .store_oob hi hv ha (by omega)
          next hne =>
            exact .store_undef_arr hi hv fun a ha => hne a ha
      | ite c thn els =>
          simp only [stepF, Option.some.injEq] at h
          subst h
          refine step_stepBool (fun a hc => .ite_abort hc)
            (fun v hc hv => .ite_undef hc hv) fun b hc => ?_
          cases b with
          | true => simpa using Step.ite_true hc
          | false => simpa using Step.ite_false hc
      | «while» c body =>
          simp only [stepF, Option.some.injEq] at h
          subst h
          refine step_stepBool (fun a hc => .while_abort hc)
            (fun v hc hv => .while_undef hc hv) fun b hc => ?_
          cases b with
          | true => simpa using Step.while_true hc
          | false => simpa using Step.while_false hc
      | ret e =>
          simp only [stepF, Option.some.injEq] at h
          subst h
          cases ho : evalE cap ρ e with
          | abort a => exact .ret_abort (ho ▸ evalE_eval cap ρ e)
          | ok v =>
              cases σ with
              | nil => exact .ret_ok (ho ▸ evalE_eval cap ρ e)
              | cons fr σ' => exact .ret_pop (ho ▸ evalE_eval cap ρ e)
      | check name c =>
          simp only [stepF, Option.some.injEq] at h
          subst h
          refine step_stepBool (fun a hc => .check_abort hc)
            (fun v hc hv => .check_undef hc hv) fun b hc => ?_
          cases b with
          | true => simpa using Step.check_pass hc
          | false => simpa using Step.check_fail hc
      | call dst f args =>
          simp only [stepF, Option.some.injEq] at h
          subst h
          cases hf : P f with
          | none => exact .call_undef_fn hf
          | some fd =>
              cases ha : evalArgs cap ρ args with
              | abort a => exact .call_abort hf (ha ▸ evalArgs_evalArgs cap ρ args)
              | ok vs =>
                  by_cases hn : fd.params.length = vs.length
                  · simpa [hn] using
                      Step.call_enter (P := P) (k := k) (σ := σ) hf
                        (ha ▸ evalArgs_evalArgs cap ρ args) hn
                  · simpa [hn] using
                      Step.call_undef_arity (P := P) (k := k) (σ := σ) (dst := dst) hf
                        (ha ▸ evalArgs_evalArgs cap ρ args) hn

/-- The two presentations of the machine step agree. -/
theorem step_iff_stepF {P : Prog} {cap : Int} {c c' : Config} :
    Step P cap c c' ↔ stepF P cap c = some c' :=
  ⟨Step.stepF_eq, stepF_sound⟩

/-- The machine is deterministic (§10) — now a theorem, via agreement
with `stepF`. -/
theorem Step.deterministic {P : Prog} {cap : Int} {c c₁ c₂ : Config}
    (h₁ : Step P cap c c₁) (h₂ : Step P cap c c₂) : c₁ = c₂ :=
  Option.some.inj (h₁.stepF_eq.symm.trans h₂.stepF_eq)

/-- Progress: a `run` configuration always steps — with `undef` a
defined outcome, nothing is stuck (ADR 0005). -/
theorem Step.progress (P : Prog) (cap : Int) (k : List Stmt) (ρ : Env) (σ : List Frame)
    (μ : RawHeap) :
    ∃ c', Step P cap (.run k ρ σ μ) c' := by
  cases k with
  | nil => cases σ <;> exact ⟨_, stepF_sound rfl⟩
  | cons s k => cases s <;> exact ⟨_, stepF_sound rfl⟩

/-! ## The executable oracle -/

/-- Fuel-bounded iteration of `stepF`: the executable machine the
differential harness runs against `interp.rs`. Stops at the first
terminal configuration; out of fuel leaves a `run` configuration. -/
def run (P : Prog) (cap : Int) : Nat → Config → Config
  | 0, c => c
  | fuel + 1, c =>
      match stepF P cap c with
      | some c' => run P cap fuel c'
      | none => c

/-- Whatever `run` reaches is really reachable. -/
theorem run_steps (P : Prog) (cap : Int) (fuel : Nat) (c : Config) :
    Steps P cap c (run P cap fuel c) := by
  induction fuel generalizing c with
  | zero => exact .refl
  | succ n ih =>
      cases hs : stepF P cap c with
      | some c' => simpa [run, hs] using Steps.head (stepF_sound hs) (ih c')
      | none => simp [run, hs]; exact .refl

/-! ## Canonical rendering (the differential harness's wire format)

Must match `svm.rs` on the compiler side character for character:
`done <val>` / `trap <name> <data>` / `undef` / `running`. -/

def IntTy.render : IntTy → String
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"

def Val.render : Val → String
  | .unit => "unit"
  | .int n => s!"int {n}"
  | .bool b => s!"bool {b}"
  | .ptr a k => s!"ptr {a}+{k}"
  | .arr a =>
      "arr [" ++ String.intercalate ", "
        ((List.range a.len.toNat).map fun i => toString (a.get (Int.ofNat i))) ++ "]"
  | .opt none => "opt none"
  | .opt (some n) => s!"opt some {n}"

def Trap.render : Trap → String
  | .overflow t => s!"trap overflow {t.render}"
  | .divByZero => "trap divByZero"
  | .indexOOB i len => s!"trap indexOOB {i} {len}"
  | .narrowOOB t n => s!"trap narrowOOB {t.render} {n}"
  | .oom len => s!"trap oom {len}"
  | .deferViolation name => s!"trap deferViolation {name}"

def Config.render : Config → String
  | .run .. => "running"
  | .done v => s!"done {v.render}"
  | .trapped t => t.render
  | .undef => "undef"

end SVM
end Sable
