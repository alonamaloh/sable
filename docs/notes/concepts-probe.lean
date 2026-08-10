/-
Encoding probe for ADR 0009 (concepts / template-level verification):
the exact obligation shape template-mode VCgen will emit — bind an
abstract IntModel + wf + requires hypotheses, state range facts through
the model's projections — and the instantiation residue (apply the
template theorem to a concrete model + its once-proven wf lemma).
-/
import Sable.IntModel
import Sable.Auto

namespace ConceptProbe
open Sable

-- Template: fn clamp<T>(T x, T lo, T hi) -> T
--   /// requires T.max ≥ 100
--   /// pre  lo ≤ hi
--   /// post lo ≤ result ∧ result ≤ hi
-- One path's post obligation (the x < lo branch, result = lo):
theorem clamp_post_below (T : IntModel) (h_T_wf : T.wf)
    (h_req_T_max_100 : T.max ≥ 100)
    (x lo hi result : Int)
    (h_x_range : T.min ≤ x ∧ x ≤ T.max)
    (h_lo_range : T.min ≤ lo ∧ lo ≤ T.max)
    (h_hi_range : T.min ≤ hi ∧ hi ≤ T.max)
    (h_pre_lo_hi : lo ≤ hi)
    (h_path_x_lo : x < lo)
    (h_result : result = lo) :
    lo ≤ result ∧ result ≤ hi := by
  omega

-- A literal-at-type-T obligation (e.g. `T y = 100;` under the requires):
theorem lit_fits (T : IntModel) (h_T_wf : T.wf)
    (h_req_T_max_100 : T.max ≥ 100) :
    T.min ≤ 100 ∧ 100 ≤ T.max := by
  have h := h_T_wf
  simp only [IntModel.wf] at h
  omega

-- Instantiation residue: concrete model + wf lemma; requires checked
-- numerically. This is ALL an instantiation owes.
example : i32.model.max ≥ 100 := by
  simp only [i32.model, i32.max]; omega

example (x lo hi result : Int)
    (hx : i32.model.min ≤ x ∧ x ≤ i32.model.max)
    (hlo : i32.model.min ≤ lo ∧ lo ≤ i32.model.max)
    (hhi : i32.model.min ≤ hi ∧ hi ≤ i32.model.max)
    (hpre : lo ≤ hi) (hpath : x < lo) (hres : result = lo) :
    lo ≤ result ∧ result ≤ hi :=
  clamp_post_below i32.model i32.model_wf
    (by simp only [i32.model, i32.max]; omega)
    x lo hi result hx hlo hhi hpre hpath hres

end ConceptProbe
