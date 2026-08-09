/-
Sable prelude: the specification vocabulary.

Common properties so contracts read the way the design doc writes them —
`pre sorted a`, `post sorted a ∧ perm a (old a)` — with no per-file ghost
definitions. Everything here is chosen to work in all three places a
clause lives:

  - elaboration: `abbrev` (reducible), so discharge scripts can apply a
    `sorted` hypothesis directly (`h k m h0 hkm hm`);
  - automation: `@[simp]` where unfolding is what the portfolio needs
    (`perm` stays opaque — its lemma library in Perm.lean is the
    interface);
  - dynamic checking: each predicate has a native evaluator in
    `sable test`'s monitorable fragment.
-/

import Sable.Seq
import Sable.Perm

namespace Sable

/-- Nondecreasing on all of `[0, len)`. -/
@[simp] abbrev sorted (a : Seq Int) : Prop :=
  ∀ i j, 0 ≤ i → i < j → j < a.len → a.get i ≤ a.get j

/-- Nondecreasing on the index range `[lo, hi)`. -/
@[simp] abbrev sortedRange (a : Seq Int) (lo hi : Int) : Prop :=
  ∀ i j, lo ≤ i → i < j → j < hi → a.get i ≤ a.get j

/-- `v` occurs somewhere in `[0, len)`. -/
@[simp] abbrev contains (a : Seq Int) (v : Int) : Prop :=
  ∃ k, 0 ≤ k ∧ k < a.len ∧ a.get k = v

/-- Multiset equality (see Perm.lean for the lemma library:
`Seq.perm_refl`, `Seq.perm_symm`, `Seq.perm_trans`, `Seq.perm_swap`). -/
abbrev perm : Seq Int → Seq Int → Prop := Seq.perm

/-- Occurrences of `v` in `[0, len)`. -/
abbrev count (a : Seq Int) (v : Int) : Int := a.countUpto v a.len.toNat

theorem sorted_of_sortedRange (a : Seq Int) (h : sortedRange a 0 a.len) :
    sorted a := fun i j h0 hij hj => h i j h0 hij hj

end Sable
