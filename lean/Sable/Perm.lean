/-
Sable prelude: multiset equality of sequences, by counting.

`perm a b` says a and b have the same length and every value occurs the
same number of times in their first `len` positions — the standard
"same multiset" spec half of sorting. The workhorse lemma is
`countUpto_set` (how one store shifts one count); `perm_swap` is the
shape the compiler's swap idiom produces:

    t = a[i]; a[i] = a[j]; a[j] = t   ⇒   (s.set i (s.get j)).set j (s.get i)

Core-only proofs (no mathlib), by induction on the counted prefix.
-/

import Sable.Seq

namespace Sable

/-- Occurrences of `v` among positions `0..n` (as Int indices). -/
def Seq.countUpto (s : Seq Int) (v : Int) : Nat → Int
  | 0 => 0
  | n + 1 => s.countUpto v n + (if s.get n = v then 1 else 0)

/-- Same length, same value counts: multiset equality. -/
def Seq.perm (a b : Seq Int) : Prop :=
  a.len = b.len ∧ ∀ v : Int, a.countUpto v a.len.toNat = b.countUpto v b.len.toNat

theorem Seq.perm_refl (a : Seq Int) : a.perm a :=
  ⟨rfl, fun _ => rfl⟩

theorem Seq.perm_symm {a b : Seq Int} (h : a.perm b) : b.perm a :=
  ⟨h.1.symm, fun v => (h.2 v).symm⟩

theorem Seq.perm_trans {a b c : Seq Int} (h1 : a.perm b) (h2 : b.perm c) :
    a.perm c :=
  ⟨h1.1.trans h2.1, fun v => (h1.2 v).trans (h2.2 v)⟩

/-- Counting is blind to positions at or beyond the counted prefix. -/
theorem Seq.countUpto_set_ge (s : Seq Int) (v w : Int) (k : Int) (n : Nat)
    (hk : (n : Int) ≤ k) :
    (s.set k v).countUpto w n = s.countUpto w n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have hm : ((m : Nat) : Int) ≤ k := by omega
    have hne : ((m : Nat) : Int) ≠ k := by omega
    unfold Seq.countUpto
    rw [ih hm, Seq.get_set, if_neg hne]

/-- One store shifts one count: remove the old occupant, add the new. -/
theorem Seq.countUpto_set (s : Seq Int) (v w : Int) (k : Int) (n : Nat)
    (hk0 : 0 ≤ k) (hkn : k < (n : Int)) :
    (s.set k v).countUpto w n =
      s.countUpto w n - (if s.get k = w then 1 else 0)
        + (if v = w then 1 else 0) := by
  induction n with
  | zero => omega
  | succ m ih =>
    unfold Seq.countUpto
    by_cases hkm : ((m : Nat) : Int) = k
    · rw [Seq.countUpto_set_ge s v w k m (by omega)]
      rw [Seq.get_set, if_pos hkm, hkm]
      omega
    · rw [Seq.get_set, if_neg hkm]
      have hkm' : k < ((m : Nat) : Int) := by omega
      rw [ih hkm']
      omega

/-- The compiler's three-statement swap idiom is a permutation. -/
theorem Seq.perm_swap (s : Seq Int) (i j : Int)
    (hi0 : 0 ≤ i) (hin : i < s.len) (hj0 : 0 ≤ j) (hjn : j < s.len) :
    ((s.set i (s.get j)).set j (s.get i)).perm s := by
  refine ⟨rfl, fun w => ?_⟩
  simp only [Seq.len_set]
  have hi' : i < ((s.len.toNat : Nat) : Int) := by omega
  have hj' : j < ((s.len.toNat : Nat) : Int) := by omega
  by_cases hij : i = j
  · subst hij
    rw [Seq.countUpto_set _ _ _ _ _ hi0 hi']
    rw [Seq.countUpto_set _ _ _ _ _ hi0 hi']
    rw [Seq.get_set, if_pos rfl]
    omega
  · rw [Seq.countUpto_set _ _ _ _ _ hj0 hj']
    rw [Seq.countUpto_set _ _ _ _ _ hi0 hi']
    rw [Seq.get_set, if_neg (Ne.symm hij)]
    omega

end Sable
