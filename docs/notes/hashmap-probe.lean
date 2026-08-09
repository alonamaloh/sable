/-
Encoding probe for the linear-probing hash map (Tier 1, second half).

Validates, before any compiler work:
  1. cyclic probing stated WITHOUT variable modulus — `probe`/`dist` are
     if-then-else over linear arithmetic, so omega handles them after a
     split (variable `%` is outside omega's fragment; the only `%` left
     in the real VCs is `hash k % cap`, which stays an opaque atom with
     `0 ≤ · < cap` bounds from Int.emod_nonneg / Int.emod_lt_of_pos);
  2. the probe-path class invariant is preservable by `insert` filling
     an empty slot (monotone occupancy + the loop invariant);
  3. the crux: hitting an empty slot at offset j proves the key is
     absent from the WHOLE table (`absent` below) — this is what makes
     early termination of `get`/`insert` sound, and it is the lemma the
     corpus discharges will replay.

Core-only (no mathlib), mirroring the VC shapes vcgen emits: Seq for
arrays, opaque `hm : Int → Int` for the bucket map `fun k => hash k % cap`.
-/
import Sable.Seq
import Sable.Auto

namespace HashProbe

/-- Slot at offset `j` of the probe sequence starting at home `h`.
    Valid for `0 ≤ h < cap`, `0 ≤ j < cap`; wraparound by subtraction. -/
def probe (h j cap : Int) : Int := if h + j < cap then h + j else h + j - cap

/-- Cyclic distance from home `h` to slot `i`. -/
def dist (h i cap : Int) : Int := if h ≤ i then i - h else cap + i - h

theorem probe_bounds (h j cap : Int) (h0 : 0 ≤ h) (hc : h < cap)
    (j0 : 0 ≤ j) (jc : j < cap) : 0 ≤ probe h j cap ∧ probe h j cap < cap := by
  unfold probe; split <;> omega

theorem dist_bounds (h i cap : Int) (h0 : 0 ≤ h) (hc : h < cap)
    (i0 : 0 ≤ i) (ic : i < cap) : 0 ≤ dist h i cap ∧ dist h i cap < cap := by
  unfold dist; split <;> omega

theorem dist_probe (h j cap : Int) (h0 : 0 ≤ h) (hc : h < cap)
    (j0 : 0 ≤ j) (jc : j < cap) : dist h (probe h j cap) cap = j := by
  unfold probe dist; split <;> split <;> omega

theorem probe_dist (h i cap : Int) (h0 : 0 ≤ h) (hc : h < cap)
    (i0 : 0 ≤ i) (ic : i < cap) : probe h (dist h i cap) cap = i := by
  unfold probe dist; split <;> split <;> omega

theorem probe_inj (h j1 j2 cap : Int) (h0 : 0 ≤ h) (hc : h < cap)
    (hj1 : 0 ≤ j1) (hj1c : j1 < cap) (hj2 : 0 ≤ j2) (hj2c : j2 < cap)
    (heq : probe h j1 cap = probe h j2 cap) : j1 = j2 := by
  unfold probe at heq; split at heq <;> split at heq <;> omega

/-- The class invariant, one slot's worth: every occupied slot `i` is
    reachable from its key's home through occupied slots. `occ.get i = 1`
    is the u8 state array; `hm` is the bucket map. -/
def pathInv (cap : Int) (occ keys : Sable.Seq Int) (hm : Int → Int) : Prop :=
  ∀ i, 0 ≤ i → i < cap → occ.get i = 1 →
    ∀ j, 0 ≤ j → j < dist (hm (keys.get i)) i cap →
      occ.get (probe (hm (keys.get i)) j cap) = 1

/-- THE lemma: probing from `hm k` found slots `0..j` occupied with keys
    ≠ k (the loop invariant) and slot `j` empty — then `k` is nowhere in
    the table. Soundness of stopping `get`/`insert` at the first empty. -/
theorem absent (cap : Int) (occ keys : Sable.Seq Int) (hm : Int → Int) (k j : Int)
    (hbnd : ∀ x, 0 ≤ hm x ∧ hm x < cap)
    (hinv : pathInv cap occ keys hm)
    (hloop : ∀ j', 0 ≤ j' → j' < j →
      occ.get (probe (hm k) j' cap) = 1 ∧ keys.get (probe (hm k) j' cap) ≠ k)
    (hj : 0 ≤ j) (hjc : j < cap)
    (hempty : occ.get (probe (hm k) j cap) ≠ 1) :
    ∀ i, 0 ≤ i → i < cap → occ.get i = 1 → keys.get i ≠ k := by
  intro i hi0 hic hocc hkey
  have hb := hbnd k
  have hdb := dist_bounds (hm k) i cap hb.1 hb.2 hi0 hic
  have hpd : probe (hm k) (dist (hm k) i cap) cap = i := by
    have := probe_dist (hm k) i cap hb.1 hb.2 hi0 hic
    exact this
  by_cases hdj : dist (hm k) i cap = j
  · -- the empty slot IS i: contradiction with occupancy
    rw [hdj] at hpd
    rw [hpd] at hempty
    exact hempty hocc
  · by_cases hdlt : dist (hm k) i cap < j
    · -- i sits strictly inside the probed prefix: its key was ≠ k
      have h2 := (hloop _ hdb.1 hdlt).2
      rw [hpd] at h2
      exact h2 hkey
    · -- i is past the empty slot: i's own probe path crosses it, occupied
      have h3 := hinv i hi0 hic hocc
      rw [hkey] at h3
      exact hempty (h3 j hj (by omega))

/-- Insert preservation, existing slots: filling empty slot `s` keeps
    every already-occupied slot's probe path occupied (occupancy is
    monotone), and its key/home unchanged when `s` was empty. -/
theorem pathInv_preserved (cap : Int) (occ keys : Sable.Seq Int) (hm : Int → Int)
    (s k j : Int)
    (hbnd : ∀ x, 0 ≤ hm x ∧ hm x < cap)
    (hinv : pathInv cap occ keys hm)
    (hs : s = probe (hm k) j cap)
    (hj : 0 ≤ j) (hjc : j < cap)
    (hempty : occ.get s ≠ 1)
    (hloop : ∀ j', 0 ≤ j' → j' < j →
      occ.get (probe (hm k) j' cap) = 1 ∧ keys.get (probe (hm k) j' cap) ≠ k) :
    pathInv cap (occ.set s 1) (keys.set s k) hm := by
  intro i hi0 hic hocc j' hj0 hj'
  have hb := hbnd k
  have hsb : 0 ≤ s ∧ s < cap := by
    rw [hs]; exact probe_bounds (hm k) j cap hb.1 hb.2 hj hjc
  by_cases his : i = s
  · -- the new slot: its path is exactly the loop-invariant prefix
    subst his
    have hks : (keys.set i k).get i = k := by simp [Sable.Seq.get_set]
    rw [hks] at hj' ⊢
    have hdp : dist (hm k) i cap = j := by
      rw [hs]; exact dist_probe (hm k) j cap hb.1 hb.2 hj hjc
    rw [hdp] at hj'
    have hl := (hloop j' hj0 hj').1
    by_cases hps : probe (hm k) j' cap = i
    · simp [Sable.Seq.get_set, hps]
    · simp [Sable.Seq.get_set, hps]
      exact hl
  · -- an old slot: unchanged key, path occupied before, still occupied
    rw [Sable.Seq.get_set, if_neg his] at hocc
    have hkey' : (keys.set s k).get i = keys.get i := by
      rw [Sable.Seq.get_set, if_neg his]
    rw [hkey'] at hj' ⊢
    have hold := hinv i hi0 hic hocc j' hj0 hj'
    by_cases hps : probe (hm (keys.get i)) j' cap = s
    · simp [Sable.Seq.get_set, hps]
    · simp [Sable.Seq.get_set, hps]
      exact hold

end HashProbe
