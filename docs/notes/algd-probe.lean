/-
Proof-core probe for Algorithm D (Knuth 4.3.1) long division over the
bignum pillar's Nat ([u32] limbs, little-endian, base B = 2^32).

Validates, before any corpus work, the ghost skeleton of the fast
division at the natVal level — the design keeps every loop invariant on
ghost values and drives the per-digit work through the already-verified
Nat operations, so limbs enter the proofs only through top-limb
decompositions:

  1. `qhat_ge` / `qhat_le4` — the q̂ bounds, the roadmap's boss lemma,
     stated in pure ℤ against a top-two-limbs decomposition of the
     dividend prefix and a top-limb decomposition of the divisor.
     Deviation from Knuth recorded here: the normalization loop uses
     the guard `t + m ≤ 2^31` (invariant `t + m ≤ 2^32`, trivially
     preserved) instead of exact `t < 2^31` doubling — the exact form
     needs the scale factor's power-of-two-ness, which is outside
     omega's fragment, while the relaxed form only quarter-normalizes
     (top limb > 2^30) and weakens q̂ ≤ q+2 to q̂ ≤ q+4: two more
     constant-time correction steps, no extra proof difficulty. The
     corrections are straight-line `if`s, so these bounds are load-
     bearing for functional correctness, not just complexity.
  2. `top2_decomp` — natVal r as (r₍n₎·B + r₍n₋₁₎)·B^(n-1) + low with
     limb-or-zero selectors, for r.len ≤ n+1 (the estimate's bridge).
  3. `top_limb_lb` / `val_range_len` — value bounds to top-limb and
     exact-length facts (normalization's bridge: vn = v·m keeps v's
     length and gains the top-limb bound, all from natVal reasoning —
     the verified mul is reused, its internals never reopened).
  4. `valIn_shift` — the shift-in-a-limb helper's index-shifted
     congruence (R' = B·R + u_j, Q' = B·Q + q_d).
  5. `digit_step` / `digit_close` / `denorm_quot` — the outer loop's
     invariant algebra and the un-normalization at the end (the
     quotient needs no denormalization: q = (a·m)/(v·m)).

Core-only (no mathlib), everything Int, matching the bignum lemma
library's style (pw/valIn copied verbatim from corpus/verifies/
bignum.sable so the statements splice unchanged).
-/
import Sable

open Sable

-- ---- defs and support lemmas, verbatim from the bignum library ----

def pw (n : Int) : Int := if 0 < n then 4294967296 * pw (n - 1) else 1
termination_by n.toNat
decreasing_by omega

def valIn (a : Sable.Seq Int) (i n : Int) : Int :=
  if i < n then a.get i + 4294967296 * valIn a (i + 1) n else 0
termination_by (n - i).toNat
decreasing_by omega

def natVal (a : Sable.Seq Int) : Int := valIn a 0 a.len

theorem pw_nonpos (n : Int) (h : n ≤ 0) : pw n = 1 := by
  rw [pw, if_neg (by omega)]

theorem pw_pos (n : Int) : 0 < pw n := by
  fun_induction pw n with
  | case1 n h ih => omega
  | case2 n h => omega

theorem pw_succ (n : Int) (h : 0 ≤ n) : pw (n + 1) = 4294967296 * pw n := by
  rw [pw, if_pos (by omega)]
  have e : n + 1 - 1 = n := by omega
  rw [e]

theorem pw_mono (m n : Int) (h : m ≤ n) : pw m ≤ pw n := by
  revert h
  fun_induction pw n with
  | case1 n hn ih =>
      intro h
      by_cases hmn : m = n
      · rw [hmn, pw, if_pos hn]
        omega
      · have h1 := ih (by omega)
        have h2 := pw_pos (n - 1)
        omega
  | case2 n hn =>
      intro h
      rw [pw_nonpos m (by omega)]
      omega

theorem valIn_nil (a : Sable.Seq Int) (i n : Int) (h : n ≤ i) :
    valIn a i n = 0 := by
  rw [valIn, if_neg (by omega)]

theorem valIn_nonneg (a : Sable.Seq Int) (i n : Int)
    (hb : ∀ k, i ≤ k → k < n → 0 ≤ a.get k) : 0 ≤ valIn a i n := by
  revert hb
  fun_induction valIn a i n with
  | case1 i h ih =>
      intro hb
      have h1 := ih (fun k hk1 hk2 => hb k (by omega) hk2)
      have h2 := hb i (by omega) h
      omega
  | case2 i h =>
      intro _
      omega

theorem valIn_lt_pw (a : Sable.Seq Int) (i n : Int)
    (hb : ∀ k, i ≤ k → k < n → 0 ≤ a.get k ∧ a.get k ≤ 4294967295) :
    valIn a i n < pw (n - i) := by
  revert hb
  fun_induction valIn a i n with
  | case1 i h ih =>
      intro hb
      have h1 := ih (fun k hk1 hk2 => hb k (by omega) hk2)
      have h2 := hb i (by omega) h
      have h3 : pw (n - i) = 4294967296 * pw (n - (i + 1)) := by
        rw [pw, if_pos (by omega)]
        have e : n - i - 1 = n - (i + 1) := by omega
        rw [e]
      rw [h3]
      omega
  | case2 i h =>
      intro _
      exact pw_pos _

theorem valIn_ge_pw (a : Sable.Seq Int) (i n : Int)
    (hb : ∀ k, i ≤ k → k < n → 0 ≤ a.get k)
    (htop : 1 ≤ a.get (n - 1)) (hin : i < n) :
    pw (n - 1 - i) ≤ valIn a i n := by
  revert hb hin
  fun_induction valIn a i n with
  | case1 i h ih =>
      intro hb hin
      by_cases hlast : i = n - 1
      · have hz : valIn a (i + 1) n = 0 := by rw [valIn, if_neg (by omega)]
        have ht : 1 ≤ a.get i := by rw [hlast]; exact htop
        rw [hz, show n - 1 - i = 0 from by omega, pw_nonpos 0 (by omega)]
        omega
      · have h1 := ih (fun k hk1 hk2 => hb k (by omega) hk2) (by omega)
        have h2 := hb i (by omega) h
        have h3 : pw (n - 1 - i) = 4294967296 * pw (n - 1 - (i + 1)) := by
          rw [pw, if_pos (by omega)]
          have e : n - 1 - i - 1 = n - 1 - (i + 1) := by omega
          rw [e]
        rw [h3]
        have h4 := pw_pos (n - 1 - (i + 1))
        omega
  | case2 i h =>
      intro _ hin
      omega

theorem valIn_snoc (a : Sable.Seq Int) (i n : Int) (h : i ≤ n) :
    valIn a i (n + 1) = valIn a i n + a.get n * pw (n - i) := by
  revert h
  fun_induction valIn a i n with
  | case1 i hc ih =>
      intro h
      have h1 : valIn a i (n + 1)
          = a.get i + 4294967296 * valIn a (i + 1) (n + 1) := by
        rw [valIn, if_pos (by omega)]
      have h2 := ih (by omega)
      have h3 : pw (n - i) = 4294967296 * pw (n - (i + 1)) := by
        rw [pw, if_pos (by omega)]
        have e : n - i - 1 = n - (i + 1) := by omega
        rw [e]
      rw [h1, h2, h3]
      have e : a.get n * (4294967296 * pw (n - (i + 1)))
             = 4294967296 * (a.get n * pw (n - (i + 1))) :=
        Int.mul_left_comm _ _ _
      rw [e, Int.mul_add]
      omega
  | case2 i hc =>
      intro h
      have hin : i = n := by omega
      have h1 : valIn a i (n + 1)
          = a.get i + 4294967296 * valIn a (i + 1) (n + 1) := by
        rw [valIn, if_pos (by omega)]
      have h2 : valIn a (i + 1) (n + 1) = 0 := by
        rw [valIn, if_neg (by omega)]
      rw [h1, h2, ← hin, show i - i = 0 from by omega, pw_nonpos 0 (by omega)]
      omega

theorem div_unique (a b q r : Int) (hb : 1 ≤ b)
    (h : q * b + r = a) (hr0 : 0 ≤ r) (hrb : r < b) : q = a / b := by
  have h2 := (Int.ediv_emod_unique (a := a) (b := b) (r := r) (q := q)
      (by omega : (0:Int) < b)).mpr
    ⟨by rw [Int.mul_comm b q]; omega, hr0, hrb⟩
  omega

-- -------------------- new: division-fact toolbox --------------------

/-- The Euclidean decomposition, packaged the way the q̂ proofs consume
it: `a = (a/b)·b + r` with `0 ≤ r < b`. -/
theorem ediv_decomp (a b : Int) (hb : 1 ≤ b) :
    (a / b) * b + a % b = a ∧ 0 ≤ a % b ∧ a % b < b := by
  obtain ⟨h1, h2, h3⟩ :=
    (Int.ediv_emod_unique (by omega : (0:Int) < b)).mp ⟨rfl, rfl⟩
  refine ⟨?_, h2, h3⟩
  rw [Int.mul_comm] at h1
  omega

/-- Cancel a positive factor: `q·b ≤ a < (p+1)·b → q ≤ p` — the floor
comparison both q̂ bounds reduce to. -/
theorem le_of_mul_sandwich (a b p q : Int) (hb : 1 ≤ b)
    (hq : q * b ≤ a) (hp : a < (p + 1) * b) : q ≤ p := by
  by_cases h : q ≤ p
  · exact h
  · exfalso
    have h1 : p + 1 ≤ q := by omega
    have h2 : (p + 1) * b ≤ q * b :=
      Int.mul_le_mul_of_nonneg_right h1 (by omega)
    omega

/-- `a/b` under a strict multiple bound: `a < c·b → a/b < c`. -/
theorem ediv_lt_of_lt_mul (a b c : Int) (hb : 1 ≤ b) (_ha : 0 ≤ a)
    (h : a < c * b) : a / b < c := by
  obtain ⟨hdec, hr0, hrb⟩ := ediv_decomp a b hb
  have := le_of_mul_sandwich a b (c - 1) (a / b) hb (by omega)
    (by rw [show c - 1 + 1 = c from by omega]; exact h)
  omega

-- ----------------------- the boss: q̂ bounds ------------------------

/-- q̂ never underestimates: with the dividend prefix `R` decomposed at
the top two limb positions (`R = rtop2·B^k + Rlow`) and the divisor at
its top limb (`V = w·B^k + Vlow`), the estimate
`q̂ = min(rtop2 / w, B-1)` satisfies `R/V ≤ q̂`. No normalization
needed. -/
theorem qhat_ge (w rtop2 Rlow R V Vlow k qh : Int)
    (hw : 1 ≤ w) (_hk : 0 ≤ k)
    (hV : V = w * pw k + Vlow) (hVl : 0 ≤ Vlow) (_hVh : Vlow < pw k)
    (hR : R = rtop2 * pw k + Rlow) (hRl : 0 ≤ Rlow) (hRh : Rlow < pw k)
    (hr2 : 0 ≤ rtop2)
    (hRB : R < 4294967296 * V)
    (hqh : (qh = rtop2 / w ∧ rtop2 / w ≤ 4294967295)
         ∨ (qh = 4294967295 ∧ 4294967295 ≤ rtop2 / w)) :
    R / V ≤ qh := by
  have hpw := pw_pos k
  have hV1 : 1 ≤ V := by
    have : 1 * pw k ≤ w * pw k := Int.mul_le_mul_of_nonneg_right hw (by omega)
    omega
  have hR0 : 0 ≤ R := by
    have : 0 * pw k ≤ rtop2 * pw k := Int.mul_le_mul_of_nonneg_right hr2 (by omega)
    omega
  obtain ⟨hRdec, hRr0, hRrb⟩ := ediv_decomp R V hV1
  rcases hqh with ⟨hq, _⟩ | ⟨hq, _⟩
  · -- uncapped: rtop2 < (q̂+1)·w pushes down through the decomposition
    obtain ⟨hdec, hr0, hrb⟩ := ediv_decomp rtop2 w hw
    have hql : qh * w ≤ rtop2 := by rw [hq]; omega
    have hqu : rtop2 < qh * w + w := by rw [hq]; omega
    have hq0 : 0 ≤ qh := by
      rw [hq]
      by_cases h : 0 ≤ rtop2 / w
      · exact h
      · exfalso
        have : rtop2 / w ≤ -1 := by omega
        have h2 : (rtop2 / w) * w ≤ (-1) * w :=
          Int.mul_le_mul_of_nonneg_right this (by omega)
        omega
    -- R < (q̂+1)·V
    have step1 : rtop2 * pw k ≤ (qh * w + w - 1) * pw k :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    have step2 : (qh + 1) * (w * pw k) ≤ (qh + 1) * V := by
      have h1 : w * pw k ≤ V := by omega
      exact Int.mul_le_mul_of_nonneg_left h1 (by omega)
    have expand : (qh * w + w - 1) * pw k + pw k = (qh + 1) * (w * pw k) := by
      have e1 : (qh * w + w - 1) * pw k = (qh * w + w) * pw k - 1 * pw k :=
        Int.sub_mul _ _ _
      have e2 : (qh * w + w) * pw k = qh * w * pw k + w * pw k :=
        Int.add_mul _ _ _
      have e3 : (qh + 1) * (w * pw k) = qh * (w * pw k) + 1 * (w * pw k) :=
        Int.add_mul _ _ _
      have e4 : qh * (w * pw k) = qh * w * pw k := (Int.mul_assoc _ _ _).symm
      omega
    have hRlt : R < (qh + 1) * V := by omega
    exact le_of_mul_sandwich R V qh (R / V) hV1 (by omega) hRlt
  · -- capped at B-1: R < B·V bounds the true digit directly
    rw [hq]
    have := ediv_lt_of_lt_mul R V 4294967296 hV1 hR0 hRB
    omega

/-- q̂ overestimates by at most 4 under quarter-normalization
(`w > 2^30`): the load-bearing bound behind the four straight-line
correction steps. `hlow` covers both estimate cases at once —
uncapped gives `q̂·w ≤ rtop2` as the floor's lower half, capped gives
it from the cap test. -/
theorem qhat_le4 (w rtop2 Rlow R V Vlow k qh : Int)
    (hw : 1073741824 < w) (_hk : 0 ≤ k)
    (hV : V = w * pw k + Vlow) (_hVl : 0 ≤ Vlow) (hVh : Vlow < pw k)
    (hR : R = rtop2 * pw k + Rlow) (hRl : 0 ≤ Rlow) (_hRh : Rlow < pw k)
    (hR0 : 0 ≤ R) (hRB : R < 4294967296 * V)
    (hlow : qh * w ≤ rtop2) (hqB : qh ≤ 4294967295) :
    qh ≤ R / V + 4 := by
  have hpw := pw_pos k
  have hV1 : 1 ≤ V := by
    have : 1 * pw k ≤ w * pw k := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    omega
  obtain ⟨hRdec, hRr0, hRrb⟩ := ediv_decomp R V hV1
  have hq0 : 0 ≤ R / V := by
    by_cases h : 0 ≤ R / V
    · exact h
    · exfalso
      have h1 : R / V ≤ -1 := by omega
      have h2 : R / V * V ≤ (-1) * V := Int.mul_le_mul_of_nonneg_right h1 (by omega)
      omega
  have hqB' : R / V ≤ 4294967295 := by
    have := ediv_lt_of_lt_mul R V 4294967296 hV1 hR0 hRB
    omega
  -- q̂·w·B^k ≤ R < (q+1)·V < (q+1)·(w+1)·B^k  ⟹  q̂·w < (q+1)·(w+1)
  have hRup : R < (R / V + 1) * V := by
    have e : (R / V + 1) * V = R / V * V + 1 * V := Int.add_mul _ _ _
    omega
  have hVup : V < (w + 1) * pw k := by
    have e : (w + 1) * pw k = w * pw k + 1 * pw k := Int.add_mul _ _ _
    omega
  have hRlo : qh * w * pw k ≤ R := by
    have h1 : qh * w * pw k ≤ rtop2 * pw k :=
      Int.mul_le_mul_of_nonneg_right hlow (by omega)
    omega
  have hchain : qh * w * pw k < (R / V + 1) * ((w + 1) * pw k) := by
    have h1 : (R / V + 1) * V ≤ (R / V + 1) * ((w + 1) * pw k - 1) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h2 : (R / V + 1) * ((w + 1) * pw k - 1)
        = (R / V + 1) * ((w + 1) * pw k) - (R / V + 1) * 1 := Int.mul_sub _ _ _
    omega
  have hcancel : qh * w < (R / V + 1) * (w + 1) := by
    have e : (R / V + 1) * ((w + 1) * pw k) = (R / V + 1) * (w + 1) * pw k :=
      (Int.mul_assoc _ _ _).symm
    rw [e] at hchain
    by_cases h : qh * w < (R / V + 1) * (w + 1)
    · exact h
    · exfalso
      have h1 : (R / V + 1) * (w + 1) * pw k ≤ qh * w * pw k :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      omega
  by_cases hfar : qh ≤ R / V + 4
  · exact hfar
  · exfalso
    -- q̂ ≥ q+5:  (q+5)·w ≤ q̂·w < (q+1)·(w+1) = q·w + q + w + 1
    -- ⟹ 4w < q + 1 ⟹ q ≥ 4w > 2^32 - 1 ≥ q. Contradiction.
    have h5 : (R / V + 5) * w ≤ qh * w :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    have e1 : (R / V + 5) * w = R / V * w + 5 * w := Int.add_mul _ _ _
    have e2 : (R / V + 1) * (w + 1) = R / V * (w + 1) + 1 * (w + 1) :=
      Int.add_mul _ _ _
    have e3 : R / V * (w + 1) = R / V * w + R / V * 1 := Int.mul_add _ _ _
    omega

-- ------------------- limb bridges (decompositions) -------------------

/-- Index-shifted congruence: if `out`'s window `[i+1, n+1)` copies
`r`'s window `[i, n)`, the values agree — the shift-in helper's core. -/
theorem valIn_shift (out r : Sable.Seq Int) (i n : Int)
    (h : ∀ k, i ≤ k → k < n → out.get (k + 1) = r.get k) :
    valIn out (i + 1) (n + 1) = valIn r i n := by
  revert h
  fun_induction valIn r i n with
  | case1 i hc ih =>
      intro h
      have h1 : valIn out (i + 1) (n + 1)
          = out.get (i + 1) + 4294967296 * valIn out (i + 1 + 1) (n + 1) := by
        rw [valIn, if_pos (by omega)]
      have h2 := ih (fun k hk1 hk2 => h k (by omega) hk2)
      have h3 := h i (by omega) hc
      rw [h1, h2, h3]
  | case2 i hc =>
      intro _
      rw [valIn, if_neg (by omega)]

/-- Top-two-limbs decomposition with limb-or-zero selectors: for any
`r` with `r.len ≤ n+1`, `natVal r = (r₍n₎·B + r₍n₋₁₎)·B^(n-1) + low`
with `0 ≤ low < B^(n-1)` — exactly the `hR`/`hRl`/`hRh` package the q̂
bounds consume, valid whatever `r`'s actual (trimmed) length. -/
theorem top2_decomp (r : Sable.Seq Int) (n : Int)
    (hn : 1 ≤ n) (_hlen0 : 0 ≤ r.len) (hlen : r.len ≤ n + 1)
    (hb : ∀ k, 0 ≤ k → k < r.len → 0 ≤ r.get k ∧ r.get k ≤ 4294967295) :
    ∃ low, natVal r
        = ((if n < r.len then r.get n else 0) * 4294967296
           + (if n - 1 < r.len then r.get (n - 1) else 0)) * pw (n - 1) + low
      ∧ 0 ≤ low ∧ low < pw (n - 1) := by
  have hpw := pw_pos (n - 1)
  by_cases hc1 : r.len ≤ n - 1
  · -- both selectors read past the end: the whole value is the low part
    refine ⟨natVal r, ?_, ?_, ?_⟩
    · rw [if_neg (by omega), if_neg (by omega)]
      omega
    · exact valIn_nonneg r 0 r.len (fun k hk1 hk2 => (hb k hk1 hk2).1)
    · have h1 := valIn_lt_pw r 0 r.len hb
      have h2 : pw (r.len - 0) ≤ pw (n - 1) := pw_mono _ _ (by omega)
      simp only [natVal]
      omega
  · by_cases hc2 : r.len = n
    · -- one snoc: value = low + r₍n₋₁₎·B^(n-1), top selector is 0
      have hs := valIn_snoc r 0 (n - 1) (by omega)
      rw [show n - 1 + 1 = n from by omega, show n - 1 - 0 = n - 1 from by omega] at hs
      refine ⟨valIn r 0 (n - 1), ?_, ?_, ?_⟩
      · rw [if_neg (by omega), if_pos (by omega)]
        simp only [natVal, hc2]
        rw [hs, Int.zero_mul, Int.zero_add]
        omega
      · exact valIn_nonneg r 0 (n - 1) (fun k hk1 hk2 => (hb k hk1 (by omega)).1)
      · have h1 := valIn_lt_pw r 0 (n - 1) (fun k hk1 hk2 => hb k hk1 (by omega))
        rw [show n - 1 - 0 = n - 1 from by omega] at h1
        exact h1
    · -- r.len = n+1: two snocs fold the top limbs into rtop2
      have hc3 : r.len = n + 1 := by omega
      have hs1 := valIn_snoc r 0 n (by omega)
      rw [show n - 0 = n from by omega] at hs1
      have hs2 := valIn_snoc r 0 (n - 1) (by omega)
      rw [show n - 1 + 1 = n from by omega, show n - 1 - 0 = n - 1 from by omega] at hs2
      have hpwn : pw n = 4294967296 * pw (n - 1) := by
        have := pw_succ (n - 1) (by omega)
        rw [show n - 1 + 1 = n from by omega] at this
        exact this
      refine ⟨valIn r 0 (n - 1), ?_, ?_, ?_⟩
      · rw [if_pos (by omega), if_pos (by omega)]
        simp only [natVal, hc3]
        rw [hs1, hs2, hpwn]
        have e : r.get n * (4294967296 * pw (n - 1))
               = r.get n * 4294967296 * pw (n - 1) := (Int.mul_assoc _ _ _).symm
        rw [e, Int.add_mul]
        omega
      · exact valIn_nonneg r 0 (n - 1) (fun k hk1 hk2 => (hb k hk1 (by omega)).1)
      · have h1 := valIn_lt_pw r 0 (n - 1) (fun k hk1 hk2 => hb k hk1 (by omega))
        rw [show n - 1 - 0 = n - 1 from by omega] at h1
        exact h1

/-- Value bound to top limb: `c·B^(len-1) < natVal v` forces the top
limb above `c` (normalization's landing: vn's top limb > 2^30 from
`t·B^(n-1) < natVal vn`). -/
theorem top_limb_lb (v : Sable.Seq Int) (c : Int)
    (hlen : 1 ≤ v.len)
    (hb : ∀ k, 0 ≤ k → k < v.len → 0 ≤ v.get k ∧ v.get k ≤ 4294967295)
    (hval : c * pw (v.len - 1) ≤ natVal v) :
    c ≤ v.get (v.len - 1) := by
  have hpw := pw_pos (v.len - 1)
  have hs := valIn_snoc v 0 (v.len - 1) (by omega)
  rw [show v.len - 1 + 1 = v.len from by omega,
      show v.len - 1 - 0 = v.len - 1 from by omega] at hs
  have hlow := valIn_lt_pw v 0 (v.len - 1) (fun k hk1 hk2 => hb k hk1 (by omega))
  rw [show v.len - 1 - 0 = v.len - 1 from by omega] at hlow
  have hlow0 := valIn_nonneg v 0 (v.len - 1) (fun k hk1 hk2 => (hb k hk1 (by omega)).1)
  -- natVal v < (top+1)·B^(len-1); with c·B^(len-1) ≤ natVal v cancel.
  have hup : natVal v < (v.get (v.len - 1) + 1) * pw (v.len - 1) := by
    simp only [natVal]
    rw [hs, Int.add_mul]
    omega
  by_cases h : c ≤ v.get (v.len - 1)
  · exact h
  · exfalso
    have h1 : v.get (v.len - 1) + 1 ≤ c := by omega
    have h2 : (v.get (v.len - 1) + 1) * pw (v.len - 1) ≤ c * pw (v.len - 1) :=
      Int.mul_le_mul_of_nonneg_right h1 (by omega)
    omega

/-- Exact length from a value range: a normalized value in
`[B^(k-1), B^k)` has exactly `k` limbs — how vn = v·m keeps v's length. -/
theorem val_range_len (v : Sable.Seq Int) (k : Int)
    (_hk : 1 ≤ k) (_hlen0 : 0 ≤ v.len)
    (hb : ∀ j, 0 ≤ j → j < v.len → 0 ≤ v.get j ∧ v.get j ≤ 4294967295)
    (htop : 0 < v.len → 1 ≤ v.get (v.len - 1))
    (hlo : pw (k - 1) ≤ natVal v) (hhi : natVal v < pw k) :
    v.len = k := by
  simp only [natVal] at hlo hhi
  have hup := valIn_lt_pw v 0 v.len hb
  rw [show v.len - 0 = v.len from by omega] at hup
  have hlen1 : 0 < v.len := by
    by_cases h : 0 < v.len
    · exact h
    · exfalso
      have hz : valIn v 0 v.len = 0 := valIn_nil v 0 v.len (by omega)
      have := pw_pos (k - 1)
      omega
  have hge := valIn_ge_pw v 0 v.len (fun j h1 h2 => (hb j h1 h2).1)
    (htop hlen1) (by omega)
  rw [show v.len - 1 - 0 = v.len - 1 from by omega] at hge
  -- pw(k-1) ≤ val < pw(len)  ⟹  k-1 < len;  pw(len-1) ≤ val < pw(k) ⟹ len-1 < k
  have h1 : k - 1 < v.len := by
    by_cases h : k - 1 < v.len
    · exact h
    · exfalso
      have := pw_mono v.len (k - 1) (by omega)
      omega
  have h2 : v.len - 1 < k := by
    by_cases h : v.len - 1 < k
    · exact h
    · exfalso
      have := pw_mono k (v.len - 1) (by omega)
      omega
  omega

-- -------------------- outer-loop invariant algebra --------------------

/-- One digit step: window `[j, ulen)` opens as `u_j + B·window[j+1..)`;
with the invariant at `j+1` and an exact digit `qd`, the invariant
re-closes at `j`. Pure ring algebra over ghost values. -/
theorem digit_step (S S' Q Q2 R R2 R3 V uj qd : Int)
    (hopen : S = uj + 4294967296 * S')
    (hinv : S' = Q * V + R)
    (hshift : R2 = 4294967296 * R + uj)
    (hQ : Q2 = 4294967296 * Q + qd)
    (hsub : R3 = R2 - qd * V) :
    S = Q2 * V + R3 := by
  subst hopen hinv hshift hQ hsub
  have e1 : (4294967296 * Q + qd) * V = 4294967296 * Q * V + qd * V :=
    Int.add_mul _ _ _
  have e2 : 4294967296 * (Q * V + R) = 4294967296 * (Q * V) + 4294967296 * R :=
    Int.mul_add _ _ _
  have e3 : 4294967296 * (Q * V) = 4294967296 * Q * V := (Int.mul_assoc _ _ _).symm
  omega

/-- The digit is exact when the corrected estimate sandwiches:
`qd·VN ≤ R2 < (qd+1)·VN ⟹ qd = R2 / VN`. -/
theorem digit_exact (R2 VN qd : Int) (hVN : 1 ≤ VN)
    (hlo : qd * VN ≤ R2) (hhi : R2 < (qd + 1) * VN) : qd = R2 / VN := by
  refine div_unique R2 VN qd (R2 - qd * VN) hVN (by omega) (by omega) ?_
  rw [Int.add_mul] at hhi
  omega

/-- Un-normalization for the quotient: from `A·m = Q·(V·m) + R` with
`0 ≤ R < V·m`, `Q` is `A/V` directly — the remainder alone would need
dividing by `m`, and the public `rem` recomputes it as `a - q·b`. -/
theorem denorm_quot (A V Q R m : Int) (hm : 1 ≤ m) (hV : 1 ≤ V)
    (heq : A * m = Q * (V * m) + R) (hR0 : 0 ≤ R) (hRm : R < V * m) :
    Q = A / V := by
  -- R = m·(A - Q·V): divisibility is by construction.
  have hRm' : R = (A - Q * V) * m := by
    have e : Q * (V * m) = Q * V * m := (Int.mul_assoc _ _ _).symm
    rw [e] at heq
    rw [Int.sub_mul]
    omega
  have hd0 : 0 ≤ A - Q * V := by
    by_cases h : 0 ≤ A - Q * V
    · exact h
    · exfalso
      have h1 : A - Q * V ≤ -1 := by omega
      have h2 : (A - Q * V) * m ≤ (-1) * m :=
        Int.mul_le_mul_of_nonneg_right h1 (by omega)
      omega
  have hdV : A - Q * V < V := by
    by_cases h : A - Q * V < V
    · exact h
    · exfalso
      have h1 : V * m ≤ (A - Q * V) * m :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      omega
  exact div_unique A V Q (A - Q * V) hV (by omega) (by omega) hdV

/-- The shifted prefix stays under `B·VN`: the digit loop's re-entry
bound (`R < VN ⟹ B·R + u_j < B·VN`). -/
theorem shift_stays_bounded (R VN uj : Int)
    (hR : R < VN) (hu0 : 0 ≤ uj) (huB : uj ≤ 4294967295) :
    4294967296 * R + uj < 4294967296 * VN := by
  have h1 : 4294967296 * R + 4294967296 ≤ 4294967296 * VN := by
    have h2 : 4294967296 * (R + 1) ≤ 4294967296 * VN :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    rw [Int.mul_add] at h2
    omega
  omega

-- Smoke check: the four-correction sandwich really lands. With
-- q ≤ q̂ ≤ q+4 and four conditional decrements, each firing exactly
-- when qd·VN > R2, the final qd satisfies the digit_exact sandwich.
example (R2 VN q qh : Int) (hVN : 1 ≤ VN)
    (hq : q = R2 / VN) (_hR0 : 0 ≤ R2)
    (hge : q ≤ qh) (_hle : qh ≤ q + 4) :
    -- after at most four decrements the sandwich holds for some qd
    ∃ qd, q ≤ qd ∧ qd ≤ qh ∧ qd * VN ≤ R2 ∧ R2 < (qd + 1) * VN := by
  obtain ⟨hdec, hr0, hrb⟩ := ediv_decomp R2 VN hVN
  refine ⟨q, by omega, hge, ?_, ?_⟩
  · rw [hq]; omega
  · rw [hq, Int.add_mul]; omega
