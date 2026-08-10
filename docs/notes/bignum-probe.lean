/-
Encoding probe for the bignum pillar (Nat over [u32] limbs, little-endian,
normalized: no leading zero limb).

Validates, before any compiler or corpus work:
  1. the ghost valuation — `valIn a i n` (value of limbs [i, n), recursion
     shaped like utf8's validFrom so it splices as a Sable ghost def) with
     `natVal a = valIn a 0 a.len`, plus `pw n` (= 2^32n) for the weighted
     loop invariants;
  2. the lemma library every discharge will replay: bounds (nonneg, < pw,
     ≥ pw for normalized), congruence, snoc (append a limb at the top),
     set (store inside the prefix);
  3. cmp's two closers: first-difference (equal above j, a[j] < b[j] ⇒
     value <) and shorter-normalized-is-smaller;
  4. add/sub loop-invariant preservation and the carry/borrow = 0 exit
     arguments — the `carry * pw i` products are outside omega's fragment,
     so these steps are where the nonlinear pain starts;
  5. the crux: schoolbook mul's inner/outer step lemmas, with genuine
     summation rearrangement (a[i]·b[j]·pw i·pw j) — the probe determines
     whether the pain stays contained in targeted mul_comm/assoc rewrites.

Core-only (no mathlib), mirroring the VC shapes vcgen emits: Sable.Seq for
limb arrays, element bounds as the `h_field_limbs_elems` hypothesis shape
(0 ≤ get k ≤ 4294967295), everything Int.

Note for the discharges: `fun_induction f a i n` leaves each case's goal
with the scrutinized call already unfolded to the branch body — do not
`rw [f]` again; other occurrences (different arguments) still unfold via
standalone `have`s.
-/
import Sable.Seq
import Sable.Auto

namespace BignumProbe

/-- pw n = (2^32)^n for n ≥ 0 (and 1 for n ≤ 0): the weight of limb n. -/
def pw (n : Int) : Int := if 0 < n then 4294967296 * pw (n - 1) else 1
termination_by n.toNat
decreasing_by omega

/-- Value of limbs [i, n) of `a`, little-endian base 2^32. -/
def valIn (a : Sable.Seq Int) (i n : Int) : Int :=
  if i < n then a.get i + 4294967296 * valIn a (i + 1) n else 0
termination_by (n - i).toNat
decreasing_by omega

/-- The abstraction function: the integer a limb sequence denotes. -/
@[simp] def natVal (a : Sable.Seq Int) : Int := valIn a 0 a.len

-- ------------------------------------------------------------------ pw

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

theorem pw_add (m n : Int) (hm : 0 ≤ m) (hn : 0 ≤ n) :
    pw (m + n) = pw m * pw n := by
  revert hm
  fun_induction pw m with
  | case1 m h ih =>
      intro hm
      have h1 : pw (m + n) = 4294967296 * pw (m - 1 + n) := by
        rw [pw, if_pos (by omega)]
        have e : m + n - 1 = m - 1 + n := by omega
        rw [e]
      rw [h1, ih (by omega)]
      exact (Int.mul_assoc _ _ _).symm
  | case2 m h =>
      intro hm
      have e : m = 0 := by omega
      subst e
      rw [Int.zero_add, Int.one_mul]

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

-- --------------------------------------------------------------- valIn

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

/-- Normalized lower bound: a nonzero top limb puts the value at or above
    its weight. -/
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
        omega
  | case2 i h =>
      intro _ hin
      omega

theorem valIn_congr (a b : Sable.Seq Int) (i n : Int)
    (h : ∀ k, i ≤ k → k < n → a.get k = b.get k) :
    valIn a i n = valIn b i n := by
  revert h
  fun_induction valIn a i n with
  | case1 i hc ih =>
      intro h
      have hab := h i (by omega) hc
      have ht := ih (fun k hk1 hk2 => h k (by omega) hk2)
      have hbu : valIn b i n = b.get i + 4294967296 * valIn b (i + 1) n := by
        rw [valIn, if_pos hc]
      rw [hbu]
      omega
  | case2 i hc =>
      intro _
      have hbu : valIn b i n = 0 := by rw [valIn, if_neg hc]
      rw [hbu]

/-- THE workhorse: append the top limb. Every bottom-up loop invariant
    extends its processed prefix through this. -/
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

/-- Store inside the prefix: the value moves by the delta at the slot's
    weight. Schoolbook mul's accumulator steps live on this. -/
theorem valIn_set (a : Sable.Seq Int) (i n p v : Int)
    (hpn : p < n) (hip : i ≤ p) :
    valIn (a.set p v) i n = valIn a i n + (v - a.get p) * pw (p - i) := by
  revert hip
  fun_induction valIn a i n with
  | case1 i hc ih =>
      intro hip
      by_cases hpi : i = p
      · have h1 : valIn (a.set p v) i n
            = v + 4294967296 * valIn (a.set p v) (i + 1) n := by
          rw [valIn, if_pos hc, Sable.Seq.get_set, if_pos hpi]
        have h2 : valIn (a.set p v) (i + 1) n = valIn a (i + 1) n :=
          valIn_congr _ _ _ _ (fun k hk1 hk2 => by
            rw [Sable.Seq.get_set, if_neg (by omega)])
        rw [h1, h2, show p - i = 0 from by omega, pw_nonpos 0 (by omega),
            ← hpi]
        omega
      · have h1 : valIn (a.set p v) i n
            = a.get i + 4294967296 * valIn (a.set p v) (i + 1) n := by
          rw [valIn, if_pos hc, Sable.Seq.get_set, if_neg (by omega)]
        have h2 := ih (by omega)
        have h3 : pw (p - i) = 4294967296 * pw (p - (i + 1)) := by
          rw [pw, if_pos (by omega)]
          have e : p - i - 1 = p - (i + 1) := by omega
          rw [e]
        rw [h1, h2, h3]
        have e : (v - a.get p) * (4294967296 * pw (p - (i + 1)))
               = 4294967296 * ((v - a.get p) * pw (p - (i + 1))) :=
          Int.mul_left_comm _ _ _
        rw [e, Int.mul_add]
        omega
  | case2 i hc =>
      intro hip
      omega

-- ----------------------------------------------------------------- cmp

/-- A strict comparison at index j propagates down to index i when the
    limbs below j are bounded (a's from above, b's from below). -/
theorem valIn_lt_down (a b : Sable.Seq Int) (i j n : Int)
    (hjn : j < n)
    (h : valIn a j n < valIn b j n)
    (hb1 : ∀ k, i ≤ k → k < j → 0 ≤ a.get k ∧ a.get k ≤ 4294967295)
    (hb2 : ∀ k, i ≤ k → k < j → 0 ≤ b.get k)
    (hij : i ≤ j) :
    valIn a i n < valIn b i n := by
  revert hb1 hb2 hij
  fun_induction valIn a i n with
  | case1 i hc ih =>
      intro hb1 hb2 hij
      by_cases hje : i = j
      · have hau : valIn a i n = a.get i + 4294967296 * valIn a (i + 1) n := by
          rw [valIn, if_pos hc]
        rw [← hau, hje]
        exact h
      · have step := ih (fun k hk1 hk2 => hb1 k (by omega) hk2)
                        (fun k hk1 hk2 => hb2 k (by omega) hk2) (by omega)
        have ha := hb1 i (by omega) (by omega)
        have hbi := hb2 i (by omega) (by omega)
        have hbu : valIn b i n = b.get i + 4294967296 * valIn b (i + 1) n := by
          rw [valIn, if_pos hc]
        rw [hbu]
        omega
  | case2 i hc =>
      intro _ _ hij
      omega

/-- cmp's descending scan, at the first difference: equal limbs above j,
    a.get j < b.get j ⇒ the whole values compare strictly. -/
theorem cmp_first_diff (a b : Sable.Seq Int) (j n : Int)
    (hj : 0 ≤ j) (hjn : j < n)
    (heq : ∀ k, j < k → k < n → a.get k = b.get k)
    (hlt : a.get j < b.get j)
    (hb1 : ∀ k, 0 ≤ k → k < n → 0 ≤ a.get k ∧ a.get k ≤ 4294967295)
    (hb2 : ∀ k, 0 ≤ k → k < n → 0 ≤ b.get k) :
    valIn a 0 n < valIn b 0 n := by
  have htail : valIn a (j + 1) n = valIn b (j + 1) n :=
    valIn_congr _ _ _ _ (fun k hk1 hk2 => heq k (by omega) hk2)
  have hj' : valIn a j n < valIn b j n := by
    rw [valIn, if_pos hjn]
    have hbu : valIn b j n = b.get j + 4294967296 * valIn b (j + 1) n := by
      rw [valIn, if_pos hjn]
    rw [hbu, htail]
    omega
  exact valIn_lt_down a b 0 j n hjn hj'
    (fun k hk1 hk2 => hb1 k hk1 (by omega))
    (fun k hk1 hk2 => hb2 k hk1 (by omega)) hj

/-- Fewer limbs, when the longer number is normalized, means smaller. -/
theorem natVal_lt_of_len_lt (a b : Sable.Seq Int)
    (hlen : a.len < b.len) (halen : 0 ≤ a.len)
    (hb1 : ∀ k, 0 ≤ k → k < a.len → 0 ≤ a.get k ∧ a.get k ≤ 4294967295)
    (hb2 : ∀ k, 0 ≤ k → k < b.len → 0 ≤ b.get k)
    (htop : 1 ≤ b.get (b.len - 1)) :
    natVal a < natVal b := by
  have h1 := valIn_lt_pw a 0 a.len hb1
  have h2 := valIn_ge_pw b 0 b.len hb2 htop (by omega)
  have h3 : pw (a.len - 0) ≤ pw (b.len - 1 - 0) := pw_mono _ _ (by omega)
  simp only [natVal]
  omega

/-- Contrapositive form for sub: a dominated value cannot be longer. -/
theorem len_le_of_val_le (a b : Sable.Seq Int)
    (hle : natVal b ≤ natVal a) (halen : 0 ≤ a.len)
    (hb1 : ∀ k, 0 ≤ k → k < a.len → 0 ≤ a.get k ∧ a.get k ≤ 4294967295)
    (hb2 : ∀ k, 0 ≤ k → k < b.len → 0 ≤ b.get k)
    (htop : 0 < b.len → 1 ≤ b.get (b.len - 1)) :
    b.len ≤ a.len := by
  by_cases h : b.len ≤ a.len
  · exact h
  · have := natVal_lt_of_len_lt a b (by omega) halen hb1 hb2 (htop (by omega))
    omega

-- -------------------------------------------------------------- trim

/-- Dropping a zero top limb preserves the value: the trim loop's
    invariant step. -/
theorem trim_top_zero (xs : Sable.Seq Int) (rl : Int) (h0 : 0 < rl)
    (hz : xs.get (rl - 1) = 0) :
    valIn xs 0 rl = valIn xs 0 (rl - 1) := by
  have h := valIn_snoc xs 0 (rl - 1) (by omega)
  rw [show rl - 1 + 1 = rl from by omega] at h
  rw [h, hz]
  omega

/-- from_prefix's value post: a copied prefix denotes the same value. -/
theorem prefix_val (s xs : Sable.Seq Int) (rl : Int)
    (hlen : s.len = rl)
    (hcopy : ∀ k, 0 ≤ k → k < rl → s.get k = xs.get k) :
    natVal s = valIn xs 0 rl := by
  simp only [natVal, hlen]
  exact valIn_congr _ _ _ _ (fun k hk1 hk2 => hcopy k (by omega) hk2)

-- ---------------------------------------------------------------- add

/-- Carry recombination: the stored low limb plus the carried high part
    reassemble to s at weight P. Keeps the div/mod algebra in one place. -/
theorem carry_split (s P : Int) :
    s % 4294967296 * P + s / 4294967296 * (4294967296 * P) = s * P := by
  have h : s % 4294967296 + 4294967296 * (s / 4294967296) = s := by
    omega
  calc s % 4294967296 * P + s / 4294967296 * (4294967296 * P)
      = s % 4294967296 * P + s / 4294967296 * 4294967296 * P := by
        rw [Int.mul_assoc]
    _ = (s % 4294967296 + 4294967296 * (s / 4294967296)) * P := by
        rw [Int.add_mul, Int.mul_comm (s / 4294967296) 4294967296]
    _ = s * P := by rw [h]

/-- add's loop-invariant preservation: one limb of the classic carry
    chain, mixed lengths handled by the min-ite. -/
theorem add_step (out a b : Sable.Seq Int) (i la lb carry s : Int)
    (hi : 0 ≤ i) (_hla : 0 ≤ la) (_hlb : 0 ≤ lb)
    (hs : s = carry + (if i < la then a.get i else 0)
                    + (if i < lb then b.get i else 0))
    (hinv : valIn out 0 i + carry * pw i
          = valIn a 0 (if i ≤ la then i else la)
          + valIn b 0 (if i ≤ lb then i else lb)) :
    valIn (out.set i (s % 4294967296)) 0 (i + 1)
        + s / 4294967296 * pw (i + 1)
      = valIn a 0 (if i + 1 ≤ la then i + 1 else la)
      + valIn b 0 (if i + 1 ≤ lb then i + 1 else lb) := by
  have h1 : valIn (out.set i (s % 4294967296)) 0 (i + 1)
      = valIn out 0 i + s % 4294967296 * pw i := by
    have hsn := valIn_snoc (out.set i (s % 4294967296)) 0 i (by omega)
    have hgi : (out.set i (s % 4294967296)).get i = s % 4294967296 := by
      rw [Sable.Seq.get_set, if_pos rfl]
    have hcg : valIn (out.set i (s % 4294967296)) 0 i = valIn out 0 i :=
      valIn_congr _ _ _ _ (fun k hk1 hk2 => by
        rw [Sable.Seq.get_set, if_neg (by omega)])
    rw [hsn, hgi, hcg, show i - 0 = i from by omega]
  have hp1 : pw (i + 1) = 4294967296 * pw i := pw_succ i hi
  have hkey : valIn (out.set i (s % 4294967296)) 0 (i + 1)
      + s / 4294967296 * pw (i + 1)
      = valIn out 0 i + s * pw i := by
    rw [h1, hp1, Int.add_assoc, carry_split]
  rw [hkey, hs, Int.add_mul, Int.add_mul]
  by_cases hia : i < la
  · have hsa : valIn a 0 (i + 1) = valIn a 0 i + a.get i * pw i := by
      have h := valIn_snoc a 0 i (by omega)
      rw [show i - 0 = i from by omega] at h
      exact h
    by_cases hib : i < lb
    · have hsb : valIn b 0 (i + 1) = valIn b 0 i + b.get i * pw i := by
        have h := valIn_snoc b 0 i (by omega)
        rw [show i - 0 = i from by omega] at h
        exact h
      rw [if_pos hia, if_pos hib,
          if_pos (show i + 1 ≤ la from by omega),
          if_pos (show i + 1 ≤ lb from by omega), hsa, hsb]
      rw [if_pos (show i ≤ la from by omega),
          if_pos (show i ≤ lb from by omega)] at hinv
      omega
    · have hsb : (if i + 1 ≤ lb then i + 1 else lb) = lb := by
        split <;> omega
      have hsb2 : (if i ≤ lb then i else lb) = lb := by
        split <;> omega
      rw [if_pos hia, if_neg hib,
          if_pos (show i + 1 ≤ la from by omega), hsb, hsa]
      rw [if_pos (show i ≤ la from by omega), hsb2] at hinv
      omega
  · have hsa : (if i + 1 ≤ la then i + 1 else la) = la := by
      split <;> omega
    have hsa2 : (if i ≤ la then i else la) = la := by
      split <;> omega
    by_cases hib : i < lb
    · have hsb : valIn b 0 (i + 1) = valIn b 0 i + b.get i * pw i := by
        have h := valIn_snoc b 0 i (by omega)
        rw [show i - 0 = i from by omega] at h
        exact h
      rw [if_neg hia, if_pos hib, hsa,
          if_pos (show i + 1 ≤ lb from by omega), hsb]
      rw [hsa2, if_pos (show i ≤ lb from by omega)] at hinv
      omega
    · have hsb : (if i + 1 ≤ lb then i + 1 else lb) = lb := by
        split <;> omega
      have hsb2 : (if i ≤ lb then i else lb) = lb := by
        split <;> omega
      rw [if_neg hia, if_neg hib, hsa, hsb]
      rw [hsa2, hsb2] at hinv
      omega

/-- add's exit: with one extra slot the final carry is zero. -/
theorem add_carry_zero (out a b : Sable.Seq Int) (n la lb carry : Int)
    (hla : 0 ≤ la) (_hlb : 0 ≤ lb)
    (hn : la < n ∧ lb < n)
    (hcb : 0 ≤ carry ∧ carry ≤ 1)
    (hbo : ∀ k, 0 ≤ k → k < n → 0 ≤ out.get k)
    (hba : ∀ k, 0 ≤ k → k < la → 0 ≤ a.get k ∧ a.get k ≤ 4294967295)
    (hbb : ∀ k, 0 ≤ k → k < lb → 0 ≤ b.get k ∧ b.get k ≤ 4294967295)
    (hinv : valIn out 0 n + carry * pw n = valIn a 0 la + valIn b 0 lb) :
    carry = 0 := by
  have h1 := valIn_lt_pw a 0 la hba
  have h2 := valIn_lt_pw b 0 lb hbb
  have h3 := valIn_nonneg out 0 n hbo
  have h4 : pw (la - 0) ≤ pw (n - 1) := pw_mono _ _ (by omega)
  have h5 : pw (lb - 0) ≤ pw (n - 1) := pw_mono _ _ (by omega)
  have h6 : pw n = 4294967296 * pw (n - 1) := by
    rw [pw, if_pos (by omega)]
  rcases (show carry = 0 ∨ carry = 1 from by omega) with h | h
  · exact h
  · exfalso
    rw [h, Int.one_mul, h6] at hinv
    have := pw_pos (n - 1)
    omega

-- ---------------------------------------------------------------- sub

/-- sub's loop-invariant preservation: borrow chain via s = a[i] + B - y
    - borrow, so every program value stays a u64. -/
theorem sub_step (out a b : Sable.Seq Int) (i lb borrow s : Int)
    (hi : 0 ≤ i) (_hlb : 0 ≤ lb)
    (hs : s = a.get i + 4294967296
            - (if i < lb then b.get i else 0) - borrow)
    (hinv : valIn out 0 i - borrow * pw i
          = valIn a 0 i - valIn b 0 (if i ≤ lb then i else lb)) :
    valIn (out.set i (s % 4294967296)) 0 (i + 1)
        - (1 - s / 4294967296) * pw (i + 1)
      = valIn a 0 (i + 1)
      - valIn b 0 (if i + 1 ≤ lb then i + 1 else lb) := by
  have h1 : valIn (out.set i (s % 4294967296)) 0 (i + 1)
      = valIn out 0 i + s % 4294967296 * pw i := by
    have hsn := valIn_snoc (out.set i (s % 4294967296)) 0 i (by omega)
    have hgi : (out.set i (s % 4294967296)).get i = s % 4294967296 := by
      rw [Sable.Seq.get_set, if_pos rfl]
    have hcg : valIn (out.set i (s % 4294967296)) 0 i = valIn out 0 i :=
      valIn_congr _ _ _ _ (fun k hk1 hk2 => by
        rw [Sable.Seq.get_set, if_neg (by omega)])
    rw [hsn, hgi, hcg, show i - 0 = i from by omega]
  have hp1 : pw (i + 1) = 4294967296 * pw i := pw_succ i hi
  have hkey : valIn (out.set i (s % 4294967296)) 0 (i + 1)
      - (1 - s / 4294967296) * pw (i + 1)
      = valIn out 0 i + s * pw i - pw (i + 1) := by
    have hc := carry_split s (pw i)
    rw [h1, hp1, Int.sub_mul, Int.one_mul]
    omega
  have hsa : valIn a 0 (i + 1) = valIn a 0 i + a.get i * pw i := by
    have h := valIn_snoc a 0 i (by omega)
    rw [show i - 0 = i from by omega] at h
    exact h
  rw [hkey, hs, hsa, hp1, Int.sub_mul, Int.sub_mul, Int.add_mul]
  by_cases hib : i < lb
  · have hsb : valIn b 0 (i + 1) = valIn b 0 i + b.get i * pw i := by
      have h := valIn_snoc b 0 i (by omega)
      rw [show i - 0 = i from by omega] at h
      exact h
    rw [if_pos hib, if_pos (show i + 1 ≤ lb from by omega), hsb]
    rw [if_pos (show i ≤ lb from by omega)] at hinv
    omega
  · have hsb : (if i + 1 ≤ lb then i + 1 else lb) = lb := by
      split <;> omega
    have hsb2 : (if i ≤ lb then i else lb) = lb := by
      split <;> omega
    rw [if_neg hib, hsb]
    rw [hsb2] at hinv
    omega

/-- sub's exit: with natVal b ≤ natVal a the final borrow is zero. -/
theorem sub_borrow_zero (out a b : Sable.Seq Int) (la lb borrow : Int)
    (_hla : 0 ≤ la)
    (hbw : 0 ≤ borrow ∧ borrow ≤ 1)
    (hbo : ∀ k, 0 ≤ k → k < la → 0 ≤ out.get k ∧ out.get k ≤ 4294967295)
    (hle : valIn b 0 lb ≤ valIn a 0 la)
    (hinv : valIn out 0 la - borrow * pw la
          = valIn a 0 la - valIn b 0 lb) :
    borrow = 0 := by
  have h1 := valIn_lt_pw out 0 la hbo
  rw [show la - 0 = la from by omega] at h1
  rcases (show borrow = 0 ∨ borrow = 1 from by omega) with h | h
  · exact h
  · exfalso
    rw [h, Int.one_mul] at hinv
    omega

-- ---------------------------------------------------------------- mul

/-- THE crux: schoolbook mul's inner-loop preservation. Genuine summation
    rearrangement: a[i]·b[j] enters at weight pw i · pw j = pw (i+j). -/
theorem mul_inner_step (out a b : Sable.Seq Int) (i j n lb carry t : Int)
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hjlb : j < lb) (hin : i + lb ≤ n)
    (ht : t = out.get (i + j) + a.get i * b.get j + carry)
    (hinv : valIn out 0 n + carry * pw (i + j)
          = valIn a 0 i * valIn b 0 lb + a.get i * valIn b 0 j * pw i) :
    valIn (out.set (i + j) (t % 4294967296)) 0 n
        + t / 4294967296 * pw (i + j + 1)
      = valIn a 0 i * valIn b 0 lb
      + a.get i * valIn b 0 (j + 1) * pw i := by
  have hset := valIn_set out 0 n (i + j) (t % 4294967296) (by omega) (by omega)
  rw [show i + j - 0 = i + j from by omega] at hset
  have hp1 : pw (i + j + 1) = 4294967296 * pw (i + j) :=
    pw_succ (i + j) (by omega)
  have hkey : valIn (out.set (i + j) (t % 4294967296)) 0 n
      + t / 4294967296 * pw (i + j + 1)
      = valIn out 0 n + (t - out.get (i + j)) * pw (i + j) := by
    have hc := carry_split t (pw (i + j))
    rw [hset, hp1, Int.sub_mul, Int.sub_mul]
    omega
  have hsb : valIn b 0 (j + 1) = valIn b 0 j + b.get j * pw j := by
    have h := valIn_snoc b 0 j (by omega)
    rw [show j - 0 = j from by omega] at h
    exact h
  have hab : (t - out.get (i + j)) * pw (i + j)
      = a.get i * b.get j * pw (i + j) + carry * pw (i + j) := by
    rw [ht]
    have e : out.get (i + j) + a.get i * b.get j + carry - out.get (i + j)
           = a.get i * b.get j + carry := by omega
    rw [e, Int.add_mul]
  have hd : a.get i * valIn b 0 (j + 1) * pw i
      = a.get i * valIn b 0 j * pw i + a.get i * b.get j * pw (i + j) := by
    rw [hsb, Int.mul_add, Int.add_mul, pw_add i j hi hj]
    have e : a.get i * (b.get j * pw j) * pw i
           = a.get i * b.get j * (pw i * pw j) := by
      ac_rfl
    rw [e]
  rw [hkey, hab, hd]
  omega

/-- mul's outer-loop close: store the leftover carry in the (still zero)
    slot i+lb, completing one full row a[i]·b. -/
theorem mul_outer_close (out a b : Sable.Seq Int) (i n lb carry : Int)
    (hi : 0 ≤ i) (_hlb : 0 ≤ lb) (hin : i + lb < n)
    (hzero : out.get (i + lb) = 0)
    (hinv : valIn out 0 n + carry * pw (i + lb)
          = valIn a 0 i * valIn b 0 lb + a.get i * valIn b 0 lb * pw i) :
    valIn (out.set (i + lb) carry) 0 n
      = valIn a 0 (i + 1) * valIn b 0 lb := by
  have hset := valIn_set out 0 n (i + lb) carry (by omega) (by omega)
  rw [show i + lb - 0 = i + lb from by omega, hzero, Int.sub_zero] at hset
  have hsa : valIn a 0 (i + 1) = valIn a 0 i + a.get i * pw i := by
    have h := valIn_snoc a 0 i (by omega)
    rw [show i - 0 = i from by omega] at h
    exact h
  rw [hset, hsa, Int.add_mul]
  have e : a.get i * pw i * valIn b 0 lb
         = a.get i * valIn b 0 lb * pw i := by
    rw [Int.mul_assoc, Int.mul_comm (pw i) (valIn b 0 lb), ← Int.mul_assoc]
  rw [e]
  omega

/-- mul's result bound: the product of two bounded prefixes fits in
    la + lb limbs — the allocation is big enough and no carry escapes. -/
theorem mul_fits (a b : Sable.Seq Int) (la lb : Int)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb)
    (hba : ∀ k, 0 ≤ k → k < la → 0 ≤ a.get k ∧ a.get k ≤ 4294967295)
    (hbb : ∀ k, 0 ≤ k → k < lb → 0 ≤ b.get k ∧ b.get k ≤ 4294967295) :
    valIn a 0 la * valIn b 0 lb < pw (la + lb) := by
  have h1 := valIn_lt_pw a 0 la hba
  have h2 := valIn_lt_pw b 0 lb hbb
  have h3 := valIn_nonneg a 0 la (fun k hk1 hk2 => (hba k hk1 hk2).1)
  have h4 := valIn_nonneg b 0 lb (fun k hk1 hk2 => (hbb k hk1 hk2).1)
  have h5 := pw_pos la
  have h6 := pw_pos lb
  have hpa : pw (la + lb) = pw la * pw lb := pw_add la lb hla hlb
  rw [show la - 0 = la from by omega] at h1
  rw [show lb - 0 = lb from by omega] at h2
  have s1 : valIn a 0 la * valIn b 0 lb ≤ valIn a 0 la * (pw lb - 1) :=
    Int.mul_le_mul_of_nonneg_left (by omega) h3
  have s2 : valIn a 0 la * (pw lb - 1) ≤ (pw la - 1) * (pw lb - 1) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  have s3 : (pw la - 1) * (pw lb - 1)
      = pw la * pw lb - pw la - pw lb + 1 := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.one_mul, Int.mul_one]
    omega
  omega

/-- An all-zero range denotes zero: the freshly allocated accumulator. -/
theorem valIn_zeros (a : Sable.Seq Int) (i n : Int)
    (hz : ∀ k, i ≤ k → k < n → a.get k = 0) : valIn a i n = 0 := by
  revert hz
  fun_induction valIn a i n with
  | case1 i h ih =>
      intro hz
      have h1 := ih (fun k hk1 hk2 => hz k (by omega) hk2)
      have h2 := hz i (by omega) h
      omega
  | case2 i h =>
      intro _
      omega

/-- The u64 headroom of a limb product: schoolbook mul's operation VCs. -/
theorem mul_bound (x y : Int)
    (hx : 0 ≤ x ∧ x ≤ 4294967295) (hy : 0 ≤ y ∧ y ≤ 4294967295) :
    0 ≤ x * y ∧ x * y ≤ 18446744065119617025 := by
  constructor
  · exact Int.mul_nonneg hx.1 hy.1
  · calc x * y ≤ x * 4294967295 := Int.mul_le_mul_of_nonneg_left hy.2 hx.1
      _ ≤ 4294967295 * 4294967295 := Int.mul_le_mul_of_nonneg_right hx.2 (by omega)
      _ = 18446744065119617025 := by decide

-- ---------------------------------------------------------------- div

/-- The uniqueness closer: double-and-subtract's exit facts pin the
    Euclidean quotient. -/
theorem div_unique (a b q r : Int) (hb : 1 ≤ b)
    (h : q * b + r = a) (hr0 : 0 ≤ r) (hrb : r < b) : q = a / b := by
  have h2 := (Int.ediv_emod_unique (a := a) (b := b) (r := r) (q := q)
      (by omega : (0:Int) < b)).mpr
    ⟨by rw [Int.mul_comm b q]; omega, hr0, hrb⟩
  omega

/-- rem as composition: r = a − (a/b)·b is the Euclidean remainder. -/
theorem rem_eq (a b q p : Int) (hq : q = a / b) (hp : p = q * b) :
    a - p = a % b := by
  rw [hp, hq, Int.mul_comm]
  have := Int.emod_def a b
  omega

/-- The doubling step keeps d = b·m. -/
theorem double_mul (v m d : Int) (h : d = v * m) : d + d = v * (m + m) := by
  rw [h, Int.mul_add]

/-- The outer step keeps q·b + r = a when (q+m)·b absorbs d = b·m. -/
theorem outer_step (q m v r d a : Int)
    (hinv : q * v + r = a) (hd : d = v * m) :
    (q + m) * v + (r - d) = a := by
  rw [Int.add_mul, hd, Int.mul_comm v m]
  omega

/-- m stays under d = v·m when the divisor is nonzero: bound for the
    inner call-pre lengths. -/
theorem le_self_mul (v m : Int) (hv : 1 ≤ v) (hm : 0 ≤ m) : m ≤ v * m := by
  have h := Int.mul_le_mul_of_nonneg_right hv hm
  rw [Int.one_mul] at h
  omega

/-- q·v ≥ 0: lets omega read r ≤ a off the outer invariant. -/
theorem mul_nonneg_atoms (q v : Int) (hq : 0 ≤ q) (hv : 0 ≤ v) :
    0 ≤ q * v := Int.mul_nonneg hq hv

/-- The quotient is dominated by the dividend (nonneg, divisor ≥ 1):
    bound for rem's mul call-pre lengths. -/
theorem ediv_le_self_nat (a b : Int) (ha : 0 ≤ a) (_hb : 1 ≤ b) :
    a / b ≤ a := Int.ediv_le_self b ha

/-- (a/b)·b ≤ a: sub's pre in rem's composition. -/
theorem ediv_mul_le_self (a b : Int) (_ha : 0 ≤ a) (hb : 1 ≤ b) :
    a / b * b ≤ a := by
  have := Int.emod_def a b
  have := Int.emod_nonneg a (by omega : b ≠ 0)
  rw [Int.mul_comm]
  omega

end BignumProbe
