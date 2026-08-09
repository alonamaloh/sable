/-
Encoding probe for the JSON tokenizer (Tier 2). Validates before
compiler work:
  1. `strTail` — the string-body grammar as a well-founded recursive
     ghost predicate with VARYING step widths (1 for plain chars, 2 for
     short escapes, 6 for \uXXXX);
  2. `lexable` — the token-stream predicate whose recursion target is
     GUARDED (`if pos < e then e else pos + 1`) so the ∃-bound token end
     needs no side condition for termination — the split gives the
     decreasing proof its hypothesis;
  3. the step lemmas the scanners' forward-scan invariants chain
     through (mirroring validFrom_step/validFrom_end).
Core-only, mirroring the in-file `/// def`/`/// theorem` blocks.
-/
import Sable.Seq
import Sable.Auto

namespace JsonProbe

def isWs (c : Int) : Prop := c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13
def digitc (c : Int) : Prop := 48 ≤ c ∧ c ≤ 57
def hexd (c : Int) : Prop :=
  (48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 70) ∨ (97 ≤ c ∧ c ≤ 102)
def escc (c : Int) : Prop :=
  c = 34 ∨ c = 92 ∨ c = 47 ∨ c = 98 ∨ c = 102 ∨ c = 110 ∨ c = 114 ∨ c = 116

/-- String body from `i`: closes with the quote exactly at `j - 1`. -/
def strTail (b : Sable.Seq Int) (i j : Int) : Prop :=
  if j ≤ i then False
  else if b.get i = 34 then j = i + 1
  else if b.get i = 92 then
    (escc (b.get (i + 1)) ∧ strTail b (i + 2) j) ∨
    (b.get (i + 1) = 117 ∧ hexd (b.get (i + 2)) ∧ hexd (b.get (i + 3)) ∧
      hexd (b.get (i + 4)) ∧ hexd (b.get (i + 5)) ∧ strTail b (i + 6) j)
  else 32 ≤ b.get i ∧ strTail b (i + 1) j
termination_by (j - i).toNat
decreasing_by
  all_goals omega

def jstring (b : Sable.Seq Int) (i j : Int) : Prop :=
  b.get i = 34 ∧ strTail b (i + 1) j

def digits (b : Sable.Seq Int) (i j : Int) : Prop :=
  i < j ∧ ∀ k, i ≤ k → k < j → digitc (b.get k)

def jint (b : Sable.Seq Int) (i j : Int) : Prop :=
  (b.get i = 48 ∧ j = i + 1) ∨ (49 ≤ b.get i ∧ b.get i ≤ 57 ∧ digits b i j)

def jfrac (b : Sable.Seq Int) (i j : Int) : Prop :=
  i = j ∨ (b.get i = 46 ∧ digits b (i + 1) j)

def jexp (b : Sable.Seq Int) (i j : Int) : Prop :=
  i = j ∨ ((b.get i = 101 ∨ b.get i = 69) ∧
    (digits b (i + 1) j ∨
      ((b.get (i + 1) = 43 ∨ b.get (i + 1) = 45) ∧ digits b (i + 2) j)))

def jnumber (b : Sable.Seq Int) (i j : Int) : Prop :=
  ∃ p q, ((b.get i = 45 ∧ jint b (i + 1) p) ∨ (b.get i ≠ 45 ∧ jint b i p)) ∧
    jfrac b p q ∧ jexp b q j ∧ i < p ∧ p ≤ q ∧ q ≤ j

def jpunct (c : Int) : Prop :=
  c = 123 ∨ c = 125 ∨ c = 91 ∨ c = 93 ∨ c = 58 ∨ c = 44

def jtoken (b : Sable.Seq Int) (i j : Int) : Prop :=
  (jpunct (b.get i) ∧ j = i + 1) ∨
  (b.get i = 116 ∧ b.get (i + 1) = 114 ∧ b.get (i + 2) = 117 ∧
    b.get (i + 3) = 101 ∧ j = i + 4) ∨
  (b.get i = 102 ∧ b.get (i + 1) = 97 ∧ b.get (i + 2) = 108 ∧
    b.get (i + 3) = 115 ∧ b.get (i + 4) = 101 ∧ j = i + 5) ∨
  (b.get i = 110 ∧ b.get (i + 1) = 117 ∧ b.get (i + 2) = 108 ∧
    b.get (i + 3) = 108 ∧ j = i + 4) ∨
  jstring b i j ∨
  jnumber b i j

/-- Whole-buffer tokenizability. The recursion target is guarded so the
    ∃-bound end needs no termination side condition. -/
def lexable (b : Sable.Seq Int) (pos : Int) : Prop :=
  if b.len ≤ pos then True
  else (isWs (b.get pos) ∧ lexable b (pos + 1)) ∨
    (∃ e, jtoken b pos e ∧ pos < e ∧ e ≤ b.len ∧
      lexable b (if pos < e then e else pos + 1))
termination_by (b.len - pos).toNat
decreasing_by
  all_goals first | omega | (split <;> omega)

-- Step lemmas (the scanners' forward-scan invariants chain through
-- these; shapes mirror validFrom_step/validFrom_end).

theorem strTail_close (b : Sable.Seq Int) (i : Int) (h : b.get i = 34) :
    strTail b i (i + 1) := by
  rw [strTail]
  rw [if_neg (by omega), if_pos h]

theorem strTail_char (b : Sable.Seq Int) (i j : Int)
    (hq : b.get i ≠ 34) (he : b.get i ≠ 92) (hlo : 32 ≤ b.get i)
    (hj : i < j)
    (hrest : strTail b (i + 1) j) : strTail b i j := by
  rw [strTail]
  rw [if_neg (by omega), if_neg hq, if_neg he]
  exact ⟨hlo, hrest⟩

theorem strTail_esc (b : Sable.Seq Int) (i j : Int)
    (hq : b.get i ≠ 34) (he : b.get i = 92) (hesc : escc (b.get (i + 1)))
    (hj : i < j)
    (hrest : strTail b (i + 2) j) : strTail b i j := by
  rw [strTail]
  rw [if_neg (by omega), if_neg hq, if_pos he]
  exact Or.inl ⟨hesc, hrest⟩

theorem strTail_hex (b : Sable.Seq Int) (i j : Int)
    (hq : b.get i ≠ 34) (he : b.get i = 92) (hu : b.get (i + 1) = 117)
    (h2 : hexd (b.get (i + 2))) (h3 : hexd (b.get (i + 3)))
    (h4 : hexd (b.get (i + 4))) (h5 : hexd (b.get (i + 5)))
    (hj : i < j)
    (hrest : strTail b (i + 6) j) : strTail b i j := by
  rw [strTail]
  rw [if_neg (by omega), if_neg hq, if_pos he]
  exact Or.inr ⟨hu, h2, h3, h4, h5, hrest⟩

theorem lexable_end (b : Sable.Seq Int) (pos : Int) (h : b.len ≤ pos) :
    lexable b pos := by
  rw [lexable]
  rw [if_pos h]
  trivial

theorem lexable_ws (b : Sable.Seq Int) (pos : Int)
    (hpos : pos < b.len) (hws : isWs (b.get pos))
    (hrest : lexable b (pos + 1)) : lexable b pos := by
  rw [lexable]
  rw [if_neg (by omega)]
  exact Or.inl ⟨hws, hrest⟩

theorem lexable_tok (b : Sable.Seq Int) (pos e : Int)
    (hpos : pos < b.len) (ht : jtoken b pos e)
    (hlt : pos < e) (hle : e ≤ b.len)
    (hrest : lexable b e) : lexable b pos := by
  rw [lexable]
  rw [if_neg (by omega)]
  refine Or.inr ⟨e, ht, hlt, hle, ?_⟩
  rw [if_pos hlt]
  exact hrest

end JsonProbe
