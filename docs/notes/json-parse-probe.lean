/-
Encoding probe for the JSON parser (Tier 2, layer 2). Validates the
riskiest ghost def yet before compiler work:

  `jgram b m i j` — the RFC 8259 value grammar as ONE well-founded
  recursive predicate, mode-encoded (0 value / 1 object-interior /
  4 object-tail / 2 array-interior / 6 array-tail) because ghost defs
  splice as single `def`s (no `mutual`). Every recursive call is
  guarded with the M10 ite-trick so the single measure (j - i).toNat
  strictly decreases on every edge:
    - position-advance guards: `if i < x then x else i + 1`
    - span-shrink guards:      `if e ≤ j then e else j`
  and a top guard `j ≤ i → False` (every production occupies at least
  one byte) puts `i < j` in scope for every decreasing goal.

Token-level predicates (jstring/jnumber/literals) are stand-ins with
the right arity — the real file uses the M10 definitions; nothing here
unfolds them.
-/
import Sable.Seq
import Sable.Auto

namespace JsonParseProbe

def isWs (c : Int) : Prop := c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13

/-- ws from `i` up to (not including) `p`. -/
def wsTo (b : Sable.Seq Int) (i p : Int) : Prop :=
  i ≤ p ∧ ∀ k, i ≤ k → k < p → isWs (b.get k)

-- Stand-ins (right arity; real file uses the M10 ghosts).
def jstring (b : Sable.Seq Int) (i j : Int) : Prop := b.get i = 34 ∧ i < j
def jnumber (b : Sable.Seq Int) (i j : Int) : Prop := 45 ≤ b.get i ∧ i < j
def jtrue (b : Sable.Seq Int) (i j : Int) : Prop := b.get i = 116 ∧ j = i + 4
def jfalse (b : Sable.Seq Int) (i j : Int) : Prop := b.get i = 102 ∧ j = i + 5
def jnull (b : Sable.Seq Int) (i j : Int) : Prop := b.get i = 110 ∧ j = i + 4

def jgram (b : Sable.Seq Int) (m i j : Int) : Prop :=
  if j ≤ i then False
  else if m = 0 then
    -- a ws-led value occupying exactly [i, j)
    ∃ p, wsTo b i p ∧
      (jstring b p j ∨ jnumber b p j ∨ jtrue b p j ∨ jfalse b p j ∨
        jnull b p j ∨
        (b.get p = 123 ∧ jgram b 1 (if i < p + 1 then p + 1 else i + 1) j) ∨
        (b.get p = 91 ∧ jgram b 2 (if i < p + 1 then p + 1 else i + 1) j))
  else if m = 1 then
    -- object interior (after `{`): ws `}` , or first member then tail
    (∃ q, wsTo b i q ∧ b.get q = 125 ∧ j = q + 1) ∨
    (∃ q r s e, wsTo b i q ∧ jstring b q r ∧ wsTo b r s ∧ b.get s = 58 ∧
      jgram b 0 (if i < s + 1 then s + 1 else i + 1) (if e ≤ j then e else j) ∧
      jgram b 4 (if i < e then e else i + 1) j)
  else if m = 4 then
    -- object tail: ws `}` , or ws `,` member then tail
    (∃ q, wsTo b i q ∧ b.get q = 125 ∧ j = q + 1) ∨
    (∃ q q2 r s e, wsTo b i q ∧ b.get q = 44 ∧ wsTo b (q + 1) q2 ∧
      jstring b q2 r ∧ wsTo b r s ∧ b.get s = 58 ∧
      jgram b 0 (if i < s + 1 then s + 1 else i + 1) (if e ≤ j then e else j) ∧
      jgram b 4 (if i < e then e else i + 1) j)
  else if m = 2 then
    -- array interior (after `[`): ws `]` , or first element then tail
    (∃ q, wsTo b i q ∧ b.get q = 93 ∧ j = q + 1) ∨
    (∃ e, jgram b 0 i (if e < j then e else j - 1) ∧
      jgram b 6 (if i < e then e else i + 1) j)
  else if m = 6 then
    -- array tail: ws `]` , or ws `,` element then tail
    (∃ q, wsTo b i q ∧ b.get q = 93 ∧ j = q + 1) ∨
    (∃ q e, wsTo b i q ∧ b.get q = 44 ∧
      jgram b 0 (if i < q + 1 then q + 1 else i + 1) (if e ≤ j then e else j) ∧
      jgram b 6 (if i < e then e else i + 1) j)
  else False
termination_by (j - i).toNat
decreasing_by
  all_goals first | omega | (split <;> first | omega | (split <;> omega))

/-- Everything `jgram` accepts occupies at least one byte. -/
theorem jgram_lt (b : Sable.Seq Int) (m i j : Int) (h : jgram b m i j) :
    i < j := by
  rw [jgram] at h
  split at h
  · exact h.elim
  · omega

-- Step lemmas: the parser's discharges chain through these, mirroring
-- strTail_*/lexable_*. Guard-reduction is `rw [if_pos (by omega)]`.

theorem jgram_val_tok (b : Sable.Seq Int) (i p j : Int)
    (hw : wsTo b i p)
    (ht : jstring b p j ∨ jnumber b p j ∨ jtrue b p j ∨ jfalse b p j ∨
      jnull b p j)
    (hij : i < j) : jgram b 0 i j := by
  rw [jgram]
  rw [if_neg (by omega), if_pos rfl]
  refine ⟨p, hw, ?_⟩
  exact ht.elim (fun h => Or.inl h) (fun h2 => h2.elim
    (fun h => Or.inr (Or.inl h)) (fun h3 => h3.elim
      (fun h => Or.inr (Or.inr (Or.inl h))) (fun h4 => h4.elim
        (fun h => Or.inr (Or.inr (Or.inr (Or.inl h))))
        (fun h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

theorem jgram_val_obj (b : Sable.Seq Int) (i p j : Int)
    (hw : wsTo b i p) (hb : b.get p = 123)
    (hrest : jgram b 1 (p + 1) j) : jgram b 0 i j := by
  have hij : i < j := by
    have := jgram_lt b 1 (p + 1) j hrest
    have hp := hw.1
    omega
  rw [jgram]
  rw [if_neg (by omega), if_pos rfl]
  refine ⟨p, hw, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, ?_⟩)))))⟩
  rw [if_pos (by have := hw.1; omega)]
  exact hrest

theorem jgram_obj_empty (b : Sable.Seq Int) (i q : Int)
    (hw : wsTo b i q) (hb : b.get q = 125) : jgram b 1 i (q + 1) := by
  rw [jgram]
  rw [if_neg (by have := hw.1; omega), if_pos rfl]
  exact Or.inl ⟨q, hw, hb, rfl⟩

theorem jgram_obj_member (b : Sable.Seq Int) (i q r s e j : Int)
    (hw : wsTo b i q) (hs : jstring b q r) (hw2 : wsTo b r s)
    (hc : b.get s = 58)
    (hv : jgram b 0 (s + 1) e) (htail : jgram b 4 e j)
    (hiq : i ≤ q) (hqs : q ≤ s) : jgram b 1 i j := by
  have hse : s + 1 < e := by
    have h1 := jgram_lt b 0 (s + 1) e hv
    omega
  have hej : e < j := jgram_lt b 4 e j htail
  rw [jgram]
  rw [if_neg (by omega), if_pos rfl]
  refine Or.inr ⟨q, r, s, e, hw, hs, hw2, hc, ?_, ?_⟩
  · rw [if_pos (by omega), if_pos (by omega)]
    exact hv
  · rw [if_pos (by omega)]
    exact htail

theorem jgram_objtail_close (b : Sable.Seq Int) (i q : Int)
    (hw : wsTo b i q) (hb : b.get q = 125) : jgram b 4 i (q + 1) := by
  rw [jgram]
  rw [if_neg (by have := hw.1; omega), if_neg (by omega), if_neg (by omega),
    if_pos rfl]
  exact Or.inl ⟨q, hw, hb, rfl⟩

theorem jgram_objtail_member (b : Sable.Seq Int) (i q q2 r s e j : Int)
    (hw : wsTo b i q) (hb : b.get q = 44) (hw1 : wsTo b (q + 1) q2)
    (hs : jstring b q2 r)
    (hw2 : wsTo b r s) (hc : b.get s = 58)
    (hv : jgram b 0 (s + 1) e) (htail : jgram b 4 e j)
    (hiq : i ≤ q) (hqs : q ≤ s) : jgram b 4 i j := by
  have hse : s + 1 < e := jgram_lt b 0 (s + 1) e hv
  have hej : e < j := jgram_lt b 4 e j htail
  rw [jgram]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  refine Or.inr ⟨q, q2, r, s, e, hw, hb, hw1, hs, hw2, hc, ?_, ?_⟩
  · rw [if_pos (by omega), if_pos (by omega)]
    exact hv
  · rw [if_pos (by omega)]
    exact htail

theorem jgram_arr_empty (b : Sable.Seq Int) (i q : Int)
    (hw : wsTo b i q) (hb : b.get q = 93) : jgram b 2 i (q + 1) := by
  rw [jgram]
  rw [if_neg (by have := hw.1; omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]
  exact Or.inl ⟨q, hw, hb, rfl⟩

theorem jgram_arr_elem (b : Sable.Seq Int) (i e j : Int)
    (hv : jgram b 0 i e) (htail : jgram b 6 e j) : jgram b 2 i j := by
  have hie : i < e := jgram_lt b 0 i e hv
  have hej : e < j := jgram_lt b 6 e j htail
  rw [jgram]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]
  refine Or.inr ⟨e, ?_, ?_⟩
  · rw [if_pos (by omega)]
    exact hv
  · rw [if_pos (by omega)]
    exact htail

theorem jgram_arrtail_close (b : Sable.Seq Int) (i q : Int)
    (hw : wsTo b i q) (hb : b.get q = 93) : jgram b 6 i (q + 1) := by
  rw [jgram]
  rw [if_neg (by have := hw.1; omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos rfl]
  exact Or.inl ⟨q, hw, hb, rfl⟩

theorem jgram_arrtail_elem (b : Sable.Seq Int) (i q e j : Int)
    (hw : wsTo b i q) (hb : b.get q = 44)
    (hv : jgram b 0 (q + 1) e) (htail : jgram b 6 e j)
    (hiq : i ≤ q) : jgram b 6 i j := by
  have hqe : q + 1 < e := jgram_lt b 0 (q + 1) e hv
  have hej : e < j := jgram_lt b 6 e j htail
  rw [jgram]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos rfl]
  refine Or.inr ⟨q, e, hw, hb, ?_, ?_⟩
  · rw [if_pos (by omega), if_pos (by omega)]
    exact hv
  · rw [if_pos (by omega)]
    exact htail

end JsonParseProbe
