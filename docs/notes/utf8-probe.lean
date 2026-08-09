/-
Encoding probe for the UTF-8 codec (Tier 2). Validates before compiler
work:
  1. the ghost byte maps and the ghost byte-level decoder — if-chains
     over /% by CONSTANTS, inside omega's fragment once split;
  2. `utf8_decode_encode`: ghost decode of the canonical bytes is the
     identity on scalar values — the single theorem the program-level
     roundtrip needs (the decoder's post says `v = utf8_decode bytes`,
     the encoder's posts say `bytes = utf8_b* cp`);
  3. byte-range lemmas for the encoder's narrow<u8> obligations.
Core-only, mirroring the in-file `/// def`/`/// theorem` blocks.
-/
import Sable.Seq
import Sable.Auto

namespace Utf8Probe

def utf8_len (cp : Int) : Int :=
  if cp < 128 then 1 else if cp < 2048 then 2 else if cp < 65536 then 3 else 4

def utf8_b0 (cp : Int) : Int :=
  if cp < 128 then cp
  else if cp < 2048 then 192 + cp / 64
  else if cp < 65536 then 224 + cp / 4096
  else 240 + cp / 262144

def utf8_b1 (cp : Int) : Int :=
  if cp < 2048 then 128 + cp % 64
  else if cp < 65536 then 128 + (cp / 64) % 64
  else 128 + (cp / 4096) % 64

def utf8_b2 (cp : Int) : Int :=
  if cp < 65536 then 128 + cp % 64 else 128 + (cp / 64) % 64

def utf8_b3 (cp : Int) : Int := 128 + cp % 64

/-- Ghost byte-level decoder; arguments past the length class are junk
    and ignored. -/
def utf8_decode (b0 b1 b2 b3 : Int) : Int :=
  if b0 < 128 then b0
  else if b0 < 224 then (b0 - 192) * 64 + (b1 - 128)
  else if b0 < 240 then (b0 - 224) * 4096 + (b1 - 128) * 64 + (b2 - 128)
  else (b0 - 240) * 262144 + (b1 - 128) * 4096 + (b2 - 128) * 64 + (b3 - 128)

/-- A Unicode scalar value: in range, not a surrogate. -/
def scalar (cp : Int) : Prop :=
  0 ≤ cp ∧ cp ≤ 1114111 ∧ (cp < 55296 ∨ cp > 57343)

theorem utf8_b0_range (cp : Int) (h : scalar cp) :
    0 ≤ utf8_b0 cp ∧ utf8_b0 cp ≤ 255 := by
  unfold scalar at h
  unfold utf8_b0
  repeat (first | omega | split)

theorem utf8_b1_range (cp : Int) (h : scalar cp) :
    128 ≤ utf8_b1 cp ∧ utf8_b1 cp ≤ 191 := by
  unfold scalar at h
  unfold utf8_b1
  repeat (first | omega | split)

theorem utf8_b2_range (cp : Int) (h : scalar cp) :
    128 ≤ utf8_b2 cp ∧ utf8_b2 cp ≤ 191 := by
  unfold scalar at h
  unfold utf8_b2
  repeat (first | omega | split)

theorem utf8_b3_range (cp : Int) (h : scalar cp) :
    128 ≤ utf8_b3 cp ∧ utf8_b3 cp ≤ 191 := by
  unfold scalar at h
  unfold utf8_b3
  omega

/-- Ghost decode of the canonical bytes is the identity: THE roundtrip
    theorem. Everything is linear once the ifs split. -/
theorem utf8_decode_encode (cp : Int) (h : scalar cp) :
    utf8_decode (utf8_b0 cp) (utf8_b1 cp) (utf8_b2 cp) (utf8_b3 cp) = cp := by
  unfold scalar at h
  unfold utf8_decode utf8_b0 utf8_b1 utf8_b2 utf8_b3
  repeat (first | omega | split)

/-- Junk-tolerant form matching the encoder's guarded posts: the tail
    bytes are only known canonical when the length class reaches them —
    exactly what the program-level roundtrip has in hand. -/
theorem utf8_decode_encode' (cp g1 g2 g3 : Int) (h : scalar cp)
    (h1 : 2 ≤ utf8_len cp → g1 = utf8_b1 cp)
    (h2 : 3 ≤ utf8_len cp → g2 = utf8_b2 cp)
    (h3 : utf8_len cp = 4 → g3 = utf8_b3 cp) :
    utf8_decode (utf8_b0 cp) g1 g2 g3 = cp := by
  unfold scalar at h
  unfold utf8_len at h1 h2 h3
  unfold utf8_decode utf8_b0 utf8_b1 utf8_b2 utf8_b3 at *
  repeat (first | omega | split | split at h1 | split at h2 | split at h3)

/-- Buffer-level validity from `pos`: decomposable into canonical
    scalar encodings. Well-founded on the remaining length; the probe
    validates that this ghost-def shape (termination_by/decreasing_by on
    an Int measure) survives the verbatim-splice pipeline. -/
def validFrom (b : Sable.Seq Int) (pos : Int) : Prop :=
  if b.len ≤ pos then True
  else ∃ cp, scalar cp ∧ pos + utf8_len cp ≤ b.len ∧
    b.get pos = utf8_b0 cp ∧
    (2 ≤ utf8_len cp → b.get (pos + 1) = utf8_b1 cp) ∧
    (3 ≤ utf8_len cp → b.get (pos + 2) = utf8_b2 cp) ∧
    (utf8_len cp = 4 → b.get (pos + 3) = utf8_b3 cp) ∧
    validFrom b (pos + utf8_len cp)
termination_by (b.len - pos).toNat
decreasing_by
  unfold utf8_len
  repeat (first | omega | split)

/-- The forward-scan step: canonical bytes at `pos` plus validity of the
    rest give validity at `pos`. -/
theorem validFrom_step (b : Sable.Seq Int) (pos cp : Int)
    (hpos : pos < b.len)
    (hs : scalar cp) (hlen : pos + utf8_len cp ≤ b.len)
    (h0 : b.get pos = utf8_b0 cp)
    (h1 : 2 ≤ utf8_len cp → b.get (pos + 1) = utf8_b1 cp)
    (h2 : 3 ≤ utf8_len cp → b.get (pos + 2) = utf8_b2 cp)
    (h3 : utf8_len cp = 4 → b.get (pos + 3) = utf8_b3 cp)
    (hrest : validFrom b (pos + utf8_len cp)) :
    validFrom b pos := by
  rw [validFrom]
  rw [if_neg (by omega)]
  exact ⟨cp, hs, hlen, h0, h1, h2, h3, hrest⟩

/-- The scan-exit base case. -/
theorem validFrom_end (b : Sable.Seq Int) (pos : Int) (h : b.len ≤ pos) :
    validFrom b pos := by
  rw [validFrom]
  rw [if_pos h]
  trivial

end Utf8Probe
