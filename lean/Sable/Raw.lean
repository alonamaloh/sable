/-
Sable prelude: resource *views*.

A resource is authority the checker keeps affine and the logic never
sees. What the logic sees is the resource's view: an ordinary value,
whose facts are duplicable knowledge, exactly like the `Seq` a borrowed
array lifts to. Nothing here mentions a heap, a capability, or
disjointness — that is the interpretation (`Own (h, Δ)`, ADR 0022), it
lives in the metatheory, and no generated VC ever receives it as a
hypothesis.

Everything is `Int` for the same reason `Seq` is (design §2.1): program
values lift to ℤ, and mixing in `Nat` costs coercions at every clause.
-/

import Sable.Seq

namespace Sable

/-- Raw storage is not a byte sequence: uninitialized is a distinct
state, and it must stay distinguishable from every inhabitant of a value
type. An initialized `option<u8>` holding `none` is not uninitialized
memory. -/
inductive ByteState where
  | uninit : ByteState
  | init : Int → ByteState
  deriving DecidableEq, Repr

/-- The byte, if this state has one. Junk-free: `none` is the honest
answer for uninitialized storage, and the initialization VC is what keeps
verified programs away from it. -/
def ByteState.value? : ByteState → Option Int
  | .uninit => none
  | .init b => some b

/-- The view of a `RawSpan`: which allocation, where in it, how long, and
what the bytes are. `alloc` is provenance, never an address — two live
spans may share a machine address only if they share an allocation. -/
structure SpanView where
  alloc : Int
  off : Int
  len : Int
  bytes : Seq ByteState

/-- Well-formedness of a span view, assumed at every binding site: a
length is nonnegative and its byte sequence covers it. Authority is not
in here; this is the shape of the value. -/
def SpanView.wf (v : SpanView) : Prop :=
  0 ≤ v.len ∧ v.len ≤ v.bytes.len

@[simp] theorem SpanView.wf_iff (v : SpanView) :
    v.wf ↔ (0 ≤ v.len ∧ v.len ≤ v.bytes.len) := Iff.rfl

/-- The first `n` bytes. Together with `drop` this is what `split_off`
redistributes: the prefix stays in the borrowed token, the suffix leaves
in the returned one. -/
def SpanView.take (v : SpanView) (n : Int) : SpanView :=
  { v with len := n, bytes := v.bytes }

/-- Everything past the first `n` bytes, as a span in its own right:
the offset advances and the byte sequence is re-indexed. -/
def SpanView.drop (v : SpanView) (n : Int) : SpanView :=
  { alloc := v.alloc,
    off := v.off + n,
    len := v.len - n,
    bytes := ⟨v.bytes.len - n, fun k => v.bytes.get (k + n)⟩ }

/-- Two adjacent spans of one allocation, as a single span. The
adjacency side conditions are the caller's obligation, not a hypothesis
here: `join` states them as a `pre`, so nonadjacency is a failed VC and
not a checker error. -/
def SpanView.cat (v1 v2 : SpanView) : SpanView :=
  { alloc := v1.alloc,
    off := v1.off,
    len := v1.len + v2.len,
    bytes := ⟨v1.len + v2.bytes.len,
              fun k => if k < v1.len then v1.bytes.get k else v2.bytes.get (k - v1.len)⟩ }

@[simp] theorem SpanView.take_len (v : SpanView) (n : Int) :
    (v.take n).len = n := rfl

@[simp] theorem SpanView.take_off (v : SpanView) (n : Int) :
    (v.take n).off = v.off := rfl

@[simp] theorem SpanView.take_alloc (v : SpanView) (n : Int) :
    (v.take n).alloc = v.alloc := rfl

@[simp] theorem SpanView.drop_len (v : SpanView) (n : Int) :
    (v.drop n).len = v.len - n := rfl

@[simp] theorem SpanView.drop_off (v : SpanView) (n : Int) :
    (v.drop n).off = v.off + n := rfl

@[simp] theorem SpanView.drop_alloc (v : SpanView) (n : Int) :
    (v.drop n).alloc = v.alloc := rfl

@[simp] theorem SpanView.cat_len (v1 v2 : SpanView) :
    (v1.cat v2).len = v1.len + v2.len := rfl

@[simp] theorem SpanView.cat_off (v1 v2 : SpanView) :
    (v1.cat v2).off = v1.off := rfl

@[simp] theorem SpanView.cat_alloc (v1 v2 : SpanView) :
    (v1.cat v2).alloc = v1.alloc := rfl

/-- A byte of a rejoined span comes from whichever half covers it. -/
@[simp] theorem SpanView.cat_get (v1 v2 : SpanView) (k : Int) :
    (v1.cat v2).bytes.get k =
      if k < v1.len then v1.bytes.get k else v2.bytes.get (k - v1.len) := rfl

@[simp] theorem SpanView.take_bytes_len (v : SpanView) (n : Int) :
    (v.take n).bytes.len = v.bytes.len := rfl

@[simp] theorem SpanView.drop_bytes_len (v : SpanView) (n : Int) :
    (v.drop n).bytes.len = v.bytes.len - n := rfl

@[simp] theorem SpanView.cat_bytes_len (v1 v2 : SpanView) :
    (v1.cat v2).bytes.len = v1.len + v2.bytes.len := rfl

/-- Splitting preserves total length: the two halves account for the
whole, which is the fact a carving loop's invariant is written against. -/
theorem SpanView.take_drop_len (v : SpanView) (n : Int) :
    (v.take n).len + (v.drop n).len = v.len := by
  simp; omega

/-- A byte of the prefix is that byte of the whole. -/
@[simp] theorem SpanView.take_get (v : SpanView) (n k : Int) :
    (v.take n).bytes.get k = v.bytes.get k := rfl

/-- A byte of the suffix is the byte `n` further along the whole. -/
@[simp] theorem SpanView.drop_get (v : SpanView) (n k : Int) :
    (v.drop n).bytes.get k = v.bytes.get (k + n) := rfl

/-- Rejoining a split span recovers every byte: `cat` on `take`/`drop`
agrees with the original everywhere the original is defined. This is the
round-trip a split-then-join must not lose. -/
theorem SpanView.cat_take_drop_get (v : SpanView) (n k : Int) :
    ((v.take n).cat (v.drop n)).bytes.get k = v.bytes.get k := by
  show (if k < n then _ else _) = _
  split
  · rfl
  · show v.bytes.get (k - n + n) = v.bytes.get k
    congr 1
    omega

/-- Well-formedness survives a split, in both halves. -/
theorem SpanView.wf_take {v : SpanView} {n : Int}
    (hv : v.wf) (h0 : 0 ≤ n) (hn : n ≤ v.len) : (v.take n).wf := by
  obtain ⟨_, hb⟩ := hv
  exact ⟨h0, by simp; omega⟩

theorem SpanView.wf_drop {v : SpanView} {n : Int}
    (hv : v.wf) (hn : n ≤ v.len) : (v.drop n).wf := by
  obtain ⟨_, hb⟩ := hv
  exact ⟨by simp; omega, by simp; omega⟩

theorem SpanView.wf_cat {v1 v2 : SpanView}
    (h1 : v1.wf) (h2 : v2.wf) : (v1.cat v2).wf := by
  obtain ⟨hl1, hb1⟩ := h1
  obtain ⟨hl2, hb2⟩ := h2
  exact ⟨by simp; omega, by simp; omega⟩

/-! ## Pointers

A raw pointer is provenance plus an offset, never an address — the same
choice the machine makes. In the logic it is an ordinary value with two
projections, and its only job in a contract is to say *which* byte an
operation names. -/

structure RawPtr where
  alloc : Int
  off : Int

/-- The pointer at the start of a span. -/
def SpanView.start (v : SpanView) : RawPtr :=
  { alloc := v.alloc, off := v.off }

@[simp] theorem SpanView.start_alloc (v : SpanView) : v.start.alloc = v.alloc := rfl
@[simp] theorem SpanView.start_off (v : SpanView) : v.start.off = v.off := rfl

/-- Moving a pointer. Pure: nothing is dereferenced, so a pointer may sit
outside its allocation with no consequence until a load or a store asks. -/
def RawPtr.add (p : RawPtr) (d : Int) : RawPtr :=
  { p with off := p.off + d }

@[simp] theorem RawPtr.add_alloc (p : RawPtr) (d : Int) : (p.add d).alloc = p.alloc := rfl
@[simp] theorem RawPtr.add_off (p : RawPtr) (d : Int) : (p.add d).off = p.off + d := rfl

/-- Whether `p` names byte `k` of `v`, counting from the span's start.
This is the premise every raw operation carries instead of a global
provenance predicate: same allocation, and the offset lands inside. -/
def SpanView.namesByte (v : SpanView) (p : RawPtr) (k : Int) : Prop :=
  p.alloc = v.alloc ∧ p.off = v.off + k ∧ 0 ≤ k ∧ k < v.len

/-- Unfolded for automation: a `namesByte` goal is three comparisons and
an allocation equality, which is what `omega` wants to see. -/
@[simp] theorem SpanView.namesByte_iff (v : SpanView) (p : RawPtr) (k : Int) :
    v.namesByte p k ↔ (p.alloc = v.alloc ∧ p.off = v.off + k ∧ 0 ≤ k ∧ k < v.len) :=
  Iff.rfl

/-! ## The bridge between safe arrays and raw bytes

Lexical exposure hands a safe `[u8]` to the raw world and takes it back.
These two functions are that bridge, and they are the only place the two
worlds meet: `ofSeq` is what the body starts from, `toSeq` is what the
array becomes at scope exit. -/

/-- The value in a byte state, with `uninit` reading as zero. The zero is
never load-bearing: reconstructing an array carries an obligation that
every byte in range is initialized, so the junk case is unreachable in
verified code — the same discipline `Seq.get` off-range follows. -/
def ByteState.byte : ByteState → Int
  | .init b => b
  | .uninit => 0

@[simp] theorem ByteState.byte_init (b : Int) : (ByteState.init b).byte = b := rfl

@[simp] theorem ByteState.byte_uninit : ByteState.uninit.byte = 0 := rfl

/-- Push `byte` through a conditional. A store rewrites one index, so
every fact about a written span is a conditional; leaving `byte` outside
it is what stalls `omega`. -/
@[simp] theorem ByteState.byte_ite (c : Prop) [Decidable c] (x y : ByteState) :
    (if c then x else y).byte = if c then x.byte else y.byte := by
  split <;> rfl

@[simp] theorem ByteState.init_ne_uninit (b : Int) : ByteState.init b ≠ .uninit := by
  intro h; exact ByteState.noConfusion h

/-- Every byte of a span that a safe array needs is present. -/
def SpanView.allInit (v : SpanView) : Prop :=
  ∀ k, 0 ≤ k → k < v.len → v.bytes.get k ≠ .uninit

/-- Unfolded for automation. The vocabulary has to be *visible*: `simp`
does not see through a reducible definition, so every spec-level notion
here carries an explicit unfolding lemma. -/
@[simp] theorem SpanView.allInit_iff (v : SpanView) :
    v.allInit ↔ ∀ k, 0 ≤ k → k < v.len → v.bytes.get k ≠ .uninit := Iff.rfl

/-- A safe array's bytes, as a span at offset 0 of allocation `alloc`.
Every byte starts initialized, which is what makes the safe world's
"there is no uninitialized value" true on the way in. -/
def SpanView.ofSeq (alloc : Int) (s : Seq Int) : SpanView :=
  { alloc := alloc, off := 0, len := s.len,
    bytes := ⟨s.len, fun k => .init (s.get k)⟩ }

@[simp] theorem SpanView.ofSeq_alloc (a : Int) (s : Seq Int) :
    (SpanView.ofSeq a s).alloc = a := rfl

@[simp] theorem SpanView.ofSeq_off (a : Int) (s : Seq Int) :
    (SpanView.ofSeq a s).off = 0 := rfl

@[simp] theorem SpanView.ofSeq_len (a : Int) (s : Seq Int) :
    (SpanView.ofSeq a s).len = s.len := rfl

@[simp] theorem SpanView.ofSeq_get (a : Int) (s : Seq Int) (k : Int) :
    (SpanView.ofSeq a s).bytes.get k = .init (s.get k) := rfl

/-- The array a span's bytes reconstruct. -/
def SpanView.toSeq (v : SpanView) : Seq Int :=
  ⟨v.len, fun k => (v.bytes.get k).byte⟩

@[simp] theorem SpanView.toSeq_len (v : SpanView) : v.toSeq.len = v.len := rfl

@[simp] theorem SpanView.toSeq_get (v : SpanView) (k : Int) :
    v.toSeq.get k = (v.bytes.get k).byte := rfl

/-- Exposing an array and taking it straight back is the identity, on
every index the array has. This is the fact a shared exposure needs and
the base case a mutable one starts from. -/
theorem SpanView.toSeq_ofSeq (a : Int) (s : Seq Int) (k : Int) :
    (SpanView.ofSeq a s).toSeq.get k = s.get k := rfl

theorem SpanView.ofSeq_allInit (a : Int) (s : Seq Int) :
    (SpanView.ofSeq a s).allInit := by
  intro k _ _; simp [SpanView.allInit]

/-- The bytes an exposed array starts with are its elements, so their
`byte` values are the elements themselves. This is what carries the
array's element-range facts into the raw world and back. -/
@[simp] theorem SpanView.ofSeq_byte (a : Int) (s : Seq Int) (k : Int) :
    ((SpanView.ofSeq a s).bytes.get k).byte = s.get k := rfl

/-- One byte written. Stating a store's effect as a *function* rather
than a conjunction of facts is what keeps automation out of case
analysis: the composition lemmas below fire on the shape, instead of
`grind` having to instantiate a "every other index is unchanged"
hypothesis. -/
def SpanView.write (v : SpanView) (k : Int) (b : ByteState) : SpanView :=
  { v with bytes := v.bytes.set k b }

@[simp] theorem SpanView.write_alloc (v : SpanView) (k : Int) (b : ByteState) :
    (v.write k b).alloc = v.alloc := rfl

@[simp] theorem SpanView.write_off (v : SpanView) (k : Int) (b : ByteState) :
    (v.write k b).off = v.off := rfl

@[simp] theorem SpanView.write_len (v : SpanView) (k : Int) (b : ByteState) :
    (v.write k b).len = v.len := rfl

@[simp] theorem SpanView.write_get (v : SpanView) (k j : Int) (b : ByteState) :
    (v.write k b).bytes.get j = if j = k then b else v.bytes.get j := by
  simp [SpanView.write, Seq.get_set]

/-! ## Reconstructing a safe array

`reconstructible` is the whole condition for handing bytes back to the
safe world: every byte the array needs is present, and every one of them
is a real `u8`. Keeping it a single notion — rather than an
initialization obligation and a range obligation — is what lets one
composition lemma per operation carry it, and that is the difference
between a wrapper that verifies and one that needs hand proofs. -/

def SpanView.reconstructible (v : SpanView) : Prop :=
  ∀ k, 0 ≤ k → k < v.len →
    v.bytes.get k ≠ .uninit ∧ 0 ≤ (v.bytes.get k).byte ∧ (v.bytes.get k).byte ≤ 255

/-- Unfolded for automation. Stated without an existential on purpose:
`∃ b, get k = .init b ∧ ...` reads better and defeats `grind`, which then
has to invent the witness at every index. -/
@[simp] theorem SpanView.reconstructible_iff (v : SpanView) :
    v.reconstructible ↔ ∀ k, 0 ≤ k → k < v.len →
      v.bytes.get k ≠ .uninit ∧ 0 ≤ (v.bytes.get k).byte ∧ (v.bytes.get k).byte ≤ 255 :=
  Iff.rfl

/-- Reconstructibility implies presence, which is the half `allInit`
names. -/
theorem SpanView.reconstructible_allInit {v : SpanView} (h : v.reconstructible) :
    v.allInit := fun k h0 hk => (h k h0 hk).1

/-- ...and it implies the reconstructed array is a `[u8]`: every element
in range is a byte value. This is what keeps the safe world's typing true
across an exposure. -/
theorem SpanView.reconstructible_range {v : SpanView} (h : v.reconstructible)
    (k : Int) (h0 : 0 ≤ k) (hk : k < v.len) : 0 ≤ v.toSeq.get k ∧ v.toSeq.get k ≤ 255 :=
  ⟨(h k h0 hk).2.1, (h k h0 hk).2.2⟩

/-- An array's own bytes are reconstructible, given that its elements are
bytes — which is exactly what the safe world already guarantees for a
`[u8]`. This is the base case of every exposure. -/
theorem SpanView.ofSeq_reconstructible (a : Int) (s : Seq Int)
    (h : ∀ k, 0 ≤ k → k < s.len → 0 ≤ s.get k ∧ s.get k ≤ 255) :
    (SpanView.ofSeq a s).reconstructible := by
  intro k h0 hk
  obtain ⟨hlo, hhi⟩ := h k h0 (by simpa using hk)
  exact ⟨by simp, by simpa using hlo, by simpa using hhi⟩

/-- A destination after a transfer of `n` bytes from `src`, starting from_
`from_`. One equation covers a short read and a failed one alike: `n = 0`
leaves every byte where it was, so a contract stating its effect this way
needs no case analysis on the outcome — the same lesson `write` taught,
applied to a *foreign* contract (ADR 0028). -/
def SpanView.fillFrom (v : SpanView) (n : Int) (src : Seq Int) (from_ : Int) : SpanView :=
  { v with
    bytes := ⟨v.bytes.len, fun k =>
      if 0 ≤ k ∧ k < n then .init (src.get (from_ + k)) else v.bytes.get k⟩ }

@[simp] theorem SpanView.fillFrom_alloc (v : SpanView) (n : Int) (src : Seq Int) (from_ : Int) :
    (v.fillFrom n src from_).alloc = v.alloc := rfl

@[simp] theorem SpanView.fillFrom_off (v : SpanView) (n : Int) (src : Seq Int) (from_ : Int) :
    (v.fillFrom n src from_).off = v.off := rfl

@[simp] theorem SpanView.fillFrom_len (v : SpanView) (n : Int) (src : Seq Int) (from_ : Int) :
    (v.fillFrom n src from_).len = v.len := rfl

@[simp] theorem SpanView.fillFrom_bytes_len (v : SpanView) (n : Int) (src : Seq Int) (from_ : Int) :
    (v.fillFrom n src from_).bytes.len = v.bytes.len := rfl

@[simp] theorem SpanView.fillFrom_get (v : SpanView) (n : Int) (src : Seq Int) (from_ k : Int) :
    (v.fillFrom n src from_).bytes.get k =
      if 0 ≤ k ∧ k < n then .init (src.get (from_ + k)) else v.bytes.get k := rfl

/-- A transfer of bytes leaves the destination reconstructible: the bytes
that arrived are bytes, and the rest were already fine. -/
theorem SpanView.fillFrom_reconstructible {v : SpanView} {n from_ : Int} {src : Seq Int}
    (hv : v.reconstructible) (hsrc : ∀ k, 0 ≤ src.get k ∧ src.get k ≤ 255) :
    (v.fillFrom n src from_).reconstructible := by
  intro k h0 hk
  simp only [SpanView.fillFrom_get]
  split
  · exact ⟨by simp, (hsrc (from_ + k)).1, (hsrc (from_ + k)).2⟩
  · exact hv k h0 (by simpa using hk)

/-- Carving preserves reconstructibility: a sub-span's bytes are a
subrange of the whole's. One lemma per operation is the whole cost of
keeping an exposure's exit automatic — and this is why `split_off` inside
an exposure does not make the wrapper proof-noisy. -/
theorem SpanView.take_reconstructible {v : SpanView} {n : Int}
    (hv : v.reconstructible) (hn : n ≤ v.len) : (v.take n).reconstructible := by
  intro k h0 hk
  exact hv k h0 (by simp at hk; omega)

theorem SpanView.drop_reconstructible {v : SpanView} {n : Int}
    (hv : v.reconstructible) (h0n : 0 ≤ n) : (v.drop n).reconstructible := by
  intro k h0 hk
  simp only [SpanView.drop_get]
  exact hv (k + n) (by omega) (by simp at hk; omega)

theorem SpanView.cat_reconstructible {v1 v2 : SpanView}
    (h1 : v1.reconstructible) (h2 : v2.reconstructible) :
    (v1.cat v2).reconstructible := by
  intro k h0 hk
  simp only [SpanView.cat_get]
  simp at hk
  split
  · exact h1 k h0 (by omega)
  · exact h2 (k - v1.len) (by omega) (by omega)

/-- Writing a byte value preserves reconstructibility. -/
theorem SpanView.write_reconstructible {v : SpanView} {k w : Int}
    (hv : v.reconstructible) (hlo : 0 ≤ w) (hhi : w ≤ 255) :
    (v.write k (.init w)).reconstructible := by
  intro j h0 hj
  by_cases he : j = k
  · simpa [he] using ⟨hlo, hhi⟩
  · simpa [he] using hv j h0 (by simpa using hj)

end Sable
