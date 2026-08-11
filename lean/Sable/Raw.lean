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

end Sable
