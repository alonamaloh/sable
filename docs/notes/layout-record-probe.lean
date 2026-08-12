/-
U7b record-layout probe (ADR 0032 follow-up).

This deliberately stops at abstract typed storage. `Pair64` has an explicit
layout and checked field offsets, but no byte representation. The probe answers
whether the current generic `PointsToView` and layout laws are already enough
for a POD record before surface syntax and executable type tags are designed.

Run from `lean/`:

  lake env lean ../docs/notes/layout-record-probe.lean
-/

import Sable.Raw
import Sable.Auto

namespace Sable.LayoutRecordProbe

structure Pair64 where
  lo : Int
  hi : Int
  deriving DecidableEq, Repr

namespace Pair64

def layout : Layout := ⟨16, 8⟩
def loOffset : Int := 0
def hiOffset : Int := 8

/-- A field is wholly inside its record and begins at a valid alignment. -/
def fieldFits (outer field : Layout) (off : Int) : Prop :=
  0 ≤ off ∧ off % field.align = 0 ∧ off + field.size ≤ outer.size

/-- Half-open field extents do not overlap. -/
def fieldsDisjoint (a : Layout) (ao : Int) (b : Layout) (bo : Int) : Prop :=
  ao + a.size ≤ bo ∨ bo + b.size ≤ ao

theorem layout_wf : layout.wf := by
  refine ⟨by decide, by decide, ⟨3, rfl⟩⟩

theorem lo_fits : fieldFits layout u64.layout loOffset := by
  simp [fieldFits, layout, loOffset, Sable.u64.layout]

theorem hi_fits : fieldFits layout u64.layout hiOffset := by
  simp [fieldFits, layout, hiOffset, Sable.u64.layout]

theorem fields_disjoint :
    fieldsDisjoint u64.layout loOffset u64.layout hiOffset := by
  simp [fieldsDisjoint, loOffset, hiOffset, Sable.u64.layout]

end Pair64

/-- Candidate pure view invariant for `PointsTo<Pair64>`. The value ranges are
type facts, not representation facts. -/
def wfPair64 (v : PointsToView Pair64) : Prop :=
  v.layout = Pair64.layout ∧
  0 ≤ v.off ∧ v.off % v.layout.align = 0 ∧
  match v.state with
  | .uninit => True
  | .init x =>
      0 ≤ x.lo ∧ x.lo ≤ u64.max ∧ 0 ≤ x.hi ∧ x.hi ≤ u64.max

def toPair64 (v : SpanView) : PointsToView Pair64 :=
  { alloc := v.alloc, off := v.off, layout := Pair64.layout, state := .uninit }

/-- Cleanup back to raw storage writes zeros, but makes no claim that those
zeros encode a `Pair64`. -/
def pair64ToSpan (v : PointsToView Pair64) : SpanView :=
  { alloc := v.alloc, off := v.off, len := v.layout.size,
    bytes := ⟨v.layout.size, fun _ => .init 0⟩ }

@[simp] theorem toPair64_layout (v : SpanView) :
    (toPair64 v).layout = Pair64.layout := rfl

@[simp] theorem pair64ToSpan_len (v : PointsToView Pair64) :
    (pair64ToSpan v).len = v.layout.size := rfl

theorem init_preserves_layout (v : PointsToView Pair64) (x : Pair64) :
    (v.put x).layout = v.layout := rfl

theorem take_preserves_layout (v : PointsToView Pair64) :
    v.clear.layout = v.layout := rfl

example (raw : SpanView)
    (hoff0 : 0 ≤ raw.off)
    (hoff : raw.off % Pair64.layout.align = 0)
    (hlen : raw.len = Pair64.layout.size) :
    wfPair64 (toPair64 raw) ∧ raw.len = Pair64.layout.size := by
  have hoff' : raw.off % 8 = 0 := by
    simpa [Pair64.layout] using hoff
  constructor
  · simp [wfPair64, toPair64, hoff0, hoff', Pair64.layout]
  · exact hlen

example (raw : SpanView) (x : Pair64)
    (hxlo : 0 ≤ x.lo ∧ x.lo ≤ u64.max)
    (hxhi : 0 ≤ x.hi ∧ x.hi ≤ u64.max)
    (hoff0 : 0 ≤ raw.off)
    (hoff : raw.off % Pair64.layout.align = 0) :
    wfPair64 ((toPair64 raw).put x) := by
  have hoff' : raw.off % 8 = 0 := by
    simpa [Pair64.layout] using hoff
  simp [wfPair64, toPair64, PointsToView.put, hoff0, hoff', Pair64.layout]
  exact ⟨hxlo.1, hxlo.2, hxhi.1, hxhi.2⟩

end Sable.LayoutRecordProbe
