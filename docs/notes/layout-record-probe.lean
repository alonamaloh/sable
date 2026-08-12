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

/-! ## The U9 node instance

`Option RawPtr` is an abstract nullable pointer value here. Giving it the
target pointer layout does not give it a byte encoding: in particular, this
probe does not identify `none` with any sequence of bytes or permit a raw byte
load from an occupied node extent.
-/

structure IntrusiveNode where
  previous : Option RawPtr
  next : Option RawPtr
  payload : Int

namespace IntrusiveNode

def rawPointerLayout : Layout := ⟨8, 8⟩
def nullableRawPointerLayout : Layout := rawPointerLayout
def layout : Layout := ⟨24, 8⟩

def previousOffset : Int := 0
def nextOffset : Int := 8
def payloadOffset : Int := 16

theorem rawPointerLayout_wf : rawPointerLayout.wf := by
  refine ⟨by decide, by decide, ⟨3, rfl⟩⟩

theorem nullableRawPointerLayout_wf : nullableRawPointerLayout.wf := by
  exact rawPointerLayout_wf

theorem layout_wf : layout.wf := by
  refine ⟨by decide, by decide, ⟨3, rfl⟩⟩

theorem previous_fits :
    Pair64.fieldFits layout nullableRawPointerLayout previousOffset := by
  simp [Pair64.fieldFits, layout, nullableRawPointerLayout, rawPointerLayout,
    previousOffset]

theorem next_fits :
    Pair64.fieldFits layout nullableRawPointerLayout nextOffset := by
  simp [Pair64.fieldFits, layout, nullableRawPointerLayout, rawPointerLayout,
    nextOffset]

theorem payload_fits :
    Pair64.fieldFits layout u64.layout payloadOffset := by
  simp [Pair64.fieldFits, layout, payloadOffset, Sable.u64.layout]

theorem previous_next_disjoint :
    Pair64.fieldsDisjoint nullableRawPointerLayout previousOffset
      nullableRawPointerLayout nextOffset := by
  simp [Pair64.fieldsDisjoint, nullableRawPointerLayout, rawPointerLayout,
    previousOffset, nextOffset]

theorem previous_payload_disjoint :
    Pair64.fieldsDisjoint nullableRawPointerLayout previousOffset
      u64.layout payloadOffset := by
  simp [Pair64.fieldsDisjoint, nullableRawPointerLayout, rawPointerLayout,
    previousOffset, payloadOffset, Sable.u64.layout]

theorem next_payload_disjoint :
    Pair64.fieldsDisjoint nullableRawPointerLayout nextOffset
      u64.layout payloadOffset := by
  simp [Pair64.fieldsDisjoint, nullableRawPointerLayout, rawPointerLayout,
    nextOffset, payloadOffset, Sable.u64.layout]

end IntrusiveNode

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

def wfIntrusiveNode (v : PointsToView IntrusiveNode) : Prop :=
  v.layout = IntrusiveNode.layout ∧
  0 ≤ v.off ∧ v.off % v.layout.align = 0 ∧
  match v.state with
  | .uninit => True
  | .init node => 0 ≤ node.payload ∧ node.payload ≤ u64.max

def toIntrusiveNode (v : SpanView) : PointsToView IntrusiveNode :=
  { alloc := v.alloc, off := v.off, layout := IntrusiveNode.layout,
    state := .uninit }

def intrusiveNodeToSpan (v : PointsToView IntrusiveNode) : SpanView :=
  { alloc := v.alloc, off := v.off, len := v.layout.size,
    bytes := ⟨v.layout.size, fun _ => .init 0⟩ }

@[simp] theorem toIntrusiveNode_layout (v : SpanView) :
    (toIntrusiveNode v).layout = IntrusiveNode.layout := rfl

@[simp] theorem intrusiveNodeToSpan_len (v : PointsToView IntrusiveNode) :
    (intrusiveNodeToSpan v).len = v.layout.size := rfl

theorem intrusiveNode_init_preserves_layout
    (v : PointsToView IntrusiveNode) (node : IntrusiveNode) :
    (v.put node).layout = v.layout := rfl

theorem intrusiveNode_take_preserves_layout
    (v : PointsToView IntrusiveNode) :
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
