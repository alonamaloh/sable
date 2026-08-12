/-
U8e probe — an identity-preserving typed header inside a free block.

Run from `lean/`:

  lake env lean ../docs/notes/free-header-probe.lean

This probe deliberately stops before list policy. It asks only whether two
aligned `u64` cells (`size`, `next`) can occupy the front of a `FreeBlock`
while allocator identity, block key, and the remaining payload stay fixed.
Two words are the minimum honest runtime header: the ghost span length erases,
so the allocator must store size as well as its link.
-/

import Sable
open Sable

set_option linter.unusedVariables false

namespace FreeHeaderProbe

def headerBytes : Int := 2 * u64.layout.size

/-- A free block while its first two words have typed metadata roles. The
payload remains raw allocator-internal authority; no component is a lease. -/
structure FreeHeaderView where
  allocator : Int
  key : Int
  sizeCell : PointsToView Int
  nextCell : PointsToView Int
  payload : SpanView

/-- Geometry and typed shape, independent of link ordering or sentinel policy. -/
def FreeHeaderView.wf (v : FreeHeaderView) : Prop :=
  v.sizeCell.wfU64 ∧ v.nextCell.wfU64 ∧
  v.key = v.sizeCell.off ∧
  v.sizeCell.alloc = v.nextCell.alloc ∧
  v.nextCell.alloc = v.payload.alloc ∧
  v.sizeCell.off + v.sizeCell.layout.size = v.nextCell.off ∧
  v.nextCell.off + v.nextCell.layout.size = v.payload.off ∧
  0 ≤ v.payload.len

/-- Give the first two words of an internal free block their header roles. -/
def blockToHeader (v : FreeBlockView) : FreeHeaderView :=
  { allocator := v.allocator
    key := v.key
    sizeCell :=
      { alloc := v.span.alloc, off := v.span.off,
        layout := u64.layout, state := .uninit }
    nextCell :=
      { alloc := v.span.alloc, off := v.span.off + u64.layout.size,
        layout := u64.layout, state := .uninit }
    payload := v.span.drop headerBytes }

def FreeHeaderView.putSize (v : FreeHeaderView) (size : Int) : FreeHeaderView :=
  { v with sizeCell := v.sizeCell.put size }

def FreeHeaderView.putNext (v : FreeHeaderView) (next : Int) : FreeHeaderView :=
  { v with nextCell := v.nextCell.put next }

def FreeHeaderView.clearFields (v : FreeHeaderView) : FreeHeaderView :=
  { v with sizeCell := v.sizeCell.clear, nextCell := v.nextCell.clear }

/-- A cleared typed word returns an uninitialized raw extent. -/
def rawCell (v : PointsToView Int) : SpanView :=
  { alloc := v.alloc
    off := v.off
    len := v.layout.size
    bytes := ⟨v.layout.size, fun _ => .uninit⟩ }

/-- Reassemble both header words and the payload into one internal block. -/
def FreeHeaderView.toFree (v : FreeHeaderView) : FreeBlockView :=
  { allocator := v.allocator
    key := v.key
    span := (rawCell v.sizeCell).cat ((rawCell v.nextCell).cat v.payload) }

theorem blockToHeader_wf {v : FreeBlockView}
    (hv : v.wf)
    (hoff : 0 ≤ v.span.off)
    (halign : v.span.off % u64.layout.align = 0)
    (hlen : headerBytes ≤ v.span.len) : (blockToHeader v).wf := by
  obtain ⟨hkey, _⟩ := hv
  simp [FreeHeaderView.wf, blockToHeader, PointsToView.wfU64,
    headerBytes, u64.layout] at ⊢ hlen halign
  exact ⟨⟨hoff, halign⟩, ⟨by omega, halign⟩, hkey,
    ⟨by omega, hlen⟩⟩

theorem header_cells_disjoint (v : FreeBlockView) {i : Int}
    (hi : (blockToHeader v).sizeCell.off ≤ i ∧
      i < (blockToHeader v).sizeCell.off +
        (blockToHeader v).sizeCell.layout.size) :
    ¬ ((blockToHeader v).nextCell.off ≤ i ∧
      i < (blockToHeader v).nextCell.off +
        (blockToHeader v).nextCell.layout.size) := by
  simp [blockToHeader, u64.layout] at hi ⊢
  omega

theorem header_payload_disjoint (v : FreeBlockView) {i : Int}
    (hi : (blockToHeader v).sizeCell.off ≤ i ∧
      i < (blockToHeader v).nextCell.off +
        (blockToHeader v).nextCell.layout.size) :
    ¬ ((blockToHeader v).payload.off ≤ i ∧
      i < (blockToHeader v).payload.off +
        (blockToHeader v).payload.len) := by
  simp [blockToHeader, headerBytes, u64.layout] at hi ⊢
  omega

theorem putSize_preserves_carrier (v : FreeHeaderView) (size : Int) :
    (v.putSize size).allocator = v.allocator ∧
    (v.putSize size).key = v.key ∧
    (v.putSize size).sizeCell.alloc = v.sizeCell.alloc ∧
    (v.putSize size).sizeCell.off = v.sizeCell.off ∧
    (v.putSize size).nextCell = v.nextCell ∧
    (v.putSize size).payload = v.payload := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem putNext_preserves_carrier (v : FreeHeaderView) (next : Int) :
    (v.putNext next).allocator = v.allocator ∧
    (v.putNext next).key = v.key ∧
    (v.putNext next).nextCell.alloc = v.nextCell.alloc ∧
    (v.putNext next).nextCell.off = v.nextCell.off ∧
    (v.putNext next).sizeCell = v.sizeCell ∧
    (v.putNext next).payload = v.payload := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem initialized_fields (v : FreeBlockView) (next : Int) :
    let header := (blockToHeader v).putSize v.span.len |>.putNext next
    header.sizeCell.state = .init v.span.len ∧
    header.nextCell.state = .init next := by
  simp [FreeHeaderView.putSize, FreeHeaderView.putNext]

theorem putFields_wf {v : FreeHeaderView} {size next : Int}
    (hv : v.wf)
    (hsize : 0 ≤ size ∧ size ≤ u64.max)
    (hnext : 0 ≤ next ∧ next ≤ u64.max) :
    (v.putSize size |>.putNext next).wf := by
  unfold FreeHeaderView.wf at hv ⊢
  obtain ⟨hsizeCell, hnextCell, hrest⟩ := hv
  obtain ⟨hsizeLayout, hsizeOff, hsizeAlign, _⟩ := hsizeCell
  obtain ⟨hnextLayout, hnextOff, hnextAlign, _⟩ := hnextCell
  exact ⟨
    ⟨by simpa [FreeHeaderView.putSize, FreeHeaderView.putNext] using hsizeLayout,
      by simpa [FreeHeaderView.putSize, FreeHeaderView.putNext] using hsizeOff,
      by simpa [FreeHeaderView.putSize, FreeHeaderView.putNext] using hsizeAlign,
      by simpa [FreeHeaderView.putSize, FreeHeaderView.putNext, u64.max] using hsize⟩,
    ⟨by simpa [FreeHeaderView.putSize, FreeHeaderView.putNext] using hnextLayout,
      by simpa [FreeHeaderView.putSize, FreeHeaderView.putNext] using hnextOff,
      by simpa [FreeHeaderView.putSize, FreeHeaderView.putNext] using hnextAlign,
      by simpa [FreeHeaderView.putSize, FreeHeaderView.putNext, u64.max] using hnext⟩,
    by simpa [FreeHeaderView.putSize, FreeHeaderView.putNext] using hrest⟩

theorem clearFields_preserves_carrier (v : FreeHeaderView) :
    v.clearFields.allocator = v.allocator ∧
    v.clearFields.key = v.key ∧
    v.clearFields.sizeCell.alloc = v.sizeCell.alloc ∧
    v.clearFields.sizeCell.off = v.sizeCell.off ∧
    v.clearFields.nextCell.alloc = v.nextCell.alloc ∧
    v.clearFields.nextCell.off = v.nextCell.off ∧
    v.clearFields.payload = v.payload := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem clearFields_wf {v : FreeHeaderView} (hv : v.wf) :
    v.clearFields.wf := by
  unfold FreeHeaderView.wf at hv ⊢
  obtain ⟨hsizeCell, hnextCell, hrest⟩ := hv
  obtain ⟨hsizeLayout, hsizeOff, hsizeAlign, _⟩ := hsizeCell
  obtain ⟨hnextLayout, hnextOff, hnextAlign, _⟩ := hnextCell
  exact ⟨
    ⟨by simpa [FreeHeaderView.clearFields] using hsizeLayout,
      by simpa [FreeHeaderView.clearFields] using hsizeOff,
      by simpa [FreeHeaderView.clearFields] using hsizeAlign,
      by simp [FreeHeaderView.clearFields, PointsToView.clear]⟩,
    ⟨by simpa [FreeHeaderView.clearFields] using hnextLayout,
      by simpa [FreeHeaderView.clearFields] using hnextOff,
      by simpa [FreeHeaderView.clearFields] using hnextAlign,
      by simp [FreeHeaderView.clearFields, PointsToView.clear]⟩,
    by simpa [FreeHeaderView.clearFields] using hrest⟩

theorem typed_roundTrip_identity (v : FreeBlockView) (next : Int) :
    let header := (blockToHeader v).putSize v.span.len |>.putNext next
    let returned := header.clearFields.toFree
    returned.allocator = v.allocator ∧ returned.key = v.key ∧
    returned.span.sameExtent v.span := by
  simp [blockToHeader, FreeHeaderView.putSize, FreeHeaderView.putNext,
    FreeHeaderView.clearFields, FreeHeaderView.toFree, rawCell,
    SpanView.sameExtent, headerBytes, u64.layout]
  omega

theorem typed_roundTrip_payload (v : FreeBlockView) (next : Int) :
    let header := (blockToHeader v).putSize v.span.len |>.putNext next
    header.clearFields.payload = v.span.drop headerBytes := by
  rfl

theorem typed_roundTrip_wf {v : FreeBlockView} (next : Int)
    (hv : v.wf) (hlen : headerBytes ≤ v.span.len) :
    let header := (blockToHeader v).putSize v.span.len |>.putNext next
    header.clearFields.toFree.wf := by
  obtain ⟨hkey, hpos⟩ := hv
  simp [blockToHeader, FreeHeaderView.putSize, FreeHeaderView.putNext,
    FreeHeaderView.clearFields, FreeHeaderView.toFree, rawCell,
    FreeBlockView.wf, headerBytes, u64.layout] at ⊢ hlen
  exact ⟨hkey, by omega⟩

#check blockToHeader_wf
#check header_cells_disjoint
#check header_payload_disjoint
#check putSize_preserves_carrier
#check putNext_preserves_carrier
#check initialized_fields
#check putFields_wf
#check clearFields_preserves_carrier
#check clearFields_wf
#check typed_roundTrip_identity
#check typed_roundTrip_payload
#check typed_roundTrip_wf

end FreeHeaderProbe
