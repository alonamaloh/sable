/-
U8d probe — allocator-owned free blocks versus client block leases.

Run from `lean/`:

  lake env lean ../docs/notes/free-block-probe.lean

`FreeBlock` is an internal role. It may split and join while preserving one
allocator identity and offset-derived keys. Converting the allocated prefix
to `BlockLease` removes those structural operations from the client surface.
-/

import Sable
open Sable

set_option linter.unusedVariables false

namespace FreeBlockProbe

structure FreeBlockView where
  allocator : Int
  key : Int
  span : SpanView

def FreeBlockView.wf (v : FreeBlockView) : Prop :=
  v.key = v.span.off ∧ 0 < v.span.len

def takeFree (v : AllocatorView) (key : Int) : FreeBlockView :=
  let lease := v.leaseAt key
  { allocator := lease.allocator, key := lease.key, span := lease.span }

def putFree (v : AllocatorView) (block : FreeBlockView) : AllocatorView :=
  v.put { allocator := block.allocator, key := block.key, span := block.span }

def FreeBlockView.toLease (v : FreeBlockView) : BlockLeaseView :=
  { allocator := v.allocator, key := v.key, span := v.span }

def FreeBlockView.prefix (v : FreeBlockView) (n : Int) : FreeBlockView :=
  { allocator := v.allocator, key := v.key, span := v.span.take n }

def FreeBlockView.suffix (v : FreeBlockView) (n : Int) : FreeBlockView :=
  { allocator := v.allocator, key := v.key + n, span := v.span.drop n }

def FreeBlockView.join (left right : FreeBlockView) : FreeBlockView :=
  { allocator := left.allocator, key := left.key,
    span := left.span.cat right.span }

def FreeBlockView.joinable (left right : FreeBlockView) : Prop :=
  left.allocator = right.allocator ∧
  left.span.alloc = right.span.alloc ∧
  left.span.off + left.span.len = right.span.off ∧
  right.key = left.key + left.span.len

theorem take_putFree {v : AllocatorView} {key : Int}
    (h : v.canTake key) :
    putFree (v.take key) (takeFree v key) = v := by
  simpa [putFree, takeFree,
    FreeBlockView.toLease] using AllocatorView.take_put v key h

theorem prefix_wf {v : FreeBlockView} {n : Int}
    (hv : v.wf) (hn : 0 < n) : (v.prefix n).wf := by
  rcases hv with ⟨hkey, _⟩
  exact ⟨by simpa [FreeBlockView.prefix] using hkey,
    by simpa [FreeBlockView.wf, FreeBlockView.prefix] using hn⟩

theorem suffix_wf {v : FreeBlockView} {n : Int}
    (hv : v.wf) (hn : n < v.span.len) : (v.suffix n).wf := by
  rcases hv with ⟨hkey, _⟩
  constructor
  · simp [FreeBlockView.suffix, hkey]
  · simp [FreeBlockView.suffix]
    omega

theorem split_joinable {v : FreeBlockView} {n : Int} :
    (v.prefix n).joinable (v.suffix n) := by
  simp [FreeBlockView.joinable, FreeBlockView.prefix,
    FreeBlockView.suffix]

theorem split_lengths {v : FreeBlockView} {n : Int} :
    (v.prefix n).span.len + (v.suffix n).span.len = v.span.len := by
  simp [FreeBlockView.prefix, FreeBlockView.suffix]
  omega

theorem split_keys_distinct {v : FreeBlockView} {n : Int} (hn : 0 < n) :
    (v.prefix n).key ≠ (v.suffix n).key := by
  simp [FreeBlockView.prefix, FreeBlockView.suffix]
  omega

theorem split_byte_disjoint {v : FreeBlockView} {n i : Int}
    (hi : (v.prefix n).span.off ≤ i ∧
      i < (v.prefix n).span.off + (v.prefix n).span.len) :
    ¬ ((v.suffix n).span.off ≤ i ∧
      i < (v.suffix n).span.off + (v.suffix n).span.len) := by
  simp [FreeBlockView.prefix, FreeBlockView.suffix] at hi ⊢
  omega

theorem join_split_extent {v : FreeBlockView} {n : Int} :
    let joined := (v.prefix n).join (v.suffix n)
    joined.allocator = v.allocator ∧ joined.key = v.key ∧
    joined.span.sameExtent v.span := by
  simp [FreeBlockView.join, FreeBlockView.prefix, FreeBlockView.suffix,
    SpanView.sameExtent]
  omega

theorem join_split_bytes {v : FreeBlockView} {n k : Int} :
    ((v.prefix n).join (v.suffix n)).span.bytes.get k =
      v.span.bytes.get k := by
  simp [FreeBlockView.join, FreeBlockView.prefix, FreeBlockView.suffix]

theorem lease_preserves_identity (v : FreeBlockView) :
    v.toLease.allocator = v.allocator ∧
    v.toLease.key = v.key ∧
    v.toLease.span = v.span := by
  exact ⟨rfl, rfl, rfl⟩

#check take_putFree
#check prefix_wf
#check suffix_wf
#check split_joinable
#check split_lengths
#check split_keys_distinct
#check split_byte_disjoint
#check join_split_extent
#check join_split_bytes
#check lease_preserves_identity

end FreeBlockProbe
