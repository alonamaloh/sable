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
import Sable.Layout

namespace Sable

/-- Pure identity and geometry carried by the unique right to release a
system allocation. The authority itself remains checker-only. -/
structure SystemDeallocView where
  alloc : Int
  len : Int

def SystemDeallocView.wf (v : SystemDeallocView) : Prop := 0 < v.len

/-- Raw storage is not a byte sequence: uninitialized is a distinct
state, and it must stay distinguishable from every inhabitant of a value
type. An initialized `option<u8>` holding `none` is not uninitialized
memory. -/
inductive ByteState where
  | uninit : ByteState
  | init : Int → ByteState
  deriving DecidableEq, Repr

/-- Initialization state of an abstract typed extent. This is not
`Option α`: an initialized `Option β` holding `none` must remain distinct
from storage that contains no value (ADR 0031). -/
inductive CellState (α : Type) where
  | uninit : CellState α
  | init : α → CellState α
  deriving DecidableEq, Repr

/-- Pure view of one typed extent. Size and alignment come from the
layout capability; the first slice fixes both to eight for `u64`. -/
structure PointsToView (α : Type) where
  alloc : Int
  off : Int
  layout : Layout
  state : CellState α

/-- Shape facts carried by every `PointsTo<u64>` binding. -/
def PointsToView.wfU64 (v : PointsToView Int) : Prop :=
  v.layout = u64.layout ∧ 0 ≤ v.off ∧ v.off % v.layout.align = 0 ∧
    match v.state with
    | .uninit => True
    | .init x => 0 ≤ x ∧ x ≤ 18446744073709551615

@[simp] theorem PointsToView.wfU64_iff (v : PointsToView Int) :
    v.wfU64 ↔ (v.layout = u64.layout ∧ 0 ≤ v.off ∧ v.off % v.layout.align = 0 ∧
      match v.state with
      | .uninit => True
      | .init x => 0 ≤ x ∧ x ≤ 18446744073709551615) := Iff.rfl

/-- Put a value into an uninitialized typed extent. -/
def PointsToView.put (v : PointsToView α) (x : α) : PointsToView α :=
  { v with state := .init x }

/-- Remove or destroy the value while retaining typed authority. -/
def PointsToView.clear (v : PointsToView α) : PointsToView α :=
  { v with state := .uninit }

@[simp] theorem PointsToView.put_alloc (v : PointsToView α) (x : α) :
    (v.put x).alloc = v.alloc := rfl
@[simp] theorem PointsToView.put_off (v : PointsToView α) (x : α) :
    (v.put x).off = v.off := rfl
@[simp] theorem PointsToView.put_layout (v : PointsToView α) (x : α) :
    (v.put x).layout = v.layout := rfl
@[simp] theorem PointsToView.put_state (v : PointsToView α) (x : α) :
    (v.put x).state = .init x := rfl
@[simp] theorem PointsToView.clear_alloc (v : PointsToView α) :
    v.clear.alloc = v.alloc := rfl
@[simp] theorem PointsToView.clear_off (v : PointsToView α) :
    v.clear.off = v.off := rfl
@[simp] theorem PointsToView.clear_layout (v : PointsToView α) :
    v.clear.layout = v.layout := rfl
@[simp] theorem PointsToView.clear_state (v : PointsToView α) :
    v.clear.state = .uninit := rfl

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

def SpanView.sameExtent (a b : SpanView) : Prop :=
  a.alloc = b.alloc ∧ a.off = b.off ∧ a.len = b.len

/-! Allocator aggregates and client leases (ADR 0037). The structures below
are pure views. Affine authority and the hidden valid-composition invariant
remain checker facts; only sealed compiler operations establish these view
transitions. -/

/-- A client block's byte authority and return identity are one resource. -/
structure BlockLeaseView where
  allocator : Int
  key : Int
  span : SpanView

/-- The same lease while its exact extent has a typed `u64` role. -/
structure LeasedPointsToU64View where
  allocator : Int
  key : Int
  cell : PointsToView Int

/-- Allocator-internal block authority. Only this role may split/join. -/
structure FreeBlockView where
  allocator : Int
  key : Int
  span : SpanView

/-- A free block whose first two words carry runtime size and next-link
metadata. The allocator identity and whole-block key remain alongside the
typed cells and raw payload (ADR 0041). -/
structure FreeHeaderView where
  allocator : Int
  key : Int
  sizeCell : PointsToView Int
  nextCell : PointsToView Int
  payload : SpanView

def freeHeaderBytes : Int := 2 * u64.layout.size

def FreeHeaderView.wf (v : FreeHeaderView) : Prop :=
  v.sizeCell.wfU64 ∧ v.nextCell.wfU64 ∧
  v.key = v.sizeCell.off ∧
  v.sizeCell.alloc = v.nextCell.alloc ∧
  v.nextCell.alloc = v.payload.alloc ∧
  v.sizeCell.off + v.sizeCell.layout.size = v.nextCell.off ∧
  v.nextCell.off + v.nextCell.layout.size = v.payload.off ∧
  0 ≤ v.payload.len

def FreeHeaderView.putFields
    (v : FreeHeaderView) (size next : Int) : FreeHeaderView :=
  { v with sizeCell := v.sizeCell.put size, nextCell := v.nextCell.put next }

def FreeHeaderView.clearFields (v : FreeHeaderView) : FreeHeaderView :=
  { v with sizeCell := v.sizeCell.clear, nextCell := v.nextCell.clear }

def FreeBlockView.wf (v : FreeBlockView) : Prop :=
  v.key = v.span.off ∧ 0 < v.span.len

def FreeBlockView.toLease (v : FreeBlockView) : BlockLeaseView :=
  { allocator := v.allocator, key := v.key, span := v.span }

def BlockLeaseView.toFree (v : BlockLeaseView) : FreeBlockView :=
  { allocator := v.allocator, key := v.key, span := v.span }

def BlockLeaseView.toCellU64 (v : BlockLeaseView) : LeasedPointsToU64View :=
  { allocator := v.allocator, key := v.key,
    cell := { alloc := v.span.alloc, off := v.span.off,
              layout := u64.layout, state := .uninit } }

def LeasedPointsToU64View.toLease (v : LeasedPointsToU64View) : BlockLeaseView :=
  { allocator := v.allocator, key := v.key,
    span := { alloc := v.cell.alloc, off := v.cell.off,
              len := v.cell.layout.size,
              bytes := ⟨v.cell.layout.size, fun _ => .uninit⟩ } }

def LeasedPointsToU64View.put
    (v : LeasedPointsToU64View) (x : Int) : LeasedPointsToU64View :=
  { v with cell := v.cell.put x }

def LeasedPointsToU64View.clear
    (v : LeasedPointsToU64View) : LeasedPointsToU64View :=
  { v with cell := v.cell.clear }

@[simp] theorem BlockLeaseView.toCellU64_allocator (v : BlockLeaseView) :
    v.toCellU64.allocator = v.allocator := rfl
@[simp] theorem BlockLeaseView.toCellU64_key (v : BlockLeaseView) :
    v.toCellU64.key = v.key := rfl
@[simp] theorem BlockLeaseView.toCellU64_cell (v : BlockLeaseView) :
    v.toCellU64.cell =
      { alloc := v.span.alloc, off := v.span.off,
        layout := u64.layout, state := .uninit } := rfl
@[simp] theorem LeasedPointsToU64View.toLease_allocator
    (v : LeasedPointsToU64View) : v.toLease.allocator = v.allocator := rfl
@[simp] theorem LeasedPointsToU64View.toLease_key
    (v : LeasedPointsToU64View) : v.toLease.key = v.key := rfl
@[simp] theorem LeasedPointsToU64View.put_allocator
    (v : LeasedPointsToU64View) (x : Int) : (v.put x).allocator = v.allocator := rfl
@[simp] theorem LeasedPointsToU64View.put_key
    (v : LeasedPointsToU64View) (x : Int) : (v.put x).key = v.key := rfl
@[simp] theorem LeasedPointsToU64View.put_cell
    (v : LeasedPointsToU64View) (x : Int) : (v.put x).cell = v.cell.put x := rfl
@[simp] theorem LeasedPointsToU64View.clear_allocator
    (v : LeasedPointsToU64View) : v.clear.allocator = v.allocator := rfl
@[simp] theorem LeasedPointsToU64View.clear_key
    (v : LeasedPointsToU64View) : v.clear.key = v.key := rfl
@[simp] theorem LeasedPointsToU64View.clear_cell
    (v : LeasedPointsToU64View) : v.clear.cell = v.cell.clear := rfl

/-- Pure view of one allocator aggregate. The first slice uses key zero for
the complete root; later allocator-owned block roles refine this map. -/
structure AllocatorView where
  allocator : Int
  root : SpanView
  free : Int → Option SpanView

def AllocatorView.initial (allocator : Int) (root : SpanView) : AllocatorView :=
  { allocator, root, free := fun key => if key = 0 then some root else none }

def AllocatorView.canTake (v : AllocatorView) (key : Int) : Prop :=
  v.free key ≠ none

def AllocatorView.leaseAt (v : AllocatorView) (key : Int) : BlockLeaseView :=
  { allocator := v.allocator, key, span := (v.free key).getD v.root }

def AllocatorView.take (v : AllocatorView) (key : Int) : AllocatorView :=
  { v with free := fun k => if k = key then none else v.free k }

def AllocatorView.canPut (v : AllocatorView) (lease : BlockLeaseView) : Prop :=
  lease.allocator = v.allocator ∧ v.free lease.key = none

@[simp] theorem AllocatorView.canPut_typedRoundTrip
    (v : AllocatorView) (lease : BlockLeaseView) (x : Int) :
    v.canPut (((lease.toCellU64.put x).clear).toLease) ↔ v.canPut lease := by
  rfl

def AllocatorView.put (v : AllocatorView) (lease : BlockLeaseView) : AllocatorView :=
  { v with free := fun k => if k = lease.key then some lease.span else v.free k }

def AllocatorView.takeFree (v : AllocatorView) (key : Int) : FreeBlockView :=
  (v.leaseAt key).toFree

def AllocatorView.canTakeFree (v : AllocatorView) (key : Int) : Prop :=
  v.canTake key ∧ (v.takeFree key).wf

def AllocatorView.canPutFree (v : AllocatorView) (block : FreeBlockView) : Prop :=
  block.allocator = v.allocator ∧ block.wf

def AllocatorView.putFree (v : AllocatorView) (block : FreeBlockView) : AllocatorView :=
  v.put block.toLease

@[simp] theorem AllocatorView.takeFree_toLease
    (v : AllocatorView) (key : Int) :
    (v.takeFree key).toLease = v.leaseAt key := rfl

@[simp] theorem AllocatorView.initial_takeFree_zero_span
    (allocator : Int) (root : SpanView) :
    ((AllocatorView.initial allocator root).takeFree 0).span = root := rfl

@[simp] theorem AllocatorView.initial_takeFree_zero_key
    (allocator : Int) (root : SpanView) :
    ((AllocatorView.initial allocator root).takeFree 0).key = 0 := rfl

@[simp] theorem AllocatorView.initial_takeFree_zero_allocator
    (allocator : Int) (root : SpanView) :
    ((AllocatorView.initial allocator root).takeFree 0).allocator = allocator := rfl

@[simp] theorem AllocatorView.initial_canTakeFree_zero
    (allocator : Int) (root : SpanView)
    (hoff : root.off = 0) (hlen : 0 < root.len) :
    (AllocatorView.initial allocator root).canTakeFree 0 := by
  simp [AllocatorView.canTakeFree, AllocatorView.canTake,
    AllocatorView.initial, AllocatorView.takeFree, AllocatorView.leaseAt,
    BlockLeaseView.toFree, FreeBlockView.wf, hoff, hlen]

@[simp] theorem FreeBlockView.toLease_toFree (v : FreeBlockView) :
    v.toLease.toFree = v := rfl

@[simp] theorem BlockLeaseView.toFree_toLease (v : BlockLeaseView) :
    v.toFree.toLease = v := rfl

def AllocatorView.releaseSpan (v : AllocatorView) : SpanView :=
  (v.free 0).getD v.root

def AllocatorView.complete (v : AllocatorView) : Prop :=
  v.free 0 ≠ none ∧ v.releaseSpan.sameExtent v.root ∧
    ∀ k, k ≠ 0 → v.free k = none

def AllocatorView.wf (v : AllocatorView) : Prop :=
  (0 ≤ v.root.len ∧ v.root.len ≤ v.root.bytes.len) ∧
    ∀ k span, v.free k = some span →
      0 ≤ span.len ∧ span.len ≤ span.bytes.len

@[simp] theorem AllocatorView.initial_complete (allocator : Int) (root : SpanView) :
    (AllocatorView.initial allocator root).complete := by
  simp [AllocatorView.complete, AllocatorView.releaseSpan,
    SpanView.sameExtent, AllocatorView.initial]

@[simp] theorem AllocatorView.initial_canTake_zero (allocator : Int)
    (root : SpanView) :
    (AllocatorView.initial allocator root).canTake 0 := by
  simp [AllocatorView.canTake, AllocatorView.initial]

@[simp] theorem AllocatorView.initial_root (allocator : Int) (root : SpanView) :
    (AllocatorView.initial allocator root).root = root := rfl

@[simp] theorem AllocatorView.initial_releaseSpan
    (allocator : Int) (root : SpanView) :
    (AllocatorView.initial allocator root).releaseSpan = root := rfl

@[simp] theorem AllocatorView.initial_leaseAt_zero_span
    (allocator : Int) (root : SpanView) :
    ((AllocatorView.initial allocator root).leaseAt 0).span = root := rfl

@[simp] theorem AllocatorView.take_root (v : AllocatorView) (key : Int) :
    (v.take key).root = v.root := rfl

@[simp] theorem AllocatorView.put_root (v : AllocatorView)
    (lease : BlockLeaseView) : (v.put lease).root = v.root := rfl

@[simp] theorem AllocatorView.take_canPut (v : AllocatorView) (key : Int) :
    (v.take key).canPut (v.leaseAt key) := by
  constructor
  · rfl
  · simp [AllocatorView.take, AllocatorView.leaseAt]

@[simp] theorem AllocatorView.initial_wf (allocator : Int) (root : SpanView)
    (hroot : 0 ≤ root.len ∧ root.len ≤ root.bytes.len) :
    (AllocatorView.initial allocator root).wf := by
  constructor
  · exact hroot
  · intro k span hentry
    by_cases hk : k = 0
    · subst k
      simp [AllocatorView.initial] at hentry
      simpa [hentry] using hroot
    · simp [AllocatorView.initial, hk] at hentry

@[simp] theorem AllocatorView.take_put (v : AllocatorView) (key : Int)
    (h : v.canTake key) :
    (v.take key).put (v.leaseAt key) = v := by
  cases v with
  | mk allocator root free =>
      simp only [AllocatorView.put, AllocatorView.take]
      congr 1
      funext k
      by_cases hk : k = key
      · subst k
        simp only [if_pos]
        simp [AllocatorView.leaseAt]
        cases heq : free key with
        | none => exact (h heq).elim
        | some span => rfl
      · simp [AllocatorView.leaseAt, hk]

@[simp] theorem AllocatorView.take_put_complete (v : AllocatorView) (key : Int)
    (h : v.canTake key) :
    ((v.take key).put (v.leaseAt key)).complete ↔ v.complete := by
  rw [AllocatorView.take_put v key h]

@[simp] theorem AllocatorView.initial_typedRoundTrip_complete
    (allocator : Int) (root : SpanView) (x : Int)
    (hlen : root.len = u64.layout.size) :
    let v := AllocatorView.initial allocator root
    ((v.take 0).put (((v.leaseAt 0).toCellU64.put x).clear.toLease)).complete := by
  simp [AllocatorView.complete, AllocatorView.releaseSpan,
    SpanView.sameExtent, AllocatorView.initial, AllocatorView.take,
    AllocatorView.put, AllocatorView.leaseAt, BlockLeaseView.toCellU64,
    LeasedPointsToU64View.put, LeasedPointsToU64View.clear,
    LeasedPointsToU64View.toLease, hlen]
  intro k hk
  simp [hk]

theorem AllocatorView.complete_releaseSpan_extent (v : AllocatorView)
    (h : v.complete) : v.releaseSpan.sameExtent v.root := h.2.1

/-- A fresh raw root: every byte exists but has no value yet. -/
def SpanView.uninit (alloc len : Int) : SpanView :=
  { alloc, off := 0, len, bytes := ⟨len, fun _ => .uninit⟩ }

@[simp] theorem SpanView.uninit_alloc (alloc len : Int) :
    (SpanView.uninit alloc len).alloc = alloc := rfl
@[simp] theorem SpanView.uninit_off (alloc len : Int) :
    (SpanView.uninit alloc len).off = 0 := rfl
@[simp] theorem SpanView.uninit_len (alloc len : Int) :
    (SpanView.uninit alloc len).len = len := rfl
@[simp] theorem SpanView.uninit_get (alloc len k : Int) :
    (SpanView.uninit alloc len).bytes.get k = .uninit := rfl

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

/-! Allocator-internal block geometry (ADR 0039). -/

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

def FreeBlockView.toHeader (v : FreeBlockView) : FreeHeaderView :=
  { allocator := v.allocator
    key := v.key
    sizeCell :=
      { alloc := v.span.alloc, off := v.span.off,
        layout := u64.layout, state := .uninit }
    nextCell :=
      { alloc := v.span.alloc, off := v.span.off + u64.layout.size,
        layout := u64.layout, state := .uninit }
    payload := v.span.drop freeHeaderBytes }

def FreeHeaderView.rawCell (v : PointsToView Int) : SpanView :=
  { alloc := v.alloc, off := v.off, len := v.layout.size,
    bytes := ⟨v.layout.size, fun _ => .init 0⟩ }

def FreeHeaderView.toFree (v : FreeHeaderView) : FreeBlockView :=
  { allocator := v.allocator
    key := v.key
    span := (rawCell v.sizeCell).cat ((rawCell v.nextCell).cat v.payload) }

@[simp] theorem FreeBlockView.split_joinable (v : FreeBlockView) (n : Int) :
    (v.prefix n).joinable (v.suffix n) := by
  simp [FreeBlockView.joinable, FreeBlockView.prefix, FreeBlockView.suffix]

theorem FreeBlockView.join_wf {left right : FreeBlockView}
    (hleft : left.wf) (hright : right.wf)
    (_hjoin : left.joinable right) : (left.join right).wf := by
  obtain ⟨hleftKey, hleftLen⟩ := hleft
  obtain ⟨_, hrightLen⟩ := hright
  exact ⟨by simpa [FreeBlockView.join, FreeBlockView.wf] using hleftKey,
    by simp [FreeBlockView.join]; omega⟩

theorem FreeBlockView.toHeader_wf {v : FreeBlockView}
    (hv : v.wf)
    (hoff : 0 ≤ v.span.off)
    (halign : v.span.off % u64.layout.align = 0)
    (hlen : freeHeaderBytes ≤ v.span.len) : v.toHeader.wf := by
  obtain ⟨hkey, _⟩ := hv
  simp [FreeHeaderView.wf, FreeBlockView.toHeader, PointsToView.wfU64,
    freeHeaderBytes, u64.layout] at ⊢ hlen halign
  exact ⟨⟨hoff, halign⟩, ⟨by omega, halign⟩, hkey,
    ⟨by omega, hlen⟩⟩

theorem FreeHeaderView.putFields_wf {v : FreeHeaderView} {size next : Int}
    (hv : v.wf)
    (hsize : 0 ≤ size ∧ size ≤ 18446744073709551615)
    (hnext : 0 ≤ next ∧ next ≤ 18446744073709551615) :
    (v.putFields size next).wf := by
  unfold FreeHeaderView.wf at hv ⊢
  obtain ⟨hsizeCell, hnextCell, hrest⟩ := hv
  obtain ⟨hsizeLayout, hsizeOff, hsizeAlign, _⟩ := hsizeCell
  obtain ⟨hnextLayout, hnextOff, hnextAlign, _⟩ := hnextCell
  exact ⟨
    ⟨by simpa [FreeHeaderView.putFields] using hsizeLayout,
      by simpa [FreeHeaderView.putFields] using hsizeOff,
      by simpa [FreeHeaderView.putFields] using hsizeAlign,
      by simpa [FreeHeaderView.putFields] using hsize⟩,
    ⟨by simpa [FreeHeaderView.putFields] using hnextLayout,
      by simpa [FreeHeaderView.putFields] using hnextOff,
      by simpa [FreeHeaderView.putFields] using hnextAlign,
      by simpa [FreeHeaderView.putFields] using hnext⟩,
    by simpa [FreeHeaderView.putFields] using hrest⟩

theorem FreeHeaderView.clearFields_wf {v : FreeHeaderView} (hv : v.wf) :
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

theorem FreeHeaderView.toFree_wf {v : FreeHeaderView} (hv : v.wf) :
    v.toFree.wf := by
  obtain ⟨hsize, hnext, hkey, _, _, _, _, hpayload⟩ := hv
  obtain ⟨hsizeLayout, _, _, _⟩ := hsize
  obtain ⟨hnextLayout, _, _, _⟩ := hnext
  constructor
  · simpa [FreeHeaderView.toFree, FreeHeaderView.rawCell,
      FreeBlockView.wf] using hkey
  · simp [FreeHeaderView.toFree, FreeHeaderView.rawCell,
      hsizeLayout, hnextLayout, u64.layout]
    omega

theorem FreeHeaderView.roundTrip_identity (v : FreeBlockView)
    (size next : Int) :
    let returned := (v.toHeader.putFields size next).clearFields.toFree
    returned.allocator = v.allocator ∧ returned.key = v.key ∧
    returned.span.sameExtent v.span := by
  simp [FreeBlockView.toHeader, FreeHeaderView.putFields,
    FreeHeaderView.clearFields, FreeHeaderView.toFree,
    FreeHeaderView.rawCell, SpanView.sameExtent, freeHeaderBytes, u64.layout]
  omega

theorem FreeHeaderView.roundTrip_wf {v : FreeBlockView}
    (size next : Int) (hv : v.wf) (hlen : freeHeaderBytes ≤ v.span.len) :
    (v.toHeader.putFields size next).clearFields.toFree.wf := by
  obtain ⟨hkey, hpos⟩ := hv
  simp [FreeBlockView.toHeader, FreeHeaderView.putFields,
    FreeHeaderView.clearFields, FreeHeaderView.toFree,
    FreeHeaderView.rawCell, FreeBlockView.wf, freeHeaderBytes, u64.layout]
    at ⊢ hlen
  exact ⟨hkey, by omega⟩

theorem AllocatorView.initialHeaderRoundTrip_complete
    (allocator : Int) (root : SpanView) (size next : Int) :
    let initial := AllocatorView.initial allocator root
    let block := initial.takeFree 0
    let returned := (block.toHeader.putFields size next).clearFields.toFree
    ((initial.take 0).putFree returned).complete := by
  simp [AllocatorView.complete, AllocatorView.releaseSpan,
    SpanView.sameExtent, AllocatorView.initial, AllocatorView.takeFree,
    AllocatorView.leaseAt, AllocatorView.take, AllocatorView.putFree,
    AllocatorView.put, FreeBlockView.toHeader, FreeHeaderView.putFields,
    FreeHeaderView.clearFields, FreeHeaderView.toFree,
    FreeHeaderView.rawCell, FreeBlockView.toLease, BlockLeaseView.toFree,
    freeHeaderBytes, u64.layout]
  constructor
  · omega
  · intro k hk
    simp [hk]

@[simp] theorem FreeBlockView.join_prefix_suffix_extent
    (v : FreeBlockView) (n : Int) :
    ((v.prefix n).join (v.suffix n)).span.sameExtent v.span := by
  simp [FreeBlockView.join, FreeBlockView.prefix, FreeBlockView.suffix,
    SpanView.sameExtent]
  omega

theorem FreeBlockView.prefix_wf {v : FreeBlockView} {n : Int}
    (hv : v.wf) (hn : 0 < n) : (v.prefix n).wf := by
  rcases hv with ⟨hkey, _⟩
  exact ⟨by simpa [FreeBlockView.prefix] using hkey,
    by simpa [FreeBlockView.wf, FreeBlockView.prefix] using hn⟩

theorem FreeBlockView.suffix_wf {v : FreeBlockView} {n : Int}
    (hv : v.wf) (hn : n < v.span.len) : (v.suffix n).wf := by
  rcases hv with ⟨hkey, _⟩
  constructor
  · simp [FreeBlockView.suffix, hkey]
  · simp [FreeBlockView.suffix]
    omega

@[simp] theorem AllocatorView.take_suffix_canPutFree
    {v : AllocatorView} {key n : Int}
    (htake : v.canTakeFree key) (hn : 0 < n ∧ n < (v.takeFree key).span.len) :
    (v.take key).canPutFree ((v.takeFree key).suffix n) := by
  constructor
  · rfl
  · exact FreeBlockView.suffix_wf htake.2 hn.2

@[simp] theorem AllocatorView.putFree_canTake
    (v : AllocatorView) (block : FreeBlockView) :
    (v.putFree block).canTake block.key := by
  simp [AllocatorView.putFree, AllocatorView.put,
    AllocatorView.canTake, FreeBlockView.toLease]

@[simp] theorem AllocatorView.putFree_takeFree
    (v : AllocatorView) (block : FreeBlockView)
    (howner : block.allocator = v.allocator) :
    (v.putFree block).takeFree block.key = block := by
  cases block
  simp [AllocatorView.putFree, AllocatorView.put, AllocatorView.takeFree,
    AllocatorView.leaseAt, FreeBlockView.toLease, BlockLeaseView.toFree] at howner ⊢
  exact howner.symm

@[simp] theorem AllocatorView.putFree_canTakeFree
    (v : AllocatorView) (block : FreeBlockView)
    (hput : v.canPutFree block) :
    (v.putFree block).canTakeFree block.key := by
  constructor
  · exact v.putFree_canTake block
  · rw [AllocatorView.putFree_takeFree v block hput.1]
    exact hput.2

/-- The first vertical FreeBlock subject as one algebraic normalization:
take the root, split it, round-trip the prefix through the client role, park
and retake the suffix, join, and reinsert the root. -/
theorem AllocatorView.splitLeaseRejoin_complete
    (allocator : Int) (root : SpanView) (n : Int)
    (hoff : root.off = 0) :
    let initial := AllocatorView.initial allocator root
    let whole := initial.takeFree 0
    let left := whole.prefix n
    let right := whole.suffix n
    let parked := (initial.take 0).putFree right
    let residual := parked.take right.key
    let joined := left.toLease.toFree.join (parked.takeFree right.key)
    (residual.putFree joined).complete := by
  simp [AllocatorView.complete, AllocatorView.releaseSpan,
    SpanView.sameExtent, AllocatorView.initial, AllocatorView.takeFree,
    AllocatorView.leaseAt, AllocatorView.take, AllocatorView.putFree,
    AllocatorView.put, FreeBlockView.prefix, FreeBlockView.suffix,
    FreeBlockView.join, FreeBlockView.toLease, BlockLeaseView.toFree, hoff]
  constructor
  · omega
  · intro k hk
    simp [hk]

/-- The same split/rejoin normalization when the client temporarily gives
the prefix a typed `u64` role. Cleanup restores an uninitialized extent;
allocator completeness depends only on the exact extent and key. -/
theorem AllocatorView.splitTypedLeaseRejoin_complete
    (allocator : Int) (root : SpanView) (n x : Int)
    (hoff : root.off = 0) (hn : n = u64.layout.size) :
    let initial := AllocatorView.initial allocator root
    let whole := initial.takeFree 0
    let left := whole.prefix n
    let right := whole.suffix n
    let parked := (initial.take 0).putFree right
    let residual := parked.take right.key
    let returned := ((left.toLease.toCellU64.put x).clear).toLease.toFree
    let joined := returned.join (parked.takeFree right.key)
    (residual.putFree joined).complete := by
  simp [AllocatorView.complete, AllocatorView.releaseSpan,
    SpanView.sameExtent, AllocatorView.initial, AllocatorView.takeFree,
    AllocatorView.leaseAt, AllocatorView.take, AllocatorView.putFree,
    AllocatorView.put, FreeBlockView.prefix, FreeBlockView.suffix,
    FreeBlockView.join, FreeBlockView.toLease, BlockLeaseView.toFree,
    BlockLeaseView.toCellU64, LeasedPointsToU64View.put,
    LeasedPointsToU64View.clear, LeasedPointsToU64View.toLease, hoff, hn]
  constructor
  · omega
  · intro k hk
    simp [hk]

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

/-- A pointer names this typed extent. -/
def PointsToView.names (v : PointsToView α) (p : RawPtr) : Prop :=
  p.alloc = v.alloc ∧ p.off = v.off

@[simp] theorem PointsToView.names_iff (v : PointsToView α) (p : RawPtr) :
    v.names p ↔ (p.alloc = v.alloc ∧ p.off = v.off) := Iff.rfl

/-- Reinterpret one checked raw extent as an uninitialized `u64` cell. -/
def SpanView.toCellU64 (v : SpanView) : PointsToView Int :=
  { alloc := v.alloc, off := v.off, layout := u64.layout, state := .uninit }

/-- Return an uninitialized typed cell to eight initialized zero bytes.
This is explicit cleanup; no typed value is serialized by the operation. -/
def PointsToView.toSpanU64 (v : PointsToView Int) : SpanView :=
  { alloc := v.alloc, off := v.off, len := v.layout.size,
    bytes := ⟨v.layout.size, fun _ => .init 0⟩ }

@[simp] theorem SpanView.toCellU64_alloc (v : SpanView) :
    v.toCellU64.alloc = v.alloc := rfl
@[simp] theorem SpanView.toCellU64_off (v : SpanView) :
    v.toCellU64.off = v.off := rfl
@[simp] theorem SpanView.toCellU64_layout (v : SpanView) :
    v.toCellU64.layout = u64.layout := rfl
@[simp] theorem SpanView.toCellU64_state (v : SpanView) :
    v.toCellU64.state = .uninit := rfl
@[simp] theorem PointsToView.toSpanU64_alloc (v : PointsToView Int) :
    v.toSpanU64.alloc = v.alloc := rfl
@[simp] theorem PointsToView.toSpanU64_off (v : PointsToView Int) :
    v.toSpanU64.off = v.off := rfl
@[simp] theorem PointsToView.toSpanU64_len (v : PointsToView Int) :
    v.toSpanU64.len = v.layout.size := rfl
@[simp] theorem PointsToView.toSpanU64_get (v : PointsToView Int) (k : Int) :
    v.toSpanU64.bytes.get k = .init 0 := rfl

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
