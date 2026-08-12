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

/-! ## Generic aggregate authority views

`ResourceMapView` is deliberately only a pure partial map. The affine
checker token owns all entries, and the hidden valid-composition
interpretation proves that taking one entry preserves separation from the
residual map (ADR 0053). Generated VCs therefore mention membership and
well-formedness, never a user-facing heap or separating conjunction.
-/

structure ResourceMapView (K : Type) (V : Type) where
  entries : K → Option V

namespace ResourceMapView

variable {K V : Type} [DecidableEq K]

def empty : ResourceMapView K V :=
  ⟨fun _ => none⟩

def erase (m : ResourceMapView K V) (key : K) : ResourceMapView K V :=
  ⟨fun other => if other = key then none else m.entries other⟩

def insert (m : ResourceMapView K V) (key : K) (value : V) :
    ResourceMapView K V :=
  ⟨fun other => if other = key then some value else m.entries other⟩

omit [DecidableEq K] in
@[simp] theorem empty_entries (key : K) :
    (empty : ResourceMapView K V).entries key = none := rfl

@[simp] theorem erase_eq (m : ResourceMapView K V) (key : K) :
    (m.erase key).entries key = none := by
  simp [erase]

@[simp] theorem erase_ne (m : ResourceMapView K V) {key other : K}
    (hne : other ≠ key) :
    (m.erase key).entries other = m.entries other := by
  simp [erase, hne]

@[simp] theorem insert_eq (m : ResourceMapView K V) (key : K) (value : V) :
    (m.insert key value).entries key = some value := by
  simp [insert]

@[simp] theorem insert_ne (m : ResourceMapView K V) {key other : K}
    (value : V) (hne : other ≠ key) :
    (m.insert key value).entries other = m.entries other := by
  simp [insert, hne]

/-- Taking and returning the same entry restores the exact map view. -/
theorem erase_insert_roundTrip
    {m : ResourceMapView K V} {key : K} {value : V}
    (hentry : m.entries key = some value) :
    (m.erase key).insert key value = m := by
  cases m with
  | mk entries =>
      simp only [erase, insert]
      congr 1
      funext other
      by_cases h : other = key
      · subst other
        simpa using hentry.symm
      · simp [h]

/-- Inserting into an absent slot and taking it back restores the map. -/
theorem insert_erase_roundTrip
    {m : ResourceMapView K V} {key : K} {value : V}
    (hempty : m.entries key = none) :
    (m.insert key value).erase key = m := by
  cases m with
  | mk entries =>
      simp only [erase, insert]
      congr 1
      funext other
      by_cases h : other = key
      · subst other
        simpa using hempty.symm
      · simp [h]

/-- Generic entry well-formedness for a resource map. Resource-specific
instances supply only the pure view predicate; hidden ownership separation
remains in the resource-context interpretation (ADRs 0053–0054). -/
def wfWith
    (pred : V → Prop) (m : ResourceMapView K V) : Prop :=
  ∀ key value, m.entries key = some value → pred value

theorem wfWith_entry
    {pred : V → Prop} {m : ResourceMapView K V}
    (hwf : m.wfWith pred) {key : K} {value : V}
    (hentry : m.entries key = some value) : pred value :=
  hwf key value hentry

@[simp] theorem wfWith_empty (pred : V → Prop) :
    (empty : ResourceMapView K V).wfWith pred := by
  intro key value hentry
  simp at hentry

theorem wfWith_erase
    {pred : V → Prop} {m : ResourceMapView K V}
    (hwf : m.wfWith pred) (key : K) : (m.erase key).wfWith pred := by
  intro other value hentry
  have hne : other ≠ key := by
    intro heq
    subst other
    simp at hentry
  exact hwf other value (by simpa [erase, hne] using hentry)

theorem wfWith_insert
    {pred : V → Prop} {m : ResourceMapView K V}
    (hwf : m.wfWith pred) (key : K) {value : V}
    (hvalue : pred value) : (m.insert key value).wfWith pred := by
  intro other stored hentry
  by_cases heq : other = key
  · subst other
    simp only [insert_eq] at hentry
    cases hentry
    exact hvalue
  · exact hwf other stored (by simpa [insert, heq] using hentry)

/-! The first source-language instance: `u64` keys and `PointsTo<u64>`
entries. A total selector keeps generated terms first-order; its fallback is
unobservable because every use carries `canTakeU64`. -/

@[simp] def canTakeU64
    (m : ResourceMapView Int (PointsToView Int)) (key : Int) : Prop :=
  ∃ cell, m.entries key = some cell

def fallbackCellU64 : PointsToView Int :=
  { alloc := 0, off := 0, layout := u64.layout, state := .uninit }

def cellAtU64
    (m : ResourceMapView Int (PointsToView Int)) (key : Int) :
    PointsToView Int :=
  match m.entries key with
  | some cell => cell
  | none => fallbackCellU64

def wfU64 (m : ResourceMapView Int (PointsToView Int)) : Prop :=
  ∀ key cell, m.entries key = some cell → cell.wfU64

theorem canTakeU64_entry {m : ResourceMapView Int (PointsToView Int)}
    {key : Int} (h : m.canTakeU64 key) :
    m.entries key = some (m.cellAtU64 key) := by
  obtain ⟨cell, hcell⟩ := h
  simp [cellAtU64, hcell]

theorem wfU64_cellAt {m : ResourceMapView Int (PointsToView Int)}
    {key : Int} (hwf : m.wfU64) (htake : m.canTakeU64 key) :
    (m.cellAtU64 key).wfU64 :=
  hwf key _ (canTakeU64_entry htake)

@[simp] theorem wfU64_empty :
    (empty : ResourceMapView Int (PointsToView Int)).wfU64 := by
  intro key cell hentry
  simp at hentry

theorem wfU64_erase {m : ResourceMapView Int (PointsToView Int)}
    (hwf : m.wfU64) (key : Int) : (m.erase key).wfU64 := by
  intro other cell hentry
  have hne : other ≠ key := by
    intro heq
    subst other
    simp at hentry
  apply hwf other cell
  simpa [erase, hne] using hentry

theorem wfU64_insert {m : ResourceMapView Int (PointsToView Int)}
    (hwf : m.wfU64) (key : Int) {cell : PointsToView Int}
    (hcell : cell.wfU64) : (m.insert key cell).wfU64 := by
  intro other stored hentry
  by_cases heq : other = key
  · subst other
    simp only [insert_eq] at hentry
    cases hentry
    exact hcell
  · apply hwf other stored
    simpa [insert, heq] using hentry

end ResourceMapView

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
  headers : Int → Option FreeHeaderView

def AllocatorView.initial (allocator : Int) (root : SpanView) : AllocatorView :=
  { allocator, root,
    free := fun key => if key = 0 then some root else none,
    headers := fun _ => none }

def AllocatorView.canTake (v : AllocatorView) (key : Int) : Prop :=
  v.free key ≠ none ∧ v.headers key = none

def AllocatorView.leaseAt (v : AllocatorView) (key : Int) : BlockLeaseView :=
  { allocator := v.allocator, key, span := (v.free key).getD v.root }

def AllocatorView.take (v : AllocatorView) (key : Int) : AllocatorView :=
  { v with free := fun k => if k = key then none else v.free k }

def AllocatorView.canPut (v : AllocatorView) (lease : BlockLeaseView) : Prop :=
  lease.allocator = v.allocator ∧ v.free lease.key = none ∧
    v.headers lease.key = none

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
  block.allocator = v.allocator ∧ block.wf ∧
    v.headers block.key = none

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
    (∀ k, k ≠ 0 → v.free k = none) ∧
    ∀ k, v.headers k = none

def AllocatorView.wf (v : AllocatorView) : Prop :=
  (0 ≤ v.root.len ∧ v.root.len ≤ v.root.bytes.len) ∧
    (∀ k span, v.free k = some span →
      0 ≤ span.len ∧ span.len ≤ span.bytes.len) ∧
    ∀ k header, v.headers k = some header → header.wf

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

@[simp] theorem AllocatorView.take_canPut (v : AllocatorView) (key : Int)
    (h : v.canTake key) :
    (v.take key).canPut (v.leaseAt key) := by
  constructor
  · rfl
  constructor
  · simp [AllocatorView.take, AllocatorView.leaseAt]
  · change v.headers key = none
    exact h.2

@[simp] theorem AllocatorView.initial_wf (allocator : Int) (root : SpanView)
    (hroot : 0 ≤ root.len ∧ root.len ≤ root.bytes.len) :
    (AllocatorView.initial allocator root).wf := by
  constructor
  · exact hroot
  constructor
  · intro k span hentry
    by_cases hk : k = 0
    · subst k
      simp [AllocatorView.initial] at hentry
      simpa [hentry] using hroot
    · simp [AllocatorView.initial, hk] at hentry
  · simp [AllocatorView.initial]

@[simp] theorem AllocatorView.take_put (v : AllocatorView) (key : Int)
    (h : v.canTake key) :
    (v.take key).put (v.leaseAt key) = v := by
  cases v with
  | mk allocator root free headers =>
      simp only [AllocatorView.put, AllocatorView.take]
      congr 1
      funext k
      by_cases hk : k = key
      · subst k
        simp only [if_pos]
        simp [AllocatorView.leaseAt]
        cases heq : free key with
        | none => exact (h.1 heq).elim
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

@[simp] theorem FreeHeaderView.clearFields_toFree_allocator
    (v : FreeHeaderView) : v.clearFields.toFree.allocator = v.allocator := rfl

@[simp] theorem FreeHeaderView.clearFields_toFree_key
    (v : FreeHeaderView) : v.clearFields.toFree.key = v.key := rfl

@[simp] theorem FreeHeaderView.clearFields_toFree_span_alloc
    (v : FreeHeaderView) : v.clearFields.toFree.span.alloc = v.sizeCell.alloc := rfl

@[simp] theorem FreeHeaderView.clearFields_toFree_span_len
    (v : FreeHeaderView) :
    v.clearFields.toFree.span.len = v.toFree.span.len := rfl

@[simp] theorem FreeHeaderView.clearFields_putFields_toFree_span_len
    (v : FreeHeaderView) (size next : Int) :
    (v.clearFields.putFields size next).toFree.span.len =
      v.toFree.span.len := rfl

def AllocatorView.headerAt (v : AllocatorView) (key : Int) : FreeHeaderView :=
  (v.headers key).getD (v.takeFree key).toHeader

def AllocatorView.canTakeHeader (v : AllocatorView) (key : Int) : Prop :=
  v.headers key ≠ none ∧ v.free key = none ∧
    (v.headerAt key).key = key ∧ (v.headerAt key).wf ∧
    (v.headerAt key).allocator = v.allocator

def AllocatorView.takeHeader (v : AllocatorView) (key : Int) : AllocatorView :=
  { v with headers := fun k => if k = key then none else v.headers k }

def AllocatorView.canPutHeader
    (v : AllocatorView) (header : FreeHeaderView) : Prop :=
  header.allocator = v.allocator ∧ header.wf ∧
    v.free header.key = none ∧ v.headers header.key = none

def AllocatorView.putHeader
    (v : AllocatorView) (header : FreeHeaderView) : AllocatorView :=
  { v with headers := fun k =>
      if k = header.key then some header else v.headers k }

@[simp] theorem AllocatorView.takeHeader_headerAt_ne
    (v : AllocatorView) {removed key : Int} (hne : key ≠ removed) :
    (v.takeHeader removed).headerAt key = v.headerAt key := by
  simp [AllocatorView.takeHeader, AllocatorView.headerAt, hne,
    AllocatorView.takeFree, AllocatorView.leaseAt]

@[simp] theorem AllocatorView.putHeader_headerAt_ne
    (v : AllocatorView) (header : FreeHeaderView) {key : Int}
    (hne : key ≠ header.key) :
    (v.putHeader header).headerAt key = v.headerAt key := by
  simp [AllocatorView.putHeader, AllocatorView.headerAt, hne,
    AllocatorView.takeFree, AllocatorView.leaseAt]

theorem AllocatorView.takeHeader_canTakeHeader_ne
    (v : AllocatorView) {removed key : Int}
    (htake : v.canTakeHeader key) (hne : key ≠ removed) :
    (v.takeHeader removed).canTakeHeader key := by
  rcases htake with ⟨hpresent, hfree, hkey, hwf, howner⟩
  refine ⟨?_, hfree, ?_, ?_, ?_⟩
  · simpa [AllocatorView.takeHeader, hne] using hpresent
  · simpa [AllocatorView.takeHeader_headerAt_ne v hne] using hkey
  · simpa [AllocatorView.takeHeader_headerAt_ne v hne] using hwf
  · rw [AllocatorView.takeHeader_headerAt_ne v hne]
    change (v.headerAt key).allocator = v.allocator
    exact howner

theorem AllocatorView.putHeader_canTakeHeader_ne
    (v : AllocatorView) (header : FreeHeaderView) {key : Int}
    (htake : v.canTakeHeader key) (hne : key ≠ header.key) :
    (v.putHeader header).canTakeHeader key := by
  rcases htake with ⟨hpresent, hfree, hkey, hwf, howner⟩
  refine ⟨?_, hfree, ?_, ?_, ?_⟩
  · simpa [AllocatorView.putHeader, hne] using hpresent
  · simpa [AllocatorView.putHeader_headerAt_ne v header hne] using hkey
  · simpa [AllocatorView.putHeader_headerAt_ne v header hne] using hwf
  · rw [AllocatorView.putHeader_headerAt_ne v header hne]
    change (v.headerAt key).allocator = v.allocator
    exact howner

@[simp] theorem AllocatorView.putHeader_headerAt
    (v : AllocatorView) (header : FreeHeaderView) :
    (v.putHeader header).headerAt header.key = header := by
  simp [AllocatorView.putHeader, AllocatorView.headerAt]

@[simp] theorem AllocatorView.putHeader_canTakeHeader
    (v : AllocatorView) (header : FreeHeaderView)
    (hput : v.canPutHeader header) :
    (v.putHeader header).canTakeHeader header.key := by
  unfold AllocatorView.canPutHeader at hput
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [AllocatorView.putHeader]
  · simpa [AllocatorView.putHeader] using hput.2.2.1
  · rw [AllocatorView.putHeader_headerAt]
  · simpa using hput.2.1
  · rw [AllocatorView.putHeader_headerAt]
    change header.allocator = v.allocator
    exact hput.1

@[simp] theorem AllocatorView.takeHeader_canPutHeader
    (v : AllocatorView) (key : Int) (htake : v.canTakeHeader key) :
    (v.takeHeader key).canPutHeader (v.headerAt key) := by
  rcases htake with ⟨_, hfree, hkey, hwf, howner⟩
  refine ⟨howner, hwf, ?_, ?_⟩
  · rw [hkey]
    simpa [AllocatorView.takeHeader] using hfree
  · rw [hkey]
    simp [AllocatorView.takeHeader]

@[simp] theorem AllocatorView.takeHeader_putHeader
    (v : AllocatorView) (key : Int) (htake : v.canTakeHeader key) :
    (v.takeHeader key).putHeader (v.headerAt key) = v := by
  have hkey : (v.headerAt key).key = key := htake.2.2.1
  cases v with
  | mk allocator root free headers =>
      simp only [AllocatorView.putHeader, AllocatorView.takeHeader]
      congr 1
      funext k
      by_cases hk : k = key
      · subst k
        simp only [hkey, if_pos]
        simp [AllocatorView.headerAt]
        cases heq : headers key with
        | none => exact (htake.1 heq).elim
        | some header => simp
      · simp [hkey, hk]

theorem AllocatorView.takeFree_putFields_canPutHeader
    (v : AllocatorView) (key size next : Int)
    (htake : v.canTakeFree key)
    (hwf : ((v.takeFree key).toHeader.putFields size next).wf) :
    (v.take key).canPutHeader
      ((v.takeFree key).toHeader.putFields size next) := by
  refine ⟨rfl, hwf, ?_, ?_⟩
  · simp [AllocatorView.take, FreeBlockView.toHeader,
      FreeHeaderView.putFields, AllocatorView.takeFree,
      AllocatorView.leaseAt, BlockLeaseView.toFree]
  · simpa [AllocatorView.take, FreeBlockView.toHeader,
      FreeHeaderView.putFields, AllocatorView.takeFree,
      AllocatorView.leaseAt, BlockLeaseView.toFree] using htake.1.2

def FreeHeaderView.hasFields
    (header : FreeHeaderView) (size next : Int) : Prop :=
  header.sizeCell.state = .init size ∧
  header.nextCell.state = .init next

def AllocatorView.storesHeader
    (v : AllocatorView) (key : Int) (header : FreeHeaderView) : Prop :=
  v.headers key = some header ∧
  v.free key = none ∧
  header.key = key ∧
  header.wf ∧
  header.allocator = v.allocator ∧
  header.sizeCell.alloc = v.root.alloc

theorem AllocatorView.putHeader_storesHeader
    {v : AllocatorView} {header : FreeHeaderView}
    (hput : v.canPutHeader header)
    (hroot : header.sizeCell.alloc = v.root.alloc) :
    (v.putHeader header).storesHeader header.key header := by
  exact ⟨by simp [AllocatorView.putHeader],
    by simpa [AllocatorView.putHeader] using hput.2.2.1,
    rfl, hput.2.1,
    by change header.allocator = v.allocator; exact hput.1,
    by simpa [AllocatorView.putHeader] using hroot⟩

/-- No allocator role is hidden strictly inside a stored block. This is the
spatial vacancy needed to split the block and park a remainder header without
overlapping an unrelated map entry. -/
def AllocatorView.clearInterior
    (v : AllocatorView) (key size : Int) : Prop :=
  ∀ k, key < k → k < key + size →
    v.free k = none ∧ v.headers k = none

/-- A client lease can be returned to this allocator view without colliding
with an aggregate role. Besides allocator identity and an empty key slot, the
lease names one positive offset-derived extent in the allocator root and no
free/header entry begins strictly inside it. This is the frame allocation
produces and sorted insertion consumes. -/
def AllocatorView.returnable
    (v : AllocatorView) (lease : BlockLeaseView) : Prop :=
  v.canPut lease ∧
  lease.key = lease.span.off ∧
  0 < lease.span.len ∧
  lease.span.alloc = v.root.alloc ∧
  v.clearInterior lease.key lease.span.len

theorem AllocatorView.returnable_canPutHeader
    {v : AllocatorView} {lease : BlockLeaseView}
    {header : FreeHeaderView}
    (hreturn : v.returnable lease)
    (hkey : header.key = lease.key)
    (hwf : header.wf)
    (howner : header.allocator = lease.allocator) :
    v.canPutHeader header := by
  refine ⟨howner.trans hreturn.1.1, hwf, ?_, ?_⟩
  · rw [hkey]
    exact hreturn.1.2.1
  · rw [hkey]
    exact hreturn.1.2.2

theorem AllocatorView.returnable_clearInterior
    {v : AllocatorView} {lease : BlockLeaseView}
    {key size : Int}
    (hreturn : v.returnable lease)
    (hkey : lease.key = key) (hsize : lease.span.len = size) :
    v.clearInterior key size := by
  simpa [hkey, hsize] using hreturn.2.2.2.2

theorem AllocatorView.returnable_takeHeader_ne
    {v : AllocatorView} {lease : BlockLeaseView} {removed : Int}
    (hreturn : v.returnable lease) (hne : lease.key ≠ removed) :
    (v.takeHeader removed).returnable lease := by
  rcases hreturn with ⟨⟨howner, hfree, hheader⟩,
    hwhole, hpositive, hroot, hclear⟩
  refine ⟨⟨howner, hfree, ?_⟩, hwhole, hpositive, hroot, ?_⟩
  · simpa [AllocatorView.takeHeader, hne] using hheader
  · intro k hlo hhi
    obtain ⟨hfreeK, hheaderK⟩ := hclear k hlo hhi
    refine ⟨hfreeK, ?_⟩
    by_cases hk : k = removed
    · simp [AllocatorView.takeHeader, hk]
    · simpa [AllocatorView.takeHeader, hk] using hheaderK

/-- Parking a header wholly before or after a client lease preserves the
lease's exact return slot and interior frame. -/
theorem AllocatorView.returnable_putHeaderOutside
    {v : AllocatorView} {lease : BlockLeaseView}
    {header : FreeHeaderView}
    (hreturn : v.returnable lease)
    (houtside : header.key < lease.key ∨
      lease.key + lease.span.len ≤ header.key) :
    (v.putHeader header).returnable lease := by
  rcases hreturn with ⟨⟨howner, hfree, hheader⟩,
    hwhole, hpositive, hroot, hclear⟩
  have hne : lease.key ≠ header.key := by omega
  refine ⟨⟨howner, hfree, ?_⟩, hwhole, hpositive, hroot, ?_⟩
  · simpa [AllocatorView.putHeader, hne] using hheader
  · intro k hlo hhi
    have hk : k ≠ header.key := by omega
    obtain ⟨hfreeK, hheaderK⟩ := hclear k hlo hhi
    exact ⟨hfreeK,
      by simpa [AllocatorView.putHeader, hk] using hheaderK⟩

/-- Any positive prefix of a returnable lease remains returnable. The suffix
may subsequently be materialized as a header at the prefix's end. -/
theorem AllocatorView.returnable_prefix
    {v : AllocatorView} {lease : BlockLeaseView} {n : Int}
    (hreturn : v.returnable lease)
    (hn : 0 < n ∧ n ≤ lease.span.len) :
    v.returnable (lease.toFree.prefix n).toLease := by
  rcases hreturn with ⟨⟨howner, hfree, hheader⟩,
    hwhole, hpositive, hroot, hclear⟩
  refine ⟨⟨howner, hfree, hheader⟩, hwhole, hn.1, hroot, ?_⟩
  intro k hlo hhi
  simp [FreeBlockView.toLease, FreeBlockView.prefix,
    BlockLeaseView.toFree] at hlo hhi
  apply hclear k hlo
  omega

/-- After taking an adjacent stored successor, the returned lease's empty
interior and the successor's stored-chain frame combine into one empty
interior for their joined extent. The former header key is empty because it
is precisely the header being taken. -/
theorem AllocatorView.returnable_takeAdjacentHeader_clearInterior
    {v : AllocatorView} {lease : BlockLeaseView}
    {head size : Int} {header : FreeHeaderView}
    (hreturn : v.returnable lease)
    (adjacent : lease.key + lease.span.len = head)
    (stored : v.storesHeader head header)
    (successorClear : (v.takeHeader head).clearInterior head size) :
    (v.takeHeader head).clearInterior
      lease.key (lease.span.len + size) := by
  intro k hlo hhi
  by_cases hbefore : k < head
  · obtain ⟨hfree, hheaders⟩ := hreturn.2.2.2.2 k hlo (by omega)
    have hne : k ≠ head := by omega
    exact ⟨hfree,
      by simpa [AllocatorView.takeHeader, hne] using hheaders⟩
  · by_cases hat : k = head
    · subst k
      exact ⟨by simpa [AllocatorView.takeHeader] using stored.2.1,
        by simp [AllocatorView.takeHeader]⟩
    · have hafter : head < k := by omega
      apply successorClear k hafter
      omega

/-- After taking an adjacent stored predecessor, its empty interior and the
returned lease's collision frame combine into one empty interior. The lease
key itself is empty by `returnable`; all later keys come from the lease's
strict interior frame. -/
theorem AllocatorView.takeHeader_returnableAdjacent_clearInterior
    {v : AllocatorView} {lease : BlockLeaseView}
    {previous size : Int}
    (hreturn : v.returnable lease)
    (adjacent : previous + size = lease.key)
    (previousClear : (v.takeHeader previous).clearInterior previous size) :
    (v.takeHeader previous).clearInterior
      previous (size + lease.span.len) := by
  intro k hlo hhi
  by_cases hbefore : k < lease.key
  · apply previousClear k hlo
    omega
  · by_cases hat : k = lease.key
    · subst k
      have hne : lease.key ≠ previous := by omega
      exact ⟨hreturn.1.2.1,
        by simpa [AllocatorView.takeHeader, hne] using hreturn.1.2.2⟩
    · have hafter : lease.key < k := by omega
      obtain ⟨hfree, hheaders⟩ := hreturn.2.2.2.2 k hafter (by omega)
      have hne : k ≠ previous := by omega
      exact ⟨hfree,
        by simpa [AllocatorView.takeHeader, hne] using hheaders⟩

/-- Taking adjacent stored headers on both sides of a returned lease combines
the predecessor frame, the lease frame, and the successor frame into one
empty interior for the three-way joined extent. -/
theorem AllocatorView.takeAdjacentHeaders_returnable_clearInterior
    {v : AllocatorView} {lease : BlockLeaseView}
    {previous previousSize current successorSize : Int}
    {successor : FreeHeaderView}
    (hreturn : v.returnable lease)
    (previousAdjacent : previous + previousSize = lease.key)
    (successorAdjacent : lease.key + lease.span.len = current)
    (previousClear :
      (v.takeHeader previous).clearInterior previous previousSize)
    (successorStored : v.storesHeader current successor)
    (successorClear :
      (v.takeHeader current).clearInterior current successorSize) :
    ((v.takeHeader current).takeHeader previous).clearInterior
      previous (previousSize + lease.span.len + successorSize) := by
  intro k hlo hhi
  have leasePositive : 0 < lease.span.len := hreturn.2.2.1
  by_cases hbeforeLease : k < lease.key
  · have hneCurrent : k ≠ current := by omega
    simpa [AllocatorView.takeHeader, hneCurrent] using
      previousClear k hlo (by omega)
  · by_cases hatLease : k = lease.key
    · subst k
      have hnePrevious : lease.key ≠ previous := by omega
      have hneCurrent : lease.key ≠ current := by omega
      exact ⟨hreturn.1.2.1,
        by simpa [AllocatorView.takeHeader, hnePrevious, hneCurrent] using
          hreturn.1.2.2⟩
    · have hafterLease : lease.key < k := by omega
      by_cases hbeforeCurrent : k < current
      · obtain ⟨hfree, hheaders⟩ :=
          hreturn.2.2.2.2 k hafterLease (by omega)
        have hnePrevious : k ≠ previous := by omega
        have hneCurrent : k ≠ current := by omega
        exact ⟨hfree,
          by simpa [AllocatorView.takeHeader, hnePrevious, hneCurrent] using
            hheaders⟩
      · by_cases hatCurrent : k = current
        · subst k
          exact ⟨by simpa [AllocatorView.takeHeader] using successorStored.2.1,
            by simp [AllocatorView.takeHeader]⟩
        · have hafterCurrent : current < k := by omega
          have hnePrevious : k ≠ previous := by omega
          simpa [AllocatorView.takeHeader, hnePrevious] using
            successorClear k hafterCurrent (by omega)

theorem AllocatorView.clearInterior_takeHeader
    {v : AllocatorView} {key size : Int}
    (hclear : v.clearInterior key size) :
    (v.takeHeader key).clearInterior key size := by
  intro k hlo hhi
  have hne : k ≠ key := by omega
  obtain ⟨hfree, hheaders⟩ := hclear k hlo hhi
  exact ⟨hfree, by simpa [AllocatorView.takeHeader, hne] using hheaders⟩

inductive AllocatorView.StoredChain
    (v : AllocatorView) (limit : Int) : Int → Prop where
  | nil : StoredChain v limit limit
  | cons (key size next : Int) (header : FreeHeaderView)
      (stored : v.storesHeader key header)
      (fields : header.hasFields size next)
      (extent : header.toFree.span.len = size)
      (interior_clear : v.clearInterior key size)
      (key_nonneg : 0 ≤ key)
      (header_fits : freeHeaderBytes ≤ size)
      (ordered_disjoint : key + size ≤ next)
      (next_bounded : next ≤ limit)
      (tail : StoredChain v limit next) : StoredChain v limit key

theorem AllocatorView.storesHeader_headerAt
    {v : AllocatorView} {key : Int} {header : FreeHeaderView}
    (h : v.storesHeader key header) : v.headerAt key = header := by
  simp [AllocatorView.headerAt, h.1]

theorem AllocatorView.storesHeader_canTake
    {v : AllocatorView} {key : Int} {header : FreeHeaderView}
    (h : v.storesHeader key header) : v.canTakeHeader key := by
  have hat : v.headerAt key = header :=
    AllocatorView.storesHeader_headerAt h
  exact ⟨by simp [h.1], h.2.1, by simpa [hat] using h.2.2.1,
    by simpa [hat] using h.2.2.2.1,
    by simpa [hat] using h.2.2.2.2.1⟩

theorem AllocatorView.StoredChain.step
    {v : AllocatorView} {limit head : Int}
    (chain : v.StoredChain limit head) (hne : head ≠ limit) :
    ∃ header size next,
      v.storesHeader head header ∧
      header.hasFields size next ∧
      header.toFree.span.len = size ∧
      v.clearInterior head size ∧
      freeHeaderBytes ≤ size ∧
      head + size ≤ next ∧
      next ≤ limit ∧
      v.StoredChain limit next := by
  cases chain with
  | nil => exact (hne rfl).elim
  | cons key size next header stored fields extent hclear hkey hheader horder hbound tail =>
      exact ⟨header, size, next, stored, fields, extent, hclear,
        hheader, horder, hbound, tail⟩

theorem AllocatorView.StoredChain.head_le_limit
    {v : AllocatorView} {limit head : Int}
    (chain : v.StoredChain limit head) : head ≤ limit := by
  cases chain with
  | nil => omega
  | cons key size next header stored fields extent hclear hkey hsize horder hbound tail =>
      simp [freeHeaderBytes, u64.layout] at hsize
      omega

theorem AllocatorView.StoredChain.takeable
    {v : AllocatorView} {limit head : Int}
    (chain : v.StoredChain limit head) (hne : head ≠ limit) :
    v.canTakeHeader head := by
  obtain ⟨header, _, _, stored, _⟩ := chain.step hne
  exact AllocatorView.storesHeader_canTake stored

theorem AllocatorView.StoredChain.step_variant
    {v : AllocatorView} {limit head : Int}
    (chain : v.StoredChain limit head) (hne : head ≠ limit) :
    ∃ next, 0 ≤ limit - next ∧ limit - next < limit - head ∧
      v.StoredChain limit next := by
  obtain ⟨_, size, next, _, _, _, _, hheader, horder, hbound, tail⟩ :=
    chain.step hne
  refine ⟨next, by omega, ?_, tail⟩
  simp [freeHeaderBytes, u64.layout] at hheader
  omega

theorem AllocatorView.StoredChain.extract_restore
    {v : AllocatorView} {limit head : Int}
    (chain : v.StoredChain limit head) (hne : head ≠ limit) :
    (v.takeHeader head).putHeader (v.headerAt head) = v := by
  exact AllocatorView.takeHeader_putHeader v head (chain.takeable hne)

theorem AllocatorView.StoredChain.singleAfterPut
    {v : AllocatorView} {header : FreeHeaderView} {size limit : Int}
    (hput : v.canPutHeader header)
    (hfields : header.hasFields size limit)
    (hextent : header.toFree.span.len = size)
    (hclear : v.clearInterior header.key size)
    (hroot : header.sizeCell.alloc = v.root.alloc)
    (hkey : 0 ≤ header.key)
    (hsize : freeHeaderBytes ≤ size)
    (hbound : header.key + size ≤ limit) :
    (v.putHeader header).StoredChain limit header.key := by
  apply AllocatorView.StoredChain.cons header.key size limit header
  · exact ⟨by simp [AllocatorView.putHeader],
      by simpa [AllocatorView.putHeader] using hput.2.2.1,
      rfl, hput.2.1,
      by change header.allocator = v.allocator; exact hput.1,
      by simpa [AllocatorView.putHeader] using hroot⟩
  · exact hfields
  · exact hextent
  · intro k hlo hhi
    have hne : k ≠ header.key := by omega
    obtain ⟨hfree, hheaders⟩ := hclear k hlo hhi
    exact ⟨by simpa [AllocatorView.putHeader] using hfree,
      by simpa [AllocatorView.putHeader, hne] using hheaders⟩
  · exact hkey
  · exact hsize
  · exact hbound
  · omega
  · exact AllocatorView.StoredChain.nil

theorem AllocatorView.StoredChain.putHeaderBefore
    {v : AllocatorView} {limit head : Int} {header : FreeHeaderView}
    (chain : v.StoredChain limit head) (hbefore : header.key < head) :
    (v.putHeader header).StoredChain limit head := by
  induction chain with
  | nil => exact AllocatorView.StoredChain.nil
  | cons key size next node stored fields extent hclear hkey hsize horder hbound tail ih =>
      apply AllocatorView.StoredChain.cons key size next node
      · refine ⟨?_, stored.2.1, stored.2.2.1, stored.2.2.2.1,
          ?_, ?_⟩
        · have hne : key ≠ header.key := by omega
          simpa [AllocatorView.putHeader, hne] using stored.1
        · change node.allocator = v.allocator
          exact stored.2.2.2.2.1
        · simpa [AllocatorView.putHeader] using stored.2.2.2.2.2
      · exact fields
      · exact extent
      · intro k hlo hhi
        have hne : k ≠ header.key := by omega
        obtain ⟨hfree, hheaders⟩ := hclear k hlo hhi
        exact ⟨by simpa [AllocatorView.putHeader] using hfree,
          by simpa [AllocatorView.putHeader, hne] using hheaders⟩
      · exact hkey
      · exact hsize
      · exact horder
      · exact hbound
      · apply ih
        simp [freeHeaderBytes, u64.layout] at hsize
        omega

theorem AllocatorView.StoredChain.takeHeaderBefore
    {v : AllocatorView} {limit head removed : Int}
    (chain : v.StoredChain limit head) (hbefore : removed < head) :
    (v.takeHeader removed).StoredChain limit head := by
  induction chain with
  | nil => exact AllocatorView.StoredChain.nil
  | cons key size next node stored fields extent hclear hkey hsize horder hbound tail ih =>
      apply AllocatorView.StoredChain.cons key size next node
      · have hne : key ≠ removed := by omega
        refine ⟨?_, stored.2.1, stored.2.2.1, stored.2.2.2.1,
          ?_, ?_⟩
        · simpa [AllocatorView.takeHeader, hne] using stored.1
        · change node.allocator = v.allocator
          exact stored.2.2.2.2.1
        · simpa [AllocatorView.takeHeader] using stored.2.2.2.2.2
      · exact fields
      · exact extent
      · intro k hlo hhi
        have hne : k ≠ removed := by omega
        obtain ⟨hfree, hheaders⟩ := hclear k hlo hhi
        exact ⟨hfree,
          by simpa [AllocatorView.takeHeader, hne] using hheaders⟩
      · exact hkey
      · exact hsize
      · exact horder
      · exact hbound
      · apply ih
        simp [freeHeaderBytes, u64.layout] at hsize
        omega

/-- Extracting the first header removes only that node. The chain beginning at
its runtime successor remains valid in the residual allocator view. -/
theorem AllocatorView.StoredChain.takeHead
    {v : AllocatorView} {limit head : Int}
    (chain : v.StoredChain limit head) (notEnd : head ≠ limit) :
    ∃ header size next,
      v.storesHeader head header ∧
      header.hasFields size next ∧
      header.toFree.span.len = size ∧
      (v.takeHeader head).clearInterior head size ∧
      freeHeaderBytes ≤ size ∧
      head + size ≤ next ∧
      next ≤ limit ∧
      (v.takeHeader head).StoredChain limit next := by
  obtain ⟨header, size, next, stored, fields, extent, hclear, hsize,
      horder, hbound, tail⟩ := chain.step notEnd
  refine ⟨header, size, next, stored, fields, extent,
    AllocatorView.clearInterior_takeHeader hclear, hsize,
    horder, hbound, ?_⟩
  apply tail.takeHeaderBefore
  simp [freeHeaderBytes, u64.layout] at hsize
  omega

/-- Match caller-supplied runtime fields against the unique stored head and
return both the exact byte extent and the residual chain after extraction. -/
theorem AllocatorView.StoredChain.takeMatchingHead
    {v : AllocatorView} {limit head size next : Int}
    {header : FreeHeaderView}
    (chain : v.StoredChain limit head) (notEnd : head ≠ limit)
    (stored : v.storesHeader head header)
    (fields : header.hasFields size next) :
    header.toFree.span.len = size ∧
    (v.takeHeader head).clearInterior head size ∧
    freeHeaderBytes ≤ size ∧
    head + size ≤ next ∧
    next ≤ limit ∧
    (v.takeHeader head).StoredChain limit next := by
  obtain ⟨chainHeader, chainSize, chainNext, chainStored, chainFields,
      extent, hclear, hsize, horder, hbound, tail⟩ := chain.takeHead notEnd
  have hheader : chainHeader = header :=
    Option.some.inj (chainStored.1.symm.trans stored.1)
  subst chainHeader
  unfold FreeHeaderView.hasFields at chainFields fields
  have hsameSize : chainSize = size :=
    CellState.init.inj (chainFields.1.symm.trans fields.1)
  have hsameNext : chainNext = next :=
    CellState.init.inj (chainFields.2.symm.trans fields.2)
  simp only [hsameSize] at extent hclear hsize horder
  simp only [hsameNext] at horder hbound tail
  exact ⟨extent, hclear, hsize, horder, hbound, tail⟩

/-- Taking an exact stored head yields a returnable whole-block lease after
its two header fields are cleared. This is the bridge from list removal to the
public free operation's collision frame. -/
theorem AllocatorView.StoredChain.takeMatchingHead_returnable
    {v : AllocatorView} {limit head size next : Int}
    {header : FreeHeaderView}
    (chain : v.StoredChain limit head) (notEnd : head ≠ limit)
    (stored : v.storesHeader head header)
    (fields : header.hasFields size next) :
    (v.takeHeader head).returnable header.clearFields.toFree.toLease := by
  have matched := chain.takeMatchingHead notEnd stored fields
  have hwf := stored.2.2.2.1
  unfold FreeHeaderView.wf at hwf
  obtain ⟨hsizeWf, hnextWf, hkeyoff, halloc, hpayloadAlloc,
    hoff, hpayloadoff, hpayloadlen⟩ := hwf
  have leaseKey : header.clearFields.toFree.toLease.key = head := by
    change header.clearFields.toFree.key = head
    rw [FreeHeaderView.clearFields_toFree_key]
    exact stored.2.2.1
  have leaseLen : header.clearFields.toFree.toLease.span.len = size := by
    change header.clearFields.toFree.span.len = size
    rw [FreeHeaderView.clearFields_toFree_span_len]
    exact matched.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · change header.clearFields.toFree.allocator =
        (v.takeHeader head).allocator
      simpa [AllocatorView.takeHeader] using stored.2.2.2.2.1
    · rw [leaseKey]
      simpa [AllocatorView.takeHeader] using stored.2.1
    · rw [leaseKey]
      simp [AllocatorView.takeHeader]
  · simpa [FreeBlockView.toLease, FreeHeaderView.toFree,
      FreeHeaderView.rawCell, FreeHeaderView.clearFields,
      PointsToView.clear] using hkeyoff
  · rw [leaseLen]
    have hmin := matched.2.2.1
    simp [freeHeaderBytes, u64.layout] at hmin
    omega
  · change header.clearFields.toFree.span.alloc =
      (v.takeHeader head).root.alloc
    simpa [AllocatorView.takeHeader] using stored.2.2.2.2.2
  · rw [leaseKey, leaseLen]
    exact matched.2.1

theorem AllocatorView.StoredChain.prependAfterPut
    {v : AllocatorView} {header : FreeHeaderView}
    {size next limit : Int}
    (tail : v.StoredChain limit next)
    (hput : v.canPutHeader header)
    (hfields : header.hasFields size next)
    (hextent : header.toFree.span.len = size)
    (hclear : v.clearInterior header.key size)
    (hroot : header.sizeCell.alloc = v.root.alloc)
    (hkey : 0 ≤ header.key)
    (hsize : freeHeaderBytes ≤ size)
    (horder : header.key + size ≤ next)
    (hbound : next ≤ limit) :
    (v.putHeader header).StoredChain limit header.key := by
  apply AllocatorView.StoredChain.cons header.key size next header
  · exact ⟨by simp [AllocatorView.putHeader],
      by simpa [AllocatorView.putHeader] using hput.2.2.1,
      rfl, hput.2.1,
      by change header.allocator = v.allocator; exact hput.1,
      by simpa [AllocatorView.putHeader] using hroot⟩
  · exact hfields
  · exact hextent
  · intro k hlo hhi
    have hne : k ≠ header.key := by omega
    obtain ⟨hfree, hheaders⟩ := hclear k hlo hhi
    exact ⟨by simpa [AllocatorView.putHeader] using hfree,
      by simpa [AllocatorView.putHeader, hne] using hheaders⟩
  · exact hkey
  · exact hsize
  · exact horder
  · exact hbound
  · apply tail.putHeaderBefore
    simp [freeHeaderBytes, u64.layout] at hsize
    omega

/-- A runtime search has followed exactly these rejected header links from
`start` to `current`. Each recorded node is stored at the key reached by the
previous link and its actual size is smaller than the normalized request. -/
inductive AllocatorView.RejectedPrefix
    (v : AllocatorView) (limit need start : Int) : Int → Prop where
  | nil : RejectedPrefix v limit need start start
  | step {current size next : Int} {header : FreeHeaderView}
      (trace : RejectedPrefix v limit need start current)
      (notEnd : current ≠ limit)
      (stored : v.storesHeader current header)
      (fields : header.hasFields size next)
      (rejected : size < need) :
      RejectedPrefix v limit need start next

theorem AllocatorView.storesHeader_unique
    {v : AllocatorView} {key : Int} {left right : FreeHeaderView}
    (hleft : v.storesHeader key left)
    (hright : v.storesHeader key right) : left = right := by
  exact Option.some.inj (hleft.1.symm.trans hright.1)

/-- A rejected trace cannot leave the original sorted chain or step through
its sentinel. This is the semantic link that makes the witness a genuine
prefix rather than merely a sequence of entries from the same header map. -/
theorem AllocatorView.RejectedPrefix.tail
    {v : AllocatorView} {limit need start current : Int}
    (chain : v.StoredChain limit start)
    (trace : v.RejectedPrefix limit need start current) :
    v.StoredChain limit current := by
  induction trace with
  | nil => exact chain
  | @step previous size next header trace notEnd stored fields rejected ih =>
      obtain ⟨chainHeader, chainSize, chainNext, chainStored, chainFields,
          extent, hclear, hfit, horder, hbound, tail⟩ := ih.step notEnd
      have hheader : chainHeader = header :=
        AllocatorView.storesHeader_unique chainStored stored
      subst chainHeader
      have hnext : chainNext = next := by
        exact CellState.init.inj
          (chainFields.2.symm.trans fields.2)
      rw [← hnext]
      exact tail

/-- Two allocator views agree on all authority-map observations strictly
below a boundary, and retain the same allocator/root identity. This is the
frame needed to splice an unchanged rejected prefix onto a rebuilt tail. -/
def AllocatorView.AgreesBelow
    (v w : AllocatorView) (boundary : Int) : Prop :=
  v.allocator = w.allocator ∧ v.root = w.root ∧
  ∀ k, k < boundary →
    w.free k = v.free k ∧ w.headers k = v.headers k

/-- Replace the suffix at the endpoint of a genuine rejected prefix. If the
new allocator view agrees below that endpoint, every earlier stored node and
its clear interior frame across unchanged, so the rebuilt tail can be spliced
back into a chain from the original start. -/
theorem AllocatorView.RejectedPrefix.splice
    {v w : AllocatorView} {limit need start current : Int}
    (chain : v.StoredChain limit start)
    (trace : v.RejectedPrefix limit need start current)
    (agree : v.AgreesBelow w current)
    (tail : w.StoredChain limit current) :
    w.StoredChain limit start := by
  induction trace generalizing w with
  | nil => exact tail
  | @step previous size next header trace notEnd stored fields rejected ih =>
      have previousChain : v.StoredChain limit previous :=
        trace.tail chain
      obtain ⟨chainHeader, chainSize, chainNext, chainStored, chainFields,
          extent, hclear, hfit, horder, hbound, originalTail⟩ :=
        previousChain.step notEnd
      have hheader : chainHeader = header :=
        AllocatorView.storesHeader_unique chainStored stored
      subst chainHeader
      unfold FreeHeaderView.hasFields at chainFields fields
      have hsameSize : chainSize = size :=
        CellState.init.inj (chainFields.1.symm.trans fields.1)
      have hsameNext : chainNext = next :=
        CellState.init.inj (chainFields.2.symm.trans fields.2)
      simp only [hsameSize] at extent hclear hfit horder
      simp only [hsameNext] at horder hbound originalTail
      have hpreviousNext : previous < next := by
        simp [freeHeaderBytes, u64.layout] at hfit
        omega
      have atPrevious := agree.2.2 previous hpreviousNext
      have stored' : w.storesHeader previous header := by
        refine ⟨?_, ?_, stored.2.2.1, stored.2.2.2.1, ?_, ?_⟩
        · rw [atPrevious.2]
          exact stored.1
        · rw [atPrevious.1]
          exact stored.2.1
        · exact stored.2.2.2.2.1.trans agree.1
        · simpa [agree.2.1] using stored.2.2.2.2.2
      have clear' : w.clearInterior previous size := by
        intro k hlo hhi
        have hk : k < next := by omega
        have atK := agree.2.2 k hk
        obtain ⟨hfree, hheaders⟩ := hclear k hlo hhi
        exact ⟨by simpa [atK.1] using hfree,
          by simpa [atK.2] using hheaders⟩
      have hkey : 0 ≤ previous := by
        have hwf := chainStored.2.2.2.1
        unfold FreeHeaderView.wf at hwf
        calc
          0 ≤ header.sizeCell.off := hwf.1.2.1
          _ = header.key := hwf.2.2.1.symm
          _ = previous := chainStored.2.2.1
      have rebuilt : w.StoredChain limit previous :=
        AllocatorView.StoredChain.cons previous size next header
          stored' fields extent clear' hkey
          hfit horder hbound tail
      have agreePrevious : v.AgreesBelow w previous := by
        refine ⟨agree.1, agree.2.1, ?_⟩
        intro k hk
        exact agree.2.2 k (by omega)
      exact ih agreePrevious rebuilt

/-- `result` is the first fitting node, or the sentinel after every reachable
node was rejected. The original chain is retained explicitly so this remains
a complete search specification rather than a trace through unrelated map
entries. -/
def AllocatorView.FirstFit
    (v : AllocatorView) (limit start need result : Int) : Prop :=
  v.StoredChain limit start ∧
  v.RejectedPrefix limit need start result ∧
  (result = limit ∨
    ∃ header size next,
      v.storesHeader result header ∧
      header.hasFields size next ∧
      need ≤ size)

theorem AllocatorView.FirstFit.found
    {v : AllocatorView} {limit start need result size next : Int}
    {header : FreeHeaderView}
    (chain : v.StoredChain limit start)
    (trace : v.RejectedPrefix limit need start result)
    (stored : v.storesHeader result header)
    (fields : header.hasFields size next)
    (fits : need ≤ size) :
    v.FirstFit limit start need result := by
  exact ⟨chain, trace, Or.inr ⟨header, size, next, stored, fields, fits⟩⟩

theorem AllocatorView.FirstFit.notFound
    {v : AllocatorView} {limit start need : Int}
    (chain : v.StoredChain limit start)
    (trace : v.RejectedPrefix limit need start limit) :
    v.FirstFit limit start need limit := by
  exact ⟨chain, trace, Or.inl rfl⟩

theorem AllocatorView.FirstFit.resultChain
    {v : AllocatorView} {limit start need result : Int}
    (first : v.FirstFit limit start need result) :
    v.StoredChain limit result := by
  exact first.2.1.tail first.1

/-- The executable search cursor remembers both the node most recently
rejected and the node reached from it. `limit` is the distinguished
"no predecessor" value at the initial cursor. -/
inductive AllocatorView.RejectedPath
    (v : AllocatorView) (limit need start : Int) : Int → Int → Prop where
  | nil : RejectedPath v limit need start limit start
  | step {previous current size next : Int} {header : FreeHeaderView}
      (path : RejectedPath v limit need start previous current)
      (notEnd : current ≠ limit)
      (stored : v.storesHeader current header)
      (fields : header.hasFields size next)
      (rejected : size < need) :
      RejectedPath v limit need start current next

theorem AllocatorView.RejectedPath.toPrefix
    {v : AllocatorView} {limit need start previous current : Int}
    (path : v.RejectedPath limit need start previous current) :
    v.RejectedPrefix limit need start current := by
  induction path with
  | nil => exact AllocatorView.RejectedPrefix.nil
  | step path notEnd stored fields rejected ih =>
      exact AllocatorView.RejectedPrefix.step
        ih notEnd stored fields rejected

theorem AllocatorView.RejectedPath.tail
    {v : AllocatorView} {limit need start previous current : Int}
    (chain : v.StoredChain limit start)
    (path : v.RejectedPath limit need start previous current) :
    v.StoredChain limit current := by
  exact path.toPrefix.tail chain

theorem AllocatorView.RejectedPath.predecessor
    {v : AllocatorView} {limit need start previous current : Int}
    (path : v.RejectedPath limit need start previous current)
    (notHead : current ≠ start) :
    ∃ header size,
      v.storesHeader previous header ∧
      header.hasFields size current ∧
      size < need := by
  cases path with
  | nil => exact (notHead rfl).elim
  | step path notEnd stored fields rejected =>
      exact ⟨_, _, stored, fields, rejected⟩

/-- A read-only insertion search has followed exactly the stored links whose
runtime keys lie strictly before `key`. Unlike `RejectedPath`, the decision is
about address order rather than block size. -/
inductive AllocatorView.BeforePath
    (v : AllocatorView) (limit key start : Int) : Int → Int → Prop where
  | nil : BeforePath v limit key start limit start
  | step {previous current size next : Int} {header : FreeHeaderView}
      (path : BeforePath v limit key start previous current)
      (notEnd : current ≠ limit)
      (stored : v.storesHeader current header)
      (fields : header.hasFields size next)
      (before : current < key) :
      BeforePath v limit key start current next

/-- Forget the address-order test and retain the structural stored prefix.
Every initialized header size is a `u64`, hence is rejected by the purely
logical request `u64.max + 1`. This lets insertion reuse the generic prefix
splice theorem without duplicating it. -/
theorem AllocatorView.BeforePath.toPrefix
    {v : AllocatorView}
    {limit key start previous current : Int}
    (path : v.BeforePath limit key start previous current) :
    v.RejectedPrefix limit (18446744073709551615 + 1) start current := by
  induction path with
  | nil => exact AllocatorView.RejectedPrefix.nil
  | @step previous current size next header path notEnd stored fields before ih =>
      apply AllocatorView.RejectedPrefix.step ih notEnd stored fields
      have hsize := stored.2.2.2.1.1
      unfold PointsToView.wfU64 at hsize
      unfold FreeHeaderView.hasFields at fields
      rw [fields.1] at hsize
      simp at hsize ⊢
      omega

theorem AllocatorView.BeforePath.tail
    {v : AllocatorView}
    {limit key start previous current : Int}
    (chain : v.StoredChain limit start)
    (path : v.BeforePath limit key start previous current) :
    v.StoredChain limit current := by
  exact path.toPrefix.tail chain

theorem AllocatorView.BeforePath.splice
    {v w : AllocatorView}
    {limit key start previous current : Int}
    (chain : v.StoredChain limit start)
    (path : v.BeforePath limit key start previous current)
    (agree : v.AgreesBelow w current)
    (tail : w.StoredChain limit current) :
    w.StoredChain limit start := by
  exact path.toPrefix.splice chain agree tail

theorem AllocatorView.BeforePath.mono
    {v : AllocatorView}
    {limit oldKey newKey start previous current : Int}
    (path : v.BeforePath limit oldKey start previous current)
    (hle : oldKey ≤ newKey) :
    v.BeforePath limit newKey start previous current := by
  induction path with
  | nil => exact AllocatorView.BeforePath.nil
  | step path notEnd stored fields before ih =>
      exact AllocatorView.BeforePath.step
        ih notEnd stored fields (by omega)

/-- Address-order paths survive a view change that agrees below their final
cursor. This is the insertion analogue of rejected-prefix splicing. -/
theorem AllocatorView.BeforePath.transport
    {v w : AllocatorView}
    {limit key start previous current : Int}
    (chain : v.StoredChain limit start)
    (path : v.BeforePath limit key start previous current)
    (agree : v.AgreesBelow w current) :
    w.BeforePath limit key start previous current := by
  induction path generalizing w with
  | nil => exact AllocatorView.BeforePath.nil
  | @step priorPrevious node size next header path notEnd stored fields before ih =>
      have nodeChain : v.StoredChain limit node := path.tail chain
      have matched := nodeChain.takeMatchingHead notEnd stored fields
      have nodeBeforeNext : node < next := by
        have hmin := matched.2.2.1
        have horder := matched.2.2.2.1
        simp [freeHeaderBytes, u64.layout] at hmin
        omega
      have atNode := agree.2.2 node nodeBeforeNext
      have stored' : w.storesHeader node header := by
        refine ⟨?_, ?_, stored.2.2.1, stored.2.2.2.1, ?_, ?_⟩
        · rw [atNode.2]
          exact stored.1
        · rw [atNode.1]
          exact stored.2.1
        · exact stored.2.2.2.2.1.trans agree.1
        · simpa [agree.2.1] using stored.2.2.2.2.2
      have agreeNode : v.AgreesBelow w node := by
        refine ⟨agree.1, agree.2.1, ?_⟩
        intro k hk
        exact agree.2.2 k (by omega)
      exact AllocatorView.BeforePath.step
        (ih agreeNode) notEnd stored' fields before

theorem AllocatorView.BeforePath.predecessor
    {v : AllocatorView}
    {limit key start previous current : Int}
    (path : v.BeforePath limit key start previous current)
    (notHead : current ≠ start) :
    ∃ header size,
      v.storesHeader previous header ∧
      header.hasFields size current ∧ previous < key := by
  cases path with
  | nil => exact (notHead rfl).elim
  | step path notEnd stored fields before =>
      exact ⟨_, _, stored, fields, before⟩

/-- A size-rejection path also records an address prefix ending at its own
cursor: stored-chain ordering makes every traversed key strictly smaller than
that endpoint. -/
theorem AllocatorView.RejectedPath.toBeforePath
    {v : AllocatorView}
    {limit need start previous current : Int}
    (chain : v.StoredChain limit start)
    (path : v.RejectedPath limit need start previous current) :
    v.BeforePath limit current start previous current := by
  induction path with
  | nil => exact AllocatorView.BeforePath.nil
  | @step previous current size next header path notEnd stored fields rejected ih =>
      have currentChain : v.StoredChain limit current := path.tail chain
      have matched := currentChain.takeMatchingHead notEnd stored fields
      have currentBeforeNext : current < next := by
        have hmin := matched.2.2.1
        have horder := matched.2.2.2.1
        simp [freeHeaderBytes, u64.layout] at hmin
        omega
      exact AllocatorView.BeforePath.step
        (ih.mono (by omega)) notEnd stored fields currentBeforeNext

/-- The deterministic remainder of an address-order insertion search. The
first two cursors are its input state; the last two are the predecessor and
current cursor at the first sentinel-or-not-before stopping point. -/
inductive AllocatorView.InsertionSearch
    (v : AllocatorView) (limit key : Int) :
    Int → Int → Int → Int → Prop where
  | done {previous current : Int}
      (stop : current = limit ∨ key ≤ current) :
      InsertionSearch v limit key previous current previous current
  | step {previous current size next resultPrevious resultCurrent : Int}
      {header : FreeHeaderView}
      (notEnd : current ≠ limit)
      (stored : v.storesHeader current header)
      (fields : header.hasFields size next)
      (before : current < key)
      (tail : InsertionSearch v limit key current next
        resultPrevious resultCurrent) :
      InsertionSearch v limit key previous current
        resultPrevious resultCurrent

theorem AllocatorView.InsertionSearch.unique
    {v : AllocatorView} {limit key previous current : Int}
    {leftPrevious leftCurrent rightPrevious rightCurrent : Int}
    (left : v.InsertionSearch limit key previous current
      leftPrevious leftCurrent)
    (right : v.InsertionSearch limit key previous current
      rightPrevious rightCurrent) :
    leftPrevious = rightPrevious ∧ leftCurrent = rightCurrent := by
  induction left generalizing rightPrevious rightCurrent with
  | @done previous current stop =>
      cases right with
      | done => exact ⟨rfl, rfl⟩
      | step notEnd stored fields before tail =>
          cases stop with
          | inl atEnd => exact (notEnd atEnd).elim
          | inr notBefore => omega
  | @step previous current size next resultPrevious resultCurrent header
      notEnd stored fields before tail ih =>
      cases right with
      | done stop =>
          cases stop with
          | inl atEnd => exact (notEnd atEnd).elim
          | inr notBefore => omega
      | @step _ _ rightSize rightNext _ _ rightHeader
          rightNotEnd rightStored rightFields rightBefore rightTail =>
          have sameHeader : header = rightHeader :=
            AllocatorView.storesHeader_unique stored rightStored
          subst rightHeader
          unfold FreeHeaderView.hasFields at fields rightFields
          have sameNext : next = rightNext :=
            CellState.init.inj (fields.2.symm.trans rightFields.2)
          subst rightNext
          exact ih rightTail

theorem AllocatorView.BeforePath.prependSearch
    {v : AllocatorView}
    {limit key start previous current resultPrevious resultCurrent : Int}
    (path : v.BeforePath limit key start previous current)
    (search : v.InsertionSearch limit key previous current
      resultPrevious resultCurrent) :
    v.InsertionSearch limit key limit start resultPrevious resultCurrent := by
  induction path generalizing resultPrevious resultCurrent with
  | nil => exact search
  | step path notEnd stored fields before ih =>
      apply ih
      exact AllocatorView.InsertionSearch.step
        notEnd stored fields before search

theorem AllocatorView.BeforePath.toSearch
    {v : AllocatorView}
    {limit key start previous current : Int}
    (path : v.BeforePath limit key start previous current)
    (stop : current = limit ∨ key ≤ current) :
    v.InsertionSearch limit key limit start previous current := by
  exact path.prependSearch (AllocatorView.InsertionSearch.done stop)

/-- The exact sorted gap in which a returned client extent may be inserted.
The path identifies the runtime predecessor/current pair; the two inequalities
state the spatial facts that `returnable` intentionally does not invent. -/
def AllocatorView.InsertionLocation
    (v : AllocatorView)
    (limit start key size previous current : Int) : Prop :=
  v.StoredChain limit start ∧
  v.BeforePath limit key start previous current ∧
  key + size ≤ current ∧
  ((previous = limit ∧ current = start) ∨
    ∃ header previousSize,
      v.storesHeader previous header ∧
      header.hasFields previousSize current ∧
      previous + previousSize ≤ key)

theorem AllocatorView.InsertionLocation.head
    {v : AllocatorView} {limit start key size : Int}
    (chain : v.StoredChain limit start)
    (before : key + size ≤ start) :
    v.InsertionLocation limit start key size limit start := by
  exact ⟨chain, AllocatorView.BeforePath.nil, before,
    Or.inl ⟨rfl, rfl⟩⟩

theorem AllocatorView.InsertionLocation.after
    {v : AllocatorView}
    {limit start key size previous current previousSize : Int}
    {header : FreeHeaderView}
    (chain : v.StoredChain limit start)
    (path : v.BeforePath limit key start previous current)
    (beforeCurrent : key + size ≤ current)
    (stored : v.storesHeader previous header)
    (fields : header.hasFields previousSize current)
    (afterPrevious : previous + previousSize ≤ key) :
    v.InsertionLocation limit start key size previous current := by
  exact ⟨chain, path, beforeCurrent,
    Or.inr ⟨header, previousSize, stored, fields, afterPrevious⟩⟩

theorem AllocatorView.InsertionLocation.currentChain
    {v : AllocatorView}
    {limit start key size previous current : Int}
    (location : v.InsertionLocation
      limit start key size previous current) :
    v.StoredChain limit current := by
  exact location.2.1.tail location.1

theorem AllocatorView.InsertionLocation.toSearch
    {v : AllocatorView}
    {limit start key size previous current : Int}
    (location : v.InsertionLocation
      limit start key size previous current)
    (positive : 0 < size) :
    v.InsertionSearch limit key limit start previous current := by
  apply location.2.1.toSearch
  exact Or.inr (by
    have beforeCurrent := location.2.2.1
    omega)

theorem AllocatorView.InsertionLocation.predecessor
    {v : AllocatorView}
    {limit start key size previous current : Int}
    (location : v.InsertionLocation
      limit start key size previous current)
    (notHead : current ≠ start) :
    ∃ header previousSize,
      v.storesHeader previous header ∧
      header.hasFields previousSize current ∧
      previous + previousSize ≤ key := by
  cases location.2.2.2 with
  | inl atHead => exact (notHead atHead.2).elim
  | inr after => exact after

theorem AllocatorView.InsertionLocation.predecessorChain
    {v : AllocatorView}
    {limit start key size previous current : Int}
    (location : v.InsertionLocation
      limit start key size previous current)
    (notHead : current ≠ start) :
    v.StoredChain limit previous := by
  cases location.2.1 with
  | nil => exact (notHead rfl).elim
  | step priorPath notEnd stored fields before =>
      exact priorPath.tail location.1

theorem AllocatorView.InsertionLocation.predecessorNotEnd
    {v : AllocatorView}
    {limit start key size previous current : Int}
    (location : v.InsertionLocation
      limit start key size previous current)
    (notHead : current ≠ start) : previous ≠ limit := by
  cases location.2.1 with
  | nil => exact (notHead rfl).elim
  | step priorPath notEnd stored fields before => exact notEnd

/-- A return frame paired with the sorted-list gap needed to consume it. -/
def AllocatorView.returnableIn
    (v : AllocatorView) (limit start : Int) (lease : BlockLeaseView) : Prop :=
  v.returnable lease ∧
  ∃ previous current,
    v.InsertionLocation limit start lease.key lease.span.len
      previous current

theorem AllocatorView.returnableIn_location
    {v : AllocatorView} {limit start : Int} {lease : BlockLeaseView}
    {previous current : Int}
    (hreturn : v.returnableIn limit start lease)
    (search : v.InsertionSearch limit lease.key limit start
      previous current) :
    v.InsertionLocation limit start lease.key lease.span.len
      previous current := by
  obtain ⟨witnessPrevious, witnessCurrent, witness⟩ := hreturn.2
  have witnessSearch := witness.toSearch hreturn.1.2.2.1
  have same := witnessSearch.unique search
  simpa [same.1, same.2] using witness

/-- Insert one exact returned extent after a stored predecessor. The returned
header is parked at `key`, the predecessor is rebuilt to point at it, and the
untouched address-ordered prefix is spliced back over the rebuilt suffix. -/
theorem AllocatorView.InsertionLocation.insertAfter
    {v : AllocatorView}
    {limit start key size previous current previousSize : Int}
    (location : v.InsertionLocation
      limit start key size previous current)
    (notHead : current ≠ start)
    {inserted predecessor relinked : FreeHeaderView}
    (insertedKey : inserted.key = key)
    (insertedFields : inserted.hasFields size current)
    (insertedExtent : inserted.toFree.span.len = size)
    (insertedClear : (v.takeHeader previous).clearInterior inserted.key size)
    (insertedRoot : inserted.sizeCell.alloc =
      (v.takeHeader previous).root.alloc)
    (canPutInserted : (v.takeHeader previous).canPutHeader inserted)
    (predecessorStored : v.storesHeader previous predecessor)
    (predecessorFields : predecessor.hasFields previousSize current)
    (relinkedEq : relinked =
      predecessor.clearFields.putFields previousSize key)
    (canPutRelinked :
      ((v.takeHeader previous).putHeader inserted).canPutHeader relinked)
    (keyNonneg : 0 ≤ key)
    (insertedMin : freeHeaderBytes ≤ size) :
    (((v.takeHeader previous).putHeader inserted).putHeader relinked
      ).StoredChain limit start := by
  obtain ⟨locationHeader, locationSize, locationStored, locationFields,
      afterPrevious⟩ := location.predecessor notHead
  have sameHeader : locationHeader = predecessor :=
    AllocatorView.storesHeader_unique locationStored predecessorStored
  subst locationHeader
  unfold FreeHeaderView.hasFields at locationFields predecessorFields
  have sameSize : locationSize = previousSize :=
    CellState.init.inj (locationFields.1.symm.trans predecessorFields.1)
  simp only [sameSize] at afterPrevious
  cases pathEq : location.2.1 with
  | nil => exact (notHead rfl).elim
  | step priorPath predecessorNotEnd pathStored pathFields beforeKey =>
      have previousChain : v.StoredChain limit previous := by
        simpa using priorPath.tail location.1
      have previousMatch := previousChain.takeMatchingHead
        predecessorNotEnd predecessorStored predecessorFields
      have previousMin := previousMatch.2.2.1
      have previousBeforeKey : previous < key := by
        simp [freeHeaderBytes, u64.layout] at previousMin
        omega
      have insertedPositive : 0 < size := by
        have hmin := insertedMin
        simp [freeHeaderBytes, u64.layout] at hmin
        omega
      have beforeCurrent : key + size ≤ current := location.2.2.1
      have currentChain : v.StoredChain limit current :=
        location.currentChain
      have currentBound : current ≤ limit := currentChain.head_le_limit
      have previousCurrent : previous < current := by omega
      have tailAfterTake :
          (v.takeHeader previous).StoredChain limit current := by
        exact currentChain.takeHeaderBefore previousCurrent
      have insertedChainAtKey :
          ((v.takeHeader previous).putHeader inserted).StoredChain
            limit inserted.key := by
        apply AllocatorView.StoredChain.prependAfterPut
          tailAfterTake canPutInserted insertedFields insertedExtent
          insertedClear insertedRoot
        · rw [insertedKey]
          exact keyNonneg
        · exact insertedMin
        · rw [insertedKey]
          exact beforeCurrent
        · exact currentBound
      have insertedChain :
          ((v.takeHeader previous).putHeader inserted).StoredChain
            limit key := by
        rw [insertedKey] at insertedChainAtKey
        exact insertedChainAtKey
      have relinkedKey : relinked.key = previous := by
        rw [relinkedEq]
        exact predecessorStored.2.2.1
      have relinkedFields : relinked.hasFields previousSize key := by
        simp [relinkedEq, FreeHeaderView.hasFields,
          FreeHeaderView.clearFields, FreeHeaderView.putFields]
      have relinkedExtent : relinked.toFree.span.len = previousSize := by
        rw [relinkedEq]
        simpa using previousMatch.1
      have relinkedClear :
          ((v.takeHeader previous).putHeader inserted).clearInterior
            relinked.key previousSize := by
        rw [relinkedKey]
        intro k hlo hhi
        have hkPrevious : k ≠ previous := by omega
        have hkInserted : k ≠ inserted.key := by
          rw [insertedKey]
          omega
        simpa [AllocatorView.takeHeader, AllocatorView.putHeader,
          hkPrevious, hkInserted] using
          previousMatch.2.1 k hlo hhi
      have relinkedRoot : relinked.sizeCell.alloc =
          ((v.takeHeader previous).putHeader inserted).root.alloc := by
        rw [relinkedEq]
        exact predecessorStored.2.2.2.2.2
      have previousNonneg : 0 ≤ previous := by
        have hwf := predecessorStored.2.2.2.1
        unfold FreeHeaderView.wf at hwf
        calc
          0 ≤ predecessor.sizeCell.off := hwf.1.2.1
          _ = predecessor.key := hwf.2.2.1.symm
          _ = previous := predecessorStored.2.2.1
      have rebuiltAtKey :
          (((v.takeHeader previous).putHeader inserted).putHeader relinked
            ).StoredChain limit relinked.key := by
        apply AllocatorView.StoredChain.prependAfterPut
          insertedChain canPutRelinked relinkedFields relinkedExtent
          relinkedClear relinkedRoot
        · rw [relinkedKey]
          exact previousNonneg
        · exact previousMin
        · rw [relinkedKey]
          exact afterPrevious
        · omega
      have rebuilt :
          (((v.takeHeader previous).putHeader inserted).putHeader relinked
            ).StoredChain limit previous := by
        rw [relinkedKey] at rebuiltAtKey
        exact rebuiltAtKey
      have agree : v.AgreesBelow
          (((v.takeHeader previous).putHeader inserted).putHeader relinked)
          previous := by
        refine ⟨rfl, rfl, ?_⟩
        intro k hk
        have hkPrevious : k ≠ previous := by omega
        have hkInserted : k ≠ inserted.key := by
          rw [insertedKey]
          omega
        have hkRelinked : k ≠ relinked.key := by
          rw [relinkedKey]
          omega
        simp [AllocatorView.takeHeader, AllocatorView.putHeader,
          hkPrevious, hkInserted, hkRelinked]
      exact priorPath.splice location.1 agree rebuilt

/-- Replace the stored predecessor at an insertion location with another
header at the same key. This is the list-structural core of predecessor
coalescing: the caller proves the larger byte extent and fields, while this
lemma preserves the untouched suffix and splices the unchanged prefix back
over the replacement. -/
theorem AllocatorView.InsertionLocation.replacePredecessor
    {v : AllocatorView}
    {limit start key gapSize previous current previousSize replacementSize : Int}
    (location : v.InsertionLocation
      limit start key gapSize previous current)
    (notHead : current ≠ start)
    {predecessor replacement : FreeHeaderView}
    (predecessorStored : v.storesHeader previous predecessor)
    (predecessorFields : predecessor.hasFields previousSize current)
    (replacementKey : replacement.key = previous)
    (replacementFields : replacement.hasFields replacementSize current)
    (replacementExtent : replacement.toFree.span.len = replacementSize)
    (replacementClear :
      (v.takeHeader previous).clearInterior replacement.key replacementSize)
    (replacementRoot : replacement.sizeCell.alloc =
      (v.takeHeader previous).root.alloc)
    (canPutReplacement :
      (v.takeHeader previous).canPutHeader replacement)
    (replacementNonneg : 0 ≤ replacement.key)
    (replacementMin : freeHeaderBytes ≤ replacementSize)
    (replacementOrder : replacement.key + replacementSize ≤ current) :
    ((v.takeHeader previous).putHeader replacement
      ).StoredChain limit start := by
  cases pathEq : location.2.1 with
  | nil => exact (notHead rfl).elim
  | step priorPath predecessorNotEnd pathStored pathFields beforeKey =>
      have previousChain : v.StoredChain limit previous := by
        simpa using priorPath.tail location.1
      have previousMatch := previousChain.takeMatchingHead
        predecessorNotEnd predecessorStored predecessorFields
      have previousMin := previousMatch.2.2.1
      have previousCurrent : previous < current := by
        have previousOrder := previousMatch.2.2.2.1
        simp [freeHeaderBytes, u64.layout] at previousMin
        omega
      have currentChain : v.StoredChain limit current :=
        location.currentChain
      have tailAfterTake :
          (v.takeHeader previous).StoredChain limit current :=
        currentChain.takeHeaderBefore previousCurrent
      have rebuiltAtKey :
          ((v.takeHeader previous).putHeader replacement).StoredChain
            limit replacement.key := by
        apply AllocatorView.StoredChain.prependAfterPut
          tailAfterTake canPutReplacement replacementFields
          replacementExtent replacementClear replacementRoot
          replacementNonneg replacementMin replacementOrder
        exact currentChain.head_le_limit
      have rebuilt :
          ((v.takeHeader previous).putHeader replacement).StoredChain
            limit previous := by
        rw [replacementKey] at rebuiltAtKey
        exact rebuiltAtKey
      have agree : v.AgreesBelow
          ((v.takeHeader previous).putHeader replacement) previous := by
        refine ⟨rfl, rfl, ?_⟩
        intro k hk
        have hkPrevious : k ≠ previous := by omega
        have hkReplacement : k ≠ replacement.key := by
          rw [replacementKey]
          omega
        simp [AllocatorView.takeHeader, AllocatorView.putHeader,
          hkPrevious, hkReplacement]
      exact priorPath.splice location.1 agree rebuilt

/-- Remove the stored successor at a non-head insertion location, replace it
with a merged header beginning at the returned key, and relink the exact
predecessor to that header. The caller supplies the byte-level merge facts;
this theorem preserves the untouched suffix and prefix. -/
theorem AllocatorView.InsertionLocation.coalesceSuccessorAfter
    {v : AllocatorView}
    {limit start key gapSize previous current previousSize
      successorSize next mergedSize : Int}
    (location : v.InsertionLocation
      limit start key gapSize previous current)
    (notHead : current ≠ start)
    (currentNotEnd : current ≠ limit)
    {predecessor successor merged relinked : FreeHeaderView}
    (predecessorStored : v.storesHeader previous predecessor)
    (predecessorFields : predecessor.hasFields previousSize current)
    (successorStored : v.storesHeader current successor)
    (successorFields : successor.hasFields successorSize next)
    (mergedKey : merged.key = key)
    (mergedFields : merged.hasFields mergedSize next)
    (mergedExtent : merged.toFree.span.len = mergedSize)
    (mergedClear :
      ((v.takeHeader current).takeHeader previous).clearInterior
        merged.key mergedSize)
    (mergedRoot : merged.sizeCell.alloc =
      ((v.takeHeader current).takeHeader previous).root.alloc)
    (canPutMerged :
      ((v.takeHeader current).takeHeader previous).canPutHeader merged)
    (relinkedEq : relinked =
      predecessor.clearFields.putFields previousSize key)
    (canPutRelinked :
      (((v.takeHeader current).takeHeader previous).putHeader merged
        ).canPutHeader relinked)
    (mergedNonneg : 0 ≤ merged.key)
    (mergedMin : freeHeaderBytes ≤ mergedSize)
    (mergedOrder : merged.key + mergedSize ≤ next) :
    ((((v.takeHeader current).takeHeader previous).putHeader merged
      ).putHeader relinked).StoredChain limit start := by
  obtain ⟨locationHeader, locationSize, locationStored, locationFields,
      afterPrevious⟩ := location.predecessor notHead
  have sameHeader : locationHeader = predecessor :=
    AllocatorView.storesHeader_unique locationStored predecessorStored
  subst locationHeader
  unfold FreeHeaderView.hasFields at locationFields predecessorFields
  have sameSize : locationSize = previousSize :=
    CellState.init.inj (locationFields.1.symm.trans predecessorFields.1)
  simp only [sameSize] at afterPrevious
  have currentChain : v.StoredChain limit current := location.currentChain
  have currentMatch := currentChain.takeMatchingHead currentNotEnd
    successorStored successorFields
  cases pathEq : location.2.1 with
  | nil => exact (notHead rfl).elim
  | step priorPath predecessorNotEnd pathStored pathFields beforeKey =>
      have previousChain : v.StoredChain limit previous := by
        simpa using priorPath.tail location.1
      have previousMatch := previousChain.takeMatchingHead
        predecessorNotEnd predecessorStored predecessorFields
      have previousCurrent : previous < current := by
        have hfit := previousMatch.2.2.1
        have horder := previousMatch.2.2.2.1
        simp [freeHeaderBytes, u64.layout] at hfit
        omega
      have currentNext : current < next := by
        have hfit := currentMatch.2.2.1
        have horder := currentMatch.2.2.2.1
        simp [freeHeaderBytes, u64.layout] at hfit
        omega
      have bareTail :
          ((v.takeHeader current).takeHeader previous).StoredChain
            limit next := by
        apply currentMatch.2.2.2.2.2.takeHeaderBefore
        omega
      have mergedChainAtKey :
          (((v.takeHeader current).takeHeader previous).putHeader merged
            ).StoredChain limit merged.key := by
        apply AllocatorView.StoredChain.prependAfterPut
          bareTail canPutMerged mergedFields mergedExtent mergedClear
          mergedRoot mergedNonneg mergedMin mergedOrder
        exact currentMatch.2.2.2.2.1
      have mergedChain :
          (((v.takeHeader current).takeHeader previous).putHeader merged
            ).StoredChain limit key := by
        rw [mergedKey] at mergedChainAtKey
        exact mergedChainAtKey
      have relinkedKey : relinked.key = previous := by
        rw [relinkedEq]
        exact predecessorStored.2.2.1
      have relinkedFields : relinked.hasFields previousSize key := by
        simp [relinkedEq, FreeHeaderView.hasFields,
          FreeHeaderView.clearFields, FreeHeaderView.putFields]
      have relinkedExtent : relinked.toFree.span.len = previousSize := by
        rw [relinkedEq]
        simpa using previousMatch.1
      have relinkedClear :
          (((v.takeHeader current).takeHeader previous).putHeader merged
            ).clearInterior relinked.key previousSize := by
        rw [relinkedKey]
        intro k hlo hhi
        have hkPrevious : k ≠ previous := by omega
        have hkCurrent : k ≠ current := by
          have horder := previousMatch.2.2.2.1
          omega
        have hkMerged : k ≠ merged.key := by
          rw [mergedKey]
          omega
        simpa [AllocatorView.takeHeader, AllocatorView.putHeader,
          hkPrevious, hkCurrent, hkMerged] using
          previousMatch.2.1 k hlo hhi
      have relinkedRoot : relinked.sizeCell.alloc =
          (((v.takeHeader current).takeHeader previous).putHeader merged
            ).root.alloc := by
        rw [relinkedEq]
        exact predecessorStored.2.2.2.2.2
      have previousNonneg : 0 ≤ previous := by
        have hwf := predecessorStored.2.2.2.1
        unfold FreeHeaderView.wf at hwf
        calc
          0 ≤ predecessor.sizeCell.off := hwf.1.2.1
          _ = predecessor.key := hwf.2.2.1.symm
          _ = previous := predecessorStored.2.2.1
      have rebuiltAtKey :
          ((((v.takeHeader current).takeHeader previous).putHeader merged
            ).putHeader relinked).StoredChain limit relinked.key := by
        apply AllocatorView.StoredChain.prependAfterPut
          mergedChain canPutRelinked relinkedFields relinkedExtent
          relinkedClear relinkedRoot
        · rw [relinkedKey]
          exact previousNonneg
        · exact previousMatch.2.2.1
        · rw [relinkedKey]
          exact afterPrevious
        · exact mergedChain.head_le_limit
      have rebuilt :
          ((((v.takeHeader current).takeHeader previous).putHeader merged
            ).putHeader relinked).StoredChain limit previous := by
        rw [relinkedKey] at rebuiltAtKey
        exact rebuiltAtKey
      have agree : v.AgreesBelow
          ((((v.takeHeader current).takeHeader previous).putHeader merged
            ).putHeader relinked) previous := by
        refine ⟨rfl, rfl, ?_⟩
        intro k hk
        have hkPrevious : k ≠ previous := by omega
        have hkCurrent : k ≠ current := by omega
        have hkMerged : k ≠ merged.key := by
          rw [mergedKey]
          omega
        have hkRelinked : k ≠ relinked.key := by
          rw [relinkedKey]
          omega
        simp [AllocatorView.takeHeader, AllocatorView.putHeader,
          hkPrevious, hkCurrent, hkMerged, hkRelinked]
      exact priorPath.splice location.1 agree rebuilt

/-- Remove both stored neighbors of an interior insertion location and replace
them with one header at the predecessor key. This is the list-structural core
of three-way predecessor/lease/successor coalescing; the caller supplies the
joined byte extent and its empty interior. -/
theorem AllocatorView.InsertionLocation.coalesceBothAfter
    {v : AllocatorView}
    {limit start key gapSize previous current previousSize
      successorSize next replacementSize : Int}
    (location : v.InsertionLocation
      limit start key gapSize previous current)
    (notHead : current ≠ start)
    (currentNotEnd : current ≠ limit)
    {predecessor successor replacement : FreeHeaderView}
    (predecessorStored : v.storesHeader previous predecessor)
    (predecessorFields : predecessor.hasFields previousSize current)
    (successorStored : v.storesHeader current successor)
    (successorFields : successor.hasFields successorSize next)
    (replacementKey : replacement.key = previous)
    (replacementFields : replacement.hasFields replacementSize next)
    (replacementExtent : replacement.toFree.span.len = replacementSize)
    (replacementClear :
      ((v.takeHeader current).takeHeader previous).clearInterior
        replacement.key replacementSize)
    (replacementRoot : replacement.sizeCell.alloc =
      ((v.takeHeader current).takeHeader previous).root.alloc)
    (canPutReplacement :
      ((v.takeHeader current).takeHeader previous).canPutHeader replacement)
    (replacementNonneg : 0 ≤ replacement.key)
    (replacementMin : freeHeaderBytes ≤ replacementSize)
    (replacementOrder : replacement.key + replacementSize ≤ next) :
    (((v.takeHeader current).takeHeader previous).putHeader replacement
      ).StoredChain limit start := by
  have currentChain : v.StoredChain limit current := location.currentChain
  have currentMatch := currentChain.takeMatchingHead currentNotEnd
    successorStored successorFields
  cases pathEq : location.2.1 with
  | nil => exact (notHead rfl).elim
  | step priorPath predecessorNotEnd pathStored pathFields beforeKey =>
      have previousChain : v.StoredChain limit previous := by
        simpa using priorPath.tail location.1
      have previousMatch := previousChain.takeMatchingHead
        predecessorNotEnd predecessorStored predecessorFields
      have previousCurrent : previous < current := by
        have hfit := previousMatch.2.2.1
        have horder := previousMatch.2.2.2.1
        simp [freeHeaderBytes, u64.layout] at hfit
        omega
      have currentNext : current < next := by
        have hfit := currentMatch.2.2.1
        have horder := currentMatch.2.2.2.1
        simp [freeHeaderBytes, u64.layout] at hfit
        omega
      have bareTail :
          ((v.takeHeader current).takeHeader previous).StoredChain
            limit next := by
        apply currentMatch.2.2.2.2.2.takeHeaderBefore
        omega
      have rebuiltAtKey :
          (((v.takeHeader current).takeHeader previous).putHeader replacement
            ).StoredChain limit replacement.key := by
        apply AllocatorView.StoredChain.prependAfterPut
          bareTail canPutReplacement replacementFields replacementExtent
          replacementClear replacementRoot replacementNonneg replacementMin
          replacementOrder
        exact currentMatch.2.2.2.2.1
      have rebuilt :
          (((v.takeHeader current).takeHeader previous).putHeader replacement
            ).StoredChain limit previous := by
        rw [replacementKey] at rebuiltAtKey
        exact rebuiltAtKey
      have agree : v.AgreesBelow
          (((v.takeHeader current).takeHeader previous).putHeader replacement)
          previous := by
        refine ⟨rfl, rfl, ?_⟩
        intro k hk
        have hkPrevious : k ≠ previous := by omega
        have hkCurrent : k ≠ current := by omega
        have hkReplacement : k ≠ replacement.key := by
          rw [replacementKey]
          omega
        simp [AllocatorView.takeHeader, AllocatorView.putHeader,
          hkPrevious, hkCurrent, hkReplacement]
      exact priorPath.splice location.1 agree rebuilt

/-- First-fit together with the runtime predecessor needed by a later unlink.
The location is still read-only: the represented allocator view is exactly the
entry view. -/
def AllocatorView.FirstFitLocation
    (v : AllocatorView)
    (limit start need previous result size next : Int) : Prop :=
  v.StoredChain limit start ∧
  v.RejectedPath limit need start previous result ∧
  ((result = limit ∧ size = 0 ∧ next = limit) ∨
    ∃ header,
      v.storesHeader result header ∧
      header.hasFields size next ∧
      need ≤ size)

theorem AllocatorView.FirstFitLocation.found
    {v : AllocatorView}
    {limit start need previous result size next : Int}
    {header : FreeHeaderView}
    (chain : v.StoredChain limit start)
    (path : v.RejectedPath limit need start previous result)
    (stored : v.storesHeader result header)
    (fields : header.hasFields size next)
    (fits : need ≤ size) :
    v.FirstFitLocation limit start need previous result size next := by
  exact ⟨chain, path, Or.inr ⟨header, stored, fields, fits⟩⟩

theorem AllocatorView.FirstFitLocation.notFound
    {v : AllocatorView} {limit start need previous : Int}
    (chain : v.StoredChain limit start)
    (path : v.RejectedPath limit need start previous limit) :
    v.FirstFitLocation limit start need previous limit 0 limit := by
  exact ⟨chain, path, Or.inl ⟨rfl, rfl, rfl⟩⟩

theorem AllocatorView.FirstFitLocation.toFirstFit
    {v : AllocatorView}
    {limit start need previous result size next : Int}
    (location : v.FirstFitLocation
      limit start need previous result size next) :
    v.FirstFit limit start need result := by
  refine ⟨location.1, location.2.1.toPrefix, ?_⟩
  cases location.2.2 with
  | inl missing => exact Or.inl missing.1
  | inr found =>
      exact Or.inr ⟨found.choose, size, next,
        found.choose_spec.1, found.choose_spec.2.1,
        found.choose_spec.2.2⟩

theorem AllocatorView.FirstFitLocation.resultChain
    {v : AllocatorView}
    {limit start need previous result size next : Int}
    (location : v.FirstFitLocation
      limit start need previous result size next) :
    v.StoredChain limit result := by
  exact location.2.1.tail location.1

theorem AllocatorView.FirstFitLocation.foundData
    {v : AllocatorView}
    {limit start need previous result size next : Int}
    (location : v.FirstFitLocation
      limit start need previous result size next)
    (notEnd : result ≠ limit) :
    ∃ header,
      v.storesHeader result header ∧
      header.hasFields size next ∧ need ≤ size := by
  cases location.2.2 with
  | inl missing => exact (notEnd missing.1).elim
  | inr found => exact found

theorem AllocatorView.FirstFitLocation.predecessor
    {v : AllocatorView}
    {limit start need previous result size next : Int}
    (location : v.FirstFitLocation
      limit start need previous result size next)
    (notHead : result ≠ start) :
    ∃ header size,
      v.storesHeader previous header ∧
      header.hasFields size result ∧
      size < need := by
  exact location.2.1.predecessor notHead

theorem AllocatorView.FirstFitLocation.predecessorChain
    {v : AllocatorView}
    {limit start need previous result size next : Int}
    (location : v.FirstFitLocation
      limit start need previous result size next)
    (notHead : result ≠ start) :
    v.StoredChain limit previous := by
  cases location.2.1 with
  | nil => exact (notHead rfl).elim
  | step priorPath notEnd stored fields rejected =>
      exact priorPath.tail location.1

theorem AllocatorView.FirstFitLocation.predecessorNotEnd
    {v : AllocatorView}
    {limit start need previous result size next : Int}
    (location : v.FirstFitLocation
      limit start need previous result size next)
    (notHead : result ≠ start) : previous ≠ limit := by
  cases location.2.1 with
  | nil => exact (notHead rfl).elim
  | step priorPath notEnd stored fields rejected => exact notEnd

theorem AllocatorView.FirstFitLocation.predecessorBefore
    {v : AllocatorView}
    {limit start need previous result size next : Int}
    (location : v.FirstFitLocation
      limit start need previous result size next)
    (notHead : result ≠ start) : previous < result := by
  obtain ⟨header, previousSize, stored, fields, rejected⟩ :=
    location.predecessor notHead
  have matched := location.predecessorChain notHead |>.takeMatchingHead
    (location.predecessorNotEnd notHead) stored fields
  have hfit := matched.2.2.1
  have horder := matched.2.2.2.1
  simp [freeHeaderBytes, u64.layout] at hfit
  omega

/-- Once allocation has rebuilt a non-head predecessor, its untouched prefix
also supplies the exact address-order location needed to return the client
extent. This factors the common whole/split `returnableIn` proof. -/
theorem AllocatorView.FirstFitLocation.replacementInsertionLocation
    {v w : AllocatorView}
    {limit start need previous current size next : Int}
    (location : v.FirstFitLocation
      limit start need previous current size next)
    (notHead : current ≠ start)
    {endpoint leaseSize previousSize : Int}
    {predecessor : FreeHeaderView}
    (finalChain : w.StoredChain limit start)
    (agree : v.AgreesBelow w previous)
    (predecessorStored : w.storesHeader previous predecessor)
    (predecessorFields : predecessor.hasFields previousSize endpoint)
    (afterPrevious : previous + previousSize ≤ current)
    (beforeEndpoint : current + leaseSize ≤ endpoint) :
    w.InsertionLocation limit start current leaseSize previous endpoint := by
  cases pathEq : location.2.1 with
  | nil => exact (notHead rfl).elim
  | step priorPath predecessorNotEnd originalStored originalFields rejected =>
      have previousBeforeCurrent : previous < current :=
        location.predecessorBefore notHead
      have oldBeforePrevious := priorPath.toBeforePath location.1
      have oldBeforeCurrent :
          v.BeforePath limit current start _ previous :=
        oldBeforePrevious.mono (by omega)
      have finalBeforePrevious :
          w.BeforePath limit current start _ previous :=
        oldBeforeCurrent.transport location.1 agree
      have finalPath :
          w.BeforePath limit current start previous endpoint :=
        AllocatorView.BeforePath.step finalBeforePrevious
          predecessorNotEnd predecessorStored predecessorFields
          previousBeforeCurrent
      exact AllocatorView.InsertionLocation.after
        finalChain finalPath beforeEndpoint predecessorStored
        predecessorFields afterPrevious

/-- Unlink a non-head first-fit result after its exact header has been taken.
The predecessor is rebuilt with the same extent and a link to the selected
node's successor. The untouched rejected prefix is then spliced onto that
rebuilt tail, yielding a chain from the original head. -/
theorem AllocatorView.FirstFitLocation.unlinkAfter
    {v : AllocatorView}
    {limit start need previous current size next previousSize : Int}
    (location : v.FirstFitLocation
      limit start need previous current size next)
    (currentNotEnd : current ≠ limit)
    (notHead : current ≠ start)
    {selected predecessor relinked : FreeHeaderView}
    (selectedStored : v.storesHeader current selected)
    (selectedFields : selected.hasFields size next)
    (predecessorStored : v.storesHeader previous predecessor)
    (predecessorFields : predecessor.hasFields previousSize current)
    (relinkedEq : relinked =
      predecessor.clearFields.putFields previousSize next)
    (canPut : ((v.takeHeader current).takeHeader previous).canPutHeader
      relinked) :
    (((v.takeHeader current).takeHeader previous).putHeader relinked).StoredChain
      limit start := by
  have currentChain : v.StoredChain limit current :=
    location.resultChain
  have currentMatch := currentChain.takeMatchingHead currentNotEnd
    selectedStored selectedFields
  cases pathEq : location.2.1 with
  | nil => exact (notHead rfl).elim
  | step priorPath predecessorNotEnd pathStored pathFields rejected =>
      have previousChain : v.StoredChain limit previous := by
        simpa using priorPath.tail location.1
      have previousMatch := previousChain.takeMatchingHead
        predecessorNotEnd predecessorStored predecessorFields
      have previousCurrent : previous < current := by
        have hfit := previousMatch.2.2.1
        have horder := previousMatch.2.2.2.1
        simp [freeHeaderBytes, u64.layout] at hfit
        omega
      have currentNext : current < next := by
        have hfit := currentMatch.2.2.1
        have horder := currentMatch.2.2.2.1
        simp [freeHeaderBytes, u64.layout] at hfit
        omega
      have tailBase :
          ((v.takeHeader current).takeHeader previous).StoredChain
            limit next := by
        apply currentMatch.2.2.2.2.2.takeHeaderBefore
        omega
      have relinkedKey : relinked.key = previous := by
        rw [relinkedEq]
        exact predecessorStored.2.2.1
      have relinkedFields : relinked.hasFields previousSize next := by
        simp [relinkedEq, FreeHeaderView.hasFields,
          FreeHeaderView.clearFields, FreeHeaderView.putFields]
      have relinkedExtent : relinked.toFree.span.len = previousSize := by
        rw [relinkedEq]
        simpa using previousMatch.1
      have relinkedClear :
          ((v.takeHeader current).takeHeader previous).clearInterior
            relinked.key previousSize := by
        rw [relinkedKey]
        intro k hlo hhi
        have hkPrevious : k ≠ previous := by omega
        have hkCurrent : k ≠ current := by
          have horder := previousMatch.2.2.2.1
          omega
        simpa [AllocatorView.takeHeader, hkPrevious, hkCurrent] using
          previousMatch.2.1 k hlo hhi
      have relinkedRoot :
          relinked.sizeCell.alloc =
            ((v.takeHeader current).takeHeader previous).root.alloc := by
        rw [relinkedEq]
        exact predecessorStored.2.2.2.2.2
      have previousNonneg : 0 ≤ previous := by
        have hwf := predecessorStored.2.2.2.1
        unfold FreeHeaderView.wf at hwf
        calc
          0 ≤ predecessor.sizeCell.off := hwf.1.2.1
          _ = predecessor.key := hwf.2.2.1.symm
          _ = previous := predecessorStored.2.2.1
      have rebuilt :
          (((v.takeHeader current).takeHeader previous).putHeader relinked).StoredChain
            limit previous := by
        have rebuiltAtKey :
            (((v.takeHeader current).takeHeader previous).putHeader relinked).StoredChain
              limit relinked.key := by
          apply AllocatorView.StoredChain.prependAfterPut
            tailBase canPut relinkedFields relinkedExtent relinkedClear
            relinkedRoot
          · rw [relinkedKey]
            exact previousNonneg
          · exact previousMatch.2.2.1
          · have hprevOrder := previousMatch.2.2.2.1
            rw [relinkedKey]
            omega
          · exact currentMatch.2.2.2.2.1
        rw [relinkedKey] at rebuiltAtKey
        exact rebuiltAtKey
      have agree : v.AgreesBelow
          (((v.takeHeader current).takeHeader previous).putHeader relinked)
          previous := by
        refine ⟨rfl, rfl, ?_⟩
        intro k hk
        have hkPrevious : k ≠ previous := by omega
        have hkCurrent : k ≠ current := by omega
        simp [AllocatorView.takeHeader, AllocatorView.putHeader,
          relinkedKey, hkPrevious, hkCurrent]
      exact priorPath.toPrefix.splice location.1 agree rebuilt

/-- Replace a non-head first-fit result by its split remainder. Both the
selected header and its predecessor have been taken; the suffix header is
parked at `current + need`, then the predecessor is rebuilt to point at it.
The untouched rejected prefix is spliced back onto the two rebuilt nodes. -/
theorem AllocatorView.FirstFitLocation.splitAfter
    {v : AllocatorView}
    {limit start need previous current size next previousSize : Int}
    (location : v.FirstFitLocation
      limit start need previous current size next)
    (currentNotEnd : current ≠ limit)
    (notHead : current ≠ start)
    {selected predecessor remainder relinked : FreeHeaderView}
    (selectedStored : v.storesHeader current selected)
    (selectedFields : selected.hasFields size next)
    (predecessorStored : v.storesHeader previous predecessor)
    (predecessorFields : predecessor.hasFields previousSize current)
    (remainderKey : remainder.key = current + need)
    (remainderFields : remainder.hasFields (size - need) next)
    (remainderExtent : remainder.toFree.span.len = size - need)
    (remainderRoot : remainder.sizeCell.alloc =
      ((v.takeHeader current).takeHeader previous).root.alloc)
    (canPutRemainder :
      ((v.takeHeader current).takeHeader previous).canPutHeader remainder)
    (relinkedEq : relinked =
      predecessor.clearFields.putFields previousSize (current + need))
    (canPutRelinked :
      (((v.takeHeader current).takeHeader previous).putHeader remainder
        ).canPutHeader relinked)
    (requestMin : freeHeaderBytes ≤ need)
    (remainderMin : freeHeaderBytes ≤ size - need) :
    ((((v.takeHeader current).takeHeader previous).putHeader remainder
      ).putHeader relinked).StoredChain limit start := by
  have currentChain : v.StoredChain limit current :=
    location.resultChain
  have currentMatch := currentChain.takeMatchingHead currentNotEnd
    selectedStored selectedFields
  cases pathEq : location.2.1 with
  | nil => exact (notHead rfl).elim
  | step priorPath predecessorNotEnd pathStored pathFields rejected =>
      have previousChain : v.StoredChain limit previous := by
        simpa using priorPath.tail location.1
      have previousMatch := previousChain.takeMatchingHead
        predecessorNotEnd predecessorStored predecessorFields
      have previousCurrent : previous < current := by
        have hfit := previousMatch.2.2.1
        have horder := previousMatch.2.2.2.1
        simp [freeHeaderBytes, u64.layout] at hfit
        omega
      have currentNext : current < next := by
        have hfit := currentMatch.2.2.1
        have horder := currentMatch.2.2.2.1
        simp [freeHeaderBytes, u64.layout] at hfit
        omega
      have bareTail :
          ((v.takeHeader current).takeHeader previous).StoredChain
            limit next := by
        apply currentMatch.2.2.2.2.2.takeHeaderBefore
        omega
      have bareSelectedClear :
          ((v.takeHeader current).takeHeader previous).clearInterior
            current size := by
        intro k hlo hhi
        have hkPrevious : k ≠ previous := by omega
        simpa [AllocatorView.takeHeader, hkPrevious] using
          currentMatch.2.1 k hlo hhi
      have needPositive : 0 < need := by
        simp [freeHeaderBytes, u64.layout] at requestMin
        omega
      have needAtMostSize : need ≤ size := by
        simp [freeHeaderBytes, u64.layout] at remainderMin
        omega
      have remainderClear :
          ((v.takeHeader current).takeHeader previous).clearInterior
            remainder.key (size - need) := by
        rw [remainderKey]
        intro k hlo hhi
        apply bareSelectedClear k
        · omega
        · omega
      have currentNonneg : 0 ≤ current := by
        have hwf := selectedStored.2.2.2.1
        unfold FreeHeaderView.wf at hwf
        calc
          0 ≤ selected.sizeCell.off := hwf.1.2.1
          _ = selected.key := hwf.2.2.1.symm
          _ = current := selectedStored.2.2.1
      have rebuiltRemainder :
          (((v.takeHeader current).takeHeader previous).putHeader remainder
            ).StoredChain limit remainder.key := by
        apply AllocatorView.StoredChain.prependAfterPut
          bareTail canPutRemainder remainderFields remainderExtent
          remainderClear remainderRoot
        · rw [remainderKey]
          omega
        · exact remainderMin
        · rw [remainderKey]
          have horder := currentMatch.2.2.2.1
          omega
        · exact currentMatch.2.2.2.2.1
      have relinkedKey : relinked.key = previous := by
        rw [relinkedEq]
        exact predecessorStored.2.2.1
      have relinkedFields :
          relinked.hasFields previousSize remainder.key := by
        rw [remainderKey, relinkedEq]
        simp [FreeHeaderView.hasFields, FreeHeaderView.clearFields,
          FreeHeaderView.putFields]
      have relinkedExtent : relinked.toFree.span.len = previousSize := by
        rw [relinkedEq]
        simpa using previousMatch.1
      have relinkedClear :
          (((v.takeHeader current).takeHeader previous).putHeader remainder
            ).clearInterior relinked.key previousSize := by
        rw [relinkedKey]
        intro k hlo hhi
        have hkPrevious : k ≠ previous := by omega
        have hkCurrent : k ≠ current := by
          have horder := previousMatch.2.2.2.1
          omega
        have hkRemainder : k ≠ remainder.key := by
          rw [remainderKey]
          omega
        simpa [AllocatorView.takeHeader, AllocatorView.putHeader,
          hkPrevious, hkCurrent, hkRemainder] using
          previousMatch.2.1 k hlo hhi
      have relinkedRoot :
          relinked.sizeCell.alloc =
            (((v.takeHeader current).takeHeader previous).putHeader remainder
              ).root.alloc := by
        rw [relinkedEq]
        exact predecessorStored.2.2.2.2.2
      have previousNonneg : 0 ≤ previous := by
        have hwf := predecessorStored.2.2.2.1
        unfold FreeHeaderView.wf at hwf
        calc
          0 ≤ predecessor.sizeCell.off := hwf.1.2.1
          _ = predecessor.key := hwf.2.2.1.symm
          _ = previous := predecessorStored.2.2.1
      have rebuiltAtKey :
          ((((v.takeHeader current).takeHeader previous).putHeader remainder
            ).putHeader relinked).StoredChain limit relinked.key := by
        apply AllocatorView.StoredChain.prependAfterPut
          rebuiltRemainder canPutRelinked relinkedFields relinkedExtent
          relinkedClear relinkedRoot
        · rw [relinkedKey]
          exact previousNonneg
        · exact previousMatch.2.2.1
        · rw [relinkedKey, remainderKey]
          have horder := previousMatch.2.2.2.1
          omega
        · rw [remainderKey]
          have horder := currentMatch.2.2.2.1
          have hbound := currentMatch.2.2.2.2.1
          omega
      have rebuilt :
          ((((v.takeHeader current).takeHeader previous).putHeader remainder
            ).putHeader relinked).StoredChain limit previous := by
        rw [relinkedKey] at rebuiltAtKey
        exact rebuiltAtKey
      have agree : v.AgreesBelow
          ((((v.takeHeader current).takeHeader previous).putHeader remainder
            ).putHeader relinked) previous := by
        refine ⟨rfl, rfl, ?_⟩
        intro k hk
        have hkPrevious : k ≠ previous := by omega
        have hkCurrent : k ≠ current := by omega
        have hkRemainder : k ≠ remainder.key := by
          rw [remainderKey]
          omega
        have hkRelinked : k ≠ relinked.key := by
          rw [relinkedKey]
          omega
        simp [AllocatorView.takeHeader, AllocatorView.putHeader,
          hkPrevious, hkCurrent, hkRemainder, hkRelinked]
      exact priorPath.toPrefix.splice location.1 agree rebuilt

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

@[simp] theorem FreeBlockView.toHeader_putFields_toFree_span_len
    (v : FreeBlockView) (size next : Int) :
    (v.toHeader.putFields size next).toFree.span.len = v.span.len := by
  simp [FreeBlockView.toHeader, FreeHeaderView.putFields,
    FreeHeaderView.toFree, FreeHeaderView.rawCell,
    SpanView.cat, SpanView.drop, freeHeaderBytes, u64.layout]
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

theorem AllocatorView.initialStoredHeaderRoundTrip_complete
    (allocator : Int) (root : SpanView) (size next : Int) :
    let initial := AllocatorView.initial allocator root
    let block := initial.takeFree 0
    let header := block.toHeader.putFields size next
    let parked := (initial.take 0).putHeader header
    let extracted := parked.takeHeader 0
    let returned := (parked.headerAt 0).clearFields.toFree
    (extracted.putFree returned).complete := by
  simp [AllocatorView.complete, AllocatorView.releaseSpan,
    SpanView.sameExtent, AllocatorView.initial, AllocatorView.takeFree,
    AllocatorView.leaseAt, AllocatorView.take, AllocatorView.putFree,
    AllocatorView.put, AllocatorView.putHeader, AllocatorView.takeHeader,
    AllocatorView.headerAt, FreeBlockView.toHeader,
    FreeHeaderView.putFields, FreeHeaderView.clearFields,
    FreeHeaderView.toFree, FreeHeaderView.rawCell,
    FreeBlockView.toLease, BlockLeaseView.toFree,
    freeHeaderBytes, u64.layout]
  constructor
  · omega
  · intro k hk
    simp [hk]

/-- Normalize the two-node lifecycle used by the first real free-list walk:
split the initial root, park initialized headers for suffix then prefix,
extract and clear both, rejoin their exact extents, and return the root. -/
theorem AllocatorView.initialSplitStoredHeadersRoundTrip_complete
    (allocator : Int) (root : SpanView) (n : Int)
    (leftSize leftNext rightSize rightNext : Int) (hn : n ≠ 0) :
    let initial := AllocatorView.initial allocator root
    let whole := initial.takeFree 0
    let left := whole.prefix n
    let right := whole.suffix n
    let leftHeader := left.toHeader.putFields leftSize leftNext
    let rightHeader := right.toHeader.putFields rightSize rightNext
    let parkedRight := (initial.take 0).putHeader rightHeader
    let parkedBoth := parkedRight.putHeader leftHeader
    let withoutLeft := parkedBoth.takeHeader 0
    let returnedLeft := (parkedBoth.headerAt 0).clearFields.toFree
    let withoutBoth := withoutLeft.takeHeader n
    let returnedRight := (withoutLeft.headerAt n).clearFields.toFree
    let joined := returnedLeft.join returnedRight
    (withoutBoth.putFree joined).complete := by
  simp [AllocatorView.complete, AllocatorView.releaseSpan,
    SpanView.sameExtent, AllocatorView.initial, AllocatorView.takeFree,
    AllocatorView.leaseAt, AllocatorView.take, AllocatorView.putFree,
    AllocatorView.put, AllocatorView.putHeader, AllocatorView.takeHeader,
    AllocatorView.headerAt, FreeBlockView.prefix, FreeBlockView.suffix,
    FreeBlockView.join, FreeBlockView.toHeader, FreeHeaderView.putFields,
    FreeHeaderView.clearFields, FreeHeaderView.toFree,
    FreeHeaderView.rawCell, FreeBlockView.toLease,
    BlockLeaseView.toFree, freeHeaderBytes, u64.layout, hn]
  constructor
  · omega
  · constructor
    · intro k hk
      simp [hk]
    · intro k hkn hk0
      simp [hkn, hk0]

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
    (htake : v.canTakeFree key) (hn : 0 < n ∧ n < (v.takeFree key).span.len)
    (habsent : v.headers ((v.takeFree key).suffix n).key = none) :
    (v.take key).canPutFree ((v.takeFree key).suffix n) := by
  constructor
  · rfl
  constructor
  · exact FreeBlockView.suffix_wf htake.2 hn.2
  · exact habsent

@[simp] theorem AllocatorView.putFree_canTake
    (v : AllocatorView) (block : FreeBlockView)
    (hput : v.canPutFree block) :
    (v.putFree block).canTake block.key := by
  constructor
  · simp [AllocatorView.putFree, AllocatorView.put, FreeBlockView.toLease]
  · simpa [AllocatorView.putFree, AllocatorView.put] using hput.2.2

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
  · exact v.putFree_canTake block hput
  · rw [AllocatorView.putFree_takeFree v block hput.1]
    exact hput.2.1

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
