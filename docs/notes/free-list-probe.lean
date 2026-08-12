/-
U8c probe — the resource shape forced by allocator block leases.

Run from `lean/`:

  lake env lean ../docs/notes/free-list-probe.lean

This deliberately tests the authority algebra before the compiler surface.
The allocator is one affine aggregate token whose pure view indexes free
spans. Taking one key returns a refined BlockLease (the byte authority itself,
not a marker beside RawSpan); putting it back reverses the partition. A leased
typed cell retains allocator/key identity, which is the fact a plain
PointsTo<u64> would lose.
-/

import Sable
open Sable

set_option linter.unusedVariables false

structure BlockLeaseView where
  allocator : Int
  key : Int
  span : SpanView

structure AllocatorView where
  allocator : Int
  free : Int → Option SpanView

inductive AllocCap where
  | byte : Int → Int → AllocCap
  | returnKey : Int → Int → AllocCap

def spanOwnsAllocCap (v : SpanView) : AllocCap → Prop
  | .byte a k => a = v.alloc ∧ v.off ≤ k ∧ k < v.off + v.len
  | .returnKey _ _ => False

def BlockLeaseView.owns (v : BlockLeaseView) : AllocCap → Prop
  | .byte a k => spanOwnsAllocCap v.span (.byte a k)
  | .returnKey owner key => owner = v.allocator ∧ key = v.key

def AllocatorView.owns (v : AllocatorView) (c : AllocCap) : Prop :=
  ∃ key span, v.free key = some span ∧
    (spanOwnsAllocCap span c ∨ c = .returnKey v.allocator key)

def Disjoint (p q : AllocCap → Prop) : Prop :=
  ∀ c, ¬ (p c ∧ q c)

def AllocatorView.take (v : AllocatorView) (key : Int) : AllocatorView :=
  { v with free := fun k => if k = key then none else v.free k }

def AllocatorView.put (v : AllocatorView) (lease : BlockLeaseView) : AllocatorView :=
  { v with free := fun k => if k = lease.key then some lease.span else v.free k }

theorem take_removes_key {v : AllocatorView} {key : Int} :
    (v.take key).free key = none := by
  simp [AllocatorView.take]

theorem take_keeps_other {v : AllocatorView} {key other : Int} (hne : other ≠ key) :
    (v.take key).free other = v.free other := by
  simp [AllocatorView.take, hne]

/-- Taking one free entry partitions, rather than duplicates, every capability
owned by that entry. -/
theorem take_partition {v : AllocatorView} {key : Int} {span : SpanView}
    (hentry : v.free key = some span) (c : AllocCap) :
    v.owns c ↔ (v.take key).owns c ∨
      (BlockLeaseView.mk v.allocator key span).owns c := by
  constructor
  · rintro ⟨j, s, hs, hcap⟩
    by_cases hj : j = key
    · subst j
      rw [hentry] at hs
      cases hs
      right
      cases c <;>
        simp_all [BlockLeaseView.owns, spanOwnsAllocCap]
    · left
      exact ⟨j, s, by simpa [AllocatorView.take, hj] using hs, hcap⟩
  · rintro (hrest | hlease)
    · obtain ⟨j, s, hs, hcap⟩ := hrest
      have hj : j ≠ key := by
        intro he
        subst j
        simp [AllocatorView.take] at hs
      exact ⟨j, s, by simpa [AllocatorView.take, hj] using hs, hcap⟩
    · exact ⟨key, span, hentry, by
        cases c with
        | byte a k => exact Or.inl hlease
        | returnKey owner k =>
            rcases hlease with ⟨rfl, rfl⟩
            exact Or.inr rfl⟩

/-- The residual aggregate and returned lease cannot both own a capability. -/
theorem take_disjoint {v : AllocatorView} {key : Int} {span : SpanView}
    (hentry : v.free key = some span)
    (hkeys : ∀ j s, v.free j = some s → j ≠ key →
      Disjoint (spanOwnsAllocCap s) (spanOwnsAllocCap span)) :
    Disjoint (v.take key).owns (BlockLeaseView.mk v.allocator key span).owns := by
  intro c
  rintro ⟨⟨j, s, hs, hcap⟩, hlease⟩
  have hj : j ≠ key := by
    intro he
    subst j
    simp [AllocatorView.take] at hs
  have hs0 : v.free j = some s := by
    simpa [AllocatorView.take, hj] using hs
  cases c with
  | byte a k =>
      rcases hcap with hbytes | hslot
      · exact hkeys j s hs0 hj _ ⟨hbytes, hlease⟩
      · cases hslot
  | returnKey owner k =>
      rcases hlease with ⟨rfl, rfl⟩
      rcases hcap with hbytes | hslot
      · exact hbytes.elim
      · cases hslot
        exact hj rfl

theorem put_after_take {v : AllocatorView} {key : Int} {span : SpanView}
    (hentry : v.free key = some span) :
    (v.take key).put ⟨v.allocator, key, span⟩ = v := by
  cases v with
  | mk allocator free =>
      simp only [AllocatorView.put, AllocatorView.take]
      congr 1
      funext k
      by_cases hk : k = key
      · subst k
        simp only [if_pos]
        exact hentry.symm
      · simp [hk]

/-! Typed-role preservation. The leased typed cell is a refinement of the
lease, not a plain PointsToView: allocator and key survive the role change. -/

structure LeasedPointsToU64View where
  allocator : Int
  key : Int
  cell : PointsToView Int

def LeasedPointsToU64View.owns (v : LeasedPointsToU64View) : AllocCap → Prop
  | .byte a k =>
      a = v.cell.alloc ∧ v.cell.off ≤ k ∧
        k < v.cell.off + v.cell.layout.size
  | .returnKey owner key => owner = v.allocator ∧ key = v.key

def BlockLeaseView.intoCellU64 (v : BlockLeaseView) : LeasedPointsToU64View :=
  { allocator := v.allocator, key := v.key,
    cell := { alloc := v.span.alloc, off := v.span.off,
              layout := u64.layout, state := .uninit } }

theorem lease_cell_identity (v : BlockLeaseView) :
    (v.intoCellU64).allocator = v.allocator ∧
    (v.intoCellU64).key = v.key := by
  exact ⟨rfl, rfl⟩

theorem lease_cell_owns_iff (v : BlockLeaseView)
    (hlen : v.span.len = u64.layout.size) (c : AllocCap) :
    v.intoCellU64.owns c ↔ v.owns c := by
  cases c with
  | byte a k => simp [BlockLeaseView.intoCellU64, BlockLeaseView.owns,
      LeasedPointsToU64View.owns, spanOwnsAllocCap, hlen]
  | returnKey owner key => rfl

#check take_partition
#check take_disjoint
#check put_after_take
#check lease_cell_owns_iff
