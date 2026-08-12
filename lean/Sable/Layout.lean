/-
Compiler-established storage layout (ADR 0032).

Layout is proof vocabulary, not a program value: generic contracts see it
through `T.layout`, while monomorphic contracts use names such as
`u64.layout`. Nothing here describes a byte representation.
-/

namespace Sable

structure Layout where
  size : Int
  align : Int
  deriving DecidableEq, Repr

/-- Minimum laws required before a type may inhabit abstract typed storage. -/
def Layout.wf (l : Layout) : Prop :=
  0 < l.size ∧ 0 < l.align ∧ ∃ k : Nat, l.align = (2 : Int) ^ k

@[simp] theorem Layout.wf_iff (l : Layout) :
    l.wf ↔ 0 < l.size ∧ 0 < l.align ∧ ∃ k : Nat, l.align = (2 : Int) ^ k := Iff.rfl

def u8.layout  : Layout := ⟨1, 1⟩
def i8.layout  : Layout := ⟨1, 1⟩
def u16.layout : Layout := ⟨2, 2⟩
def i16.layout : Layout := ⟨2, 2⟩
def u32.layout : Layout := ⟨4, 4⟩
def i32.layout : Layout := ⟨4, 4⟩
def u64.layout : Layout := ⟨8, 8⟩
def i64.layout : Layout := ⟨8, 8⟩

@[simp] theorem u8.layout_size : Sable.u8.layout.size = 1 := rfl
@[simp] theorem u8.layout_align : Sable.u8.layout.align = 1 := rfl
@[simp] theorem i8.layout_size : Sable.i8.layout.size = 1 := rfl
@[simp] theorem i8.layout_align : Sable.i8.layout.align = 1 := rfl
@[simp] theorem u16.layout_size : Sable.u16.layout.size = 2 := rfl
@[simp] theorem u16.layout_align : Sable.u16.layout.align = 2 := rfl
@[simp] theorem i16.layout_size : Sable.i16.layout.size = 2 := rfl
@[simp] theorem i16.layout_align : Sable.i16.layout.align = 2 := rfl
@[simp] theorem u32.layout_size : Sable.u32.layout.size = 4 := rfl
@[simp] theorem u32.layout_align : Sable.u32.layout.align = 4 := rfl
@[simp] theorem i32.layout_size : Sable.i32.layout.size = 4 := rfl
@[simp] theorem i32.layout_align : Sable.i32.layout.align = 4 := rfl
@[simp] theorem u64.layout_size : Sable.u64.layout.size = 8 := rfl
@[simp] theorem u64.layout_align : Sable.u64.layout.align = 8 := rfl
@[simp] theorem i64.layout_size : Sable.i64.layout.size = 8 := rfl
@[simp] theorem i64.layout_align : Sable.i64.layout.align = 8 := rfl

theorem u8.layout_wf : u8.layout.wf := by
  refine ⟨by decide, by decide, ⟨0, rfl⟩⟩
theorem i8.layout_wf : i8.layout.wf := by
  refine ⟨by decide, by decide, ⟨0, rfl⟩⟩
theorem u16.layout_wf : u16.layout.wf := by
  refine ⟨by decide, by decide, ⟨1, rfl⟩⟩
theorem i16.layout_wf : i16.layout.wf := by
  refine ⟨by decide, by decide, ⟨1, rfl⟩⟩
theorem u32.layout_wf : u32.layout.wf := by
  refine ⟨by decide, by decide, ⟨2, rfl⟩⟩
theorem i32.layout_wf : i32.layout.wf := by
  refine ⟨by decide, by decide, ⟨2, rfl⟩⟩
theorem u64.layout_wf : u64.layout.wf := by
  refine ⟨by decide, by decide, ⟨3, rfl⟩⟩
theorem i64.layout_wf : i64.layout.wf := by
  refine ⟨by decide, by decide, ⟨3, rfl⟩⟩

end Sable
