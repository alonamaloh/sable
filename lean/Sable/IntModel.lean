/-
Sable prelude: the abstract model of an integer type (ADR 0009 —
concepts). A template type parameter `T` verifies against an arbitrary
`IntModel` satisfying `wf` (bounds and layout facts true of all eight program types) plus
the template's declared `requires` preconditions; instantiation supplies
the concrete model and its once-proven `wf` lemma. Clause text like
`T.min ≤ x` elaborates as-is via field projection — verbatim splice
preserved.
-/
import Sable.Bounds
import Sable.Layout

namespace Sable

structure IntModel where
  min : Int
  max : Int
  layout : Layout

/-- What every Sable integer type satisfies. -/
@[simp] def IntModel.wf (t : IntModel) : Prop :=
  t.min ≤ 0 ∧ 0 < t.max ∧ i64.min ≤ t.min ∧ t.max ≤ u64.max ∧ t.layout.wf

def u8.model  : IntModel := ⟨0, u8.max, Sable.u8.layout⟩
def u16.model : IntModel := ⟨0, u16.max, Sable.u16.layout⟩
def u32.model : IntModel := ⟨0, u32.max, Sable.u32.layout⟩
def u64.model : IntModel := ⟨0, u64.max, Sable.u64.layout⟩
def i8.model  : IntModel := ⟨i8.min, i8.max, Sable.i8.layout⟩
def i16.model : IntModel := ⟨i16.min, i16.max, Sable.i16.layout⟩
def i32.model : IntModel := ⟨i32.min, i32.max, Sable.i32.layout⟩
def i64.model : IntModel := ⟨i64.min, i64.max, Sable.i64.layout⟩

theorem u8.model_wf : Sable.u8.model.wf := by
  simp [IntModel.wf, Sable.u8.model, Sable.u8.layout, u8.max, i64.min, u64.max, Layout.wf]
  exact ⟨0, rfl⟩
theorem u16.model_wf : Sable.u16.model.wf := by
  simp [IntModel.wf, Sable.u16.model, Sable.u16.layout, u16.max, i64.min, u64.max, Layout.wf]
  exact ⟨1, rfl⟩
theorem u32.model_wf : Sable.u32.model.wf := by
  simp [IntModel.wf, Sable.u32.model, Sable.u32.layout, u32.max, i64.min, u64.max, Layout.wf]
  exact ⟨2, rfl⟩
theorem u64.model_wf : Sable.u64.model.wf := by
  simp [IntModel.wf, Sable.u64.model, Sable.u64.layout, u64.max, i64.min, Layout.wf]
  exact ⟨3, rfl⟩
theorem i8.model_wf : Sable.i8.model.wf := by
  simp [IntModel.wf, Sable.i8.model, Sable.i8.layout, i8.min, i8.max, i64.min, u64.max, Layout.wf]
  exact ⟨0, rfl⟩
theorem i16.model_wf : Sable.i16.model.wf := by
  simp [IntModel.wf, Sable.i16.model, Sable.i16.layout, i16.min, i16.max, i64.min, u64.max, Layout.wf]
  exact ⟨1, rfl⟩
theorem i32.model_wf : Sable.i32.model.wf := by
  simp [IntModel.wf, Sable.i32.model, Sable.i32.layout, i32.min, i32.max, i64.min, u64.max, Layout.wf]
  exact ⟨2, rfl⟩
theorem i64.model_wf : Sable.i64.model.wf := by
  simp [IntModel.wf, Sable.i64.model, Sable.i64.layout, i64.min, i64.max, u64.max, Layout.wf]
  exact ⟨3, rfl⟩

end Sable
