/-
Sable prelude: the abstract model of an integer type (ADR 0009 —
concepts). A template type parameter `T` verifies against an arbitrary
`IntModel` satisfying `wf` (facts true of all eight program types) plus
the template's declared `requires` preconditions; instantiation supplies
the concrete model and its once-proven `wf` lemma. Clause text like
`T.min ≤ x` elaborates as-is via field projection — verbatim splice
preserved.
-/
import Sable.Bounds

namespace Sable

structure IntModel where
  min : Int
  max : Int

/-- What every Sable integer type satisfies. -/
@[simp] def IntModel.wf (t : IntModel) : Prop :=
  t.min ≤ 0 ∧ 0 < t.max ∧ i64.min ≤ t.min ∧ t.max ≤ u64.max

def u8.model  : IntModel := ⟨0, u8.max⟩
def u16.model : IntModel := ⟨0, u16.max⟩
def u32.model : IntModel := ⟨0, u32.max⟩
def u64.model : IntModel := ⟨0, u64.max⟩
def i8.model  : IntModel := ⟨i8.min, i8.max⟩
def i16.model : IntModel := ⟨i16.min, i16.max⟩
def i32.model : IntModel := ⟨i32.min, i32.max⟩
def i64.model : IntModel := ⟨i64.min, i64.max⟩

theorem u8.model_wf : u8.model.wf := by
  simp only [IntModel.wf, u8.model, u8.max, i64.min, u64.max]; omega
theorem u16.model_wf : u16.model.wf := by
  simp only [IntModel.wf, u16.model, u16.max, i64.min, u64.max]; omega
theorem u32.model_wf : u32.model.wf := by
  simp only [IntModel.wf, u32.model, u32.max, i64.min, u64.max]; omega
theorem u64.model_wf : u64.model.wf := by
  simp only [IntModel.wf, u64.model, u64.max, i64.min]; omega
theorem i8.model_wf : i8.model.wf := by
  simp only [IntModel.wf, i8.model, i8.min, i8.max, i64.min, u64.max]; omega
theorem i16.model_wf : i16.model.wf := by
  simp only [IntModel.wf, i16.model, i16.min, i16.max, i64.min, u64.max]; omega
theorem i32.model_wf : i32.model.wf := by
  simp only [IntModel.wf, i32.model, i32.min, i32.max, i64.min, u64.max]; omega
theorem i64.model_wf : i64.model.wf := by
  simp only [IntModel.wf, i64.model, i64.min, i64.max, u64.max]; omega

end Sable
