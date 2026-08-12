/-
Sable prelude: option accessors (ADR 0008). The program language
consumes options C++-style — `r.is_some` / `r.value` — never by pattern
matching. `value` is junk-on-none (`getD default`, hence `false` for Bool),
mirroring `Seq.get`'s junk-off-range convention: a someness VC keeps
verified code away from the junk, and `sable test` traps there. The same
dot-notation works in clause text, so specs can be written accessor-style too
(`result.is_some → result.value = 7`).
-/

namespace Option

@[simp] def is_some {α : Type} (o : Option α) : Prop := o ≠ none

@[simp] def value {α : Type} [Inhabited α] (o : Option α) : α := o.getD default

@[simp] theorem value_some {α : Type} [Inhabited α] (x : α) : (some x).value = x := rfl

@[simp] theorem is_some_some {α : Type} (x : α) : (some x).is_some := by
  simp [is_some]

@[simp] theorem not_is_some_none {α : Type} : ¬ (none : Option α).is_some := by
  intro h
  exact h rfl

theorem eq_some_of_is_some {α : Type} [Inhabited α] {o : Option α} (h : o.is_some) :
    o = some o.value := by
  cases o with
  | none => exact absurd rfl h
  | some x => rfl

end Option
