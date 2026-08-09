import Sable.Bounds

/-
Sable prelude: the automation portfolio.

Every VC the compiler emits is a theorem proved `by sable_auto` (unless a
`discharge` block overrides it). The portfolio is deliberately ordered:
cheap closers first, then normalization + omega (the workhorse for range
and overflow VCs), then simp_all, then grind.

`sable_norm` unfolds the Sable bound constants (`u32.max` etc.) to literals
everywhere, since `omega` treats unknown constants as opaque.
-/

namespace Sable

syntax "sable_norm" : tactic

macro_rules
  | `(tactic| sable_norm) =>
    `(tactic| simp only [Sable.u8.max, Sable.u16.max, Sable.u32.max, Sable.u64.max,
        Sable.i8.min, Sable.i8.max, Sable.i16.min, Sable.i16.max,
        Sable.i32.min, Sable.i32.max, Sable.i64.min, Sable.i64.max] at *)

syntax "sable_auto" : tactic

macro_rules
  | `(tactic| sable_auto) =>
    `(tactic| first
        | assumption
        | rfl
        | ((try sable_norm) <;> omega)
        | ((try sable_norm) <;> simp_all)
        | grind)

end Sable
