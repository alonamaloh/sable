/-
Sable prelude: ghost-type aliases so clause authors can write the
design-doc surface syntax (`seq i32`, `int`, `nat`).

These are *notation*, not abbrevs, on purpose: an `abbrev int := Int`
leaves a reducible type-synonym in elaborated terms, and `omega` then
fails to recognize `(x : int) ≤ y` as an integer constraint (verified
empirically — the goal displays identically but automation dies).
Notation expands at parse time, leaving no residue.

`i32.max` etc. still resolve to the bound constants in Bounds.lean:
dotted identifiers are single tokens, so the bare-`i32` notation never
fires on them.
-/

import Sable.Seq

namespace Sable

notation "int" => Int
notation "nat" => Nat
notation "seq" => Sable.Seq

notation "u8" => Int
notation "u16" => Int
notation "u32" => Int
notation "u64" => Int
notation "i8" => Int
notation "i16" => Int
notation "i32" => Int
notation "i64" => Int

end Sable
