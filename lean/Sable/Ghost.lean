/-
Sable prelude: ghost-type aliases so clause authors can write the
design-doc surface syntax (`seq i32`, `int`, `nat`) while everything
remains the uniform Int representation underneath (design §2.1).
The `iN`/`uN` type aliases coexist with the `iN.min`/`uN.max` bound
constants — Lean resolves dotted names as declarations first.
-/

import Sable.Seq

namespace Sable

abbrev int : Type := Int
abbrev nat : Type := Nat
abbrev seq : Type → Type := Sable.Seq

abbrev u8 : Type := Int
abbrev u16 : Type := Int
abbrev u32 : Type := Int
abbrev u64 : Type := Int
abbrev i8 : Type := Int
abbrev i16 : Type := Int
abbrev i32 : Type := Int
abbrev i64 : Type := Int

end Sable
