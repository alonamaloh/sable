/-
Sable prelude: the ghost sequence type that borrowed arrays lift to
(design §2.1). Everything is `Int`, matching the uniform "program values
lift to ℤ" rule: `len : Int` comes with the fact `0 ≤ len` as a
hypothesis at every use, and `get : Int → α` returns junk outside
`[0, len)` — bounds VCs keep program accesses inside, and specification
quantifiers over indices carry explicit `0 ≤ k` guards.

(The alternative — `Nat`-typed lengths and indices — does not elaborate
against Int-lifted program values: in `∀ k, k < lo → a.get k < key` Lean
commits `k : Int` at the comparison before ever seeing `get`. All-Int
with guards is uniform and coercion-free; decided during M1, 2026-08-08.)
-/

namespace Sable

structure Seq (α : Type) where
  len : Int
  get : Int → α

end Sable
