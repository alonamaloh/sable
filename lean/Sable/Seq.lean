/-
Sable prelude: the ghost sequence type that arrays lift to (design §2.1).
Lengths and indices are always `Int`; the element type is the source array's
proof-domain type (`Int` for integer arrays and `Bool` for Boolean arrays).
`len : Int` comes with the fact `0 ≤ len` as a hypothesis at every use, and
`get : Int → α` returns junk outside `[0, len)` — bounds VCs keep program
accesses inside, and specification quantifiers over indices carry explicit
`0 ≤ k` guards.

(The alternative — `Nat`-typed lengths and indices — does not elaborate
against Int-lifted program values: in `∀ k, k < lo → a.get k < key` Lean
commits `k : Int` at the comparison before ever seeing `get`. All-Int
with guards is uniform and coercion-free.)
-/

namespace Sable

structure Seq (α : Type) where
  len : Int
  get : Int → α

/-- Functional store: the model of `a[i] = v` on `&mut [T]`. Length is
preserved by construction, which is why the generator may assume
`a.len = old a.len` across havoc. -/
def Seq.set (s : Seq α) (i : Int) (v : α) : Seq α :=
  ⟨s.len, fun k => if k = i then v else s.get k⟩

@[simp] theorem Seq.len_set (s : Seq α) (i : Int) (v : α) :
    (s.set i v).len = s.len := rfl

@[simp] theorem Seq.get_set (s : Seq α) (i j : Int) (v : α) :
    (s.set i v).get j = if j = i then v else s.get j := rfl

end Sable
