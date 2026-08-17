/-
Direct executable regressions for owned integer and Boolean SVM arrays.

These pin homogeneous payload tags, including for empty arrays, as well as
the normative left-to-right order: index evaluation, value evaluation,
payload compatibility, array lookup, then bounds/capacity geometry.
-/

import Sable.SVMEval

namespace Sable
namespace SVM

private def outcome (cap : Int) (k : List Stmt) : String :=
  (run Prog.empty cap 1000 (.run k Env.empty [] .empty)).render

private def u64 (n : Int) : Expr := .intLit .u64 n

/- Allocate, read, store, and observe Boolean arrays. -/
#guard outcome 100
  [ .assign "a" (.allocArray (u64 3) (.boolLit false)),
    .store "a" (u64 1) (.boolLit true),
    .ret (.index "a" (u64 1)) ]
  = "done bool true"

#guard outcome 100
  [ .assign "a" (.allocArray (u64 3) (.boolLit false)),
    .ret (.len "a") ]
  = "done int 3"

/- Existing integer rendering remains byte-for-byte stable. -/
#guard outcome 100
  [ .assign "a" (.allocArray (u64 2) (u64 7)), .ret (.var "a") ]
  = "done arr [7, 7]"

#guard outcome 100
  [ .assign "a" (.allocArray (u64 2) (.boolLit true)), .ret (.var "a") ]
  = "done arr [true, true]"

/- OOB and OOM remain defined traps for Boolean payloads. -/
#guard outcome 100
  [ .assign "a" (.allocArray (u64 1) (.boolLit false)),
    .ret (.index "a" (u64 1)) ]
  = "trap indexOOB 1 1"

#guard outcome 1
  [ .assign "a" (.allocArray (u64 2) (.boolLit false)) ]
  = "trap oom 2"

/- Invalid allocation initializers are `undef`; the length expression wins
before the initializer, and a valid initializer is evaluated before OOM. -/
#guard outcome 100
  [ .assign "a" (.allocArray (u64 1) (.noneE)) ]
  = "undef"

#guard outcome 0
  [ .assign "a" (.allocArray (u64 1) (.noneE)) ]
  = "undef"

#guard outcome 100
  [ .assign "a" (.allocArray (.intLit .i64 (-1)) (.boolLit false)) ]
  = "undef"

#guard outcome 0
  [ .assign "a" (.allocArray (.optValue .noneE) (.optValue .noneE)) ]
  = "trap optionNone"

#guard outcome 0
  [ .assign "a" (.allocArray (u64 1) (.optValue .noneE)) ]
  = "trap optionNone"

#guard outcome 100
  [ .assign "a" (.allocArray (.intLit .i64 (-1)) (.optValue .noneE)) ]
  = "trap optionNone"

/- The empty payload tag is retained even though canonical rendering stays
`arr []`: a matching store reaches OOB, while a mismatched store is `undef`
before the bounds question. -/
#guard outcome 100
  [ .assign "a" (.allocArray (u64 0) (.boolLit false)),
    .store "a" (u64 0) (.boolLit true) ]
  = "trap indexOOB 0 0"

#guard outcome 100
  [ .assign "a" (.allocArray (u64 0) (.boolLit false)),
    .store "a" (u64 0) (u64 1) ]
  = "undef"

#guard outcome 100
  [ .assign "a" (.allocArray (u64 0) (u64 0)),
    .store "a" (u64 0) (.boolLit true) ]
  = "undef"

/- Store evaluation precedence: index aborts before value; value aborts
before array lookup/tag/bounds; tag mismatch precedes OOB. -/
#guard outcome 100
  [ .assign "a" (.allocArray (u64 1) (.boolLit false)),
    .store "a" (.optValue .noneE) (.optValue .noneE) ]
  = "trap optionNone"

#guard outcome 100
  [ .assign "a" (.allocArray (u64 1) (.boolLit false)),
    .store "a" (u64 9) (.optValue .noneE) ]
  = "trap optionNone"

#guard outcome 100
  [ .assign "a" (.allocArray (u64 1) (.boolLit false)),
    .store "a" (u64 9) (u64 1) ]
  = "undef"

/- Index evaluation also precedes the array lookup. -/
#guard outcome 100
  [ .ret (.index "missing" (.optValue .noneE)) ]
  = "trap optionNone"

/-! ## Lending an array across a call

`Arg.lend` names a caller local: the callee's exit value for the parameter
that receives it returns to that local when the frame pops. `Arg.byValue`
of the same variable supplies the same entry value and no return trip,
which is what a shared borrow promises. Neither form is payload-specific.
-/

private def lendProg : Prog := Prog.ofList
  [ ("setFirst", ⟨["m"], [.store "m" (u64 0) (.boolLit true)]⟩),
    ("setThenLen", ⟨["m"], [.store "m" (u64 0) (.boolLit true), .ret (.len "m")]⟩),
    ("lendOnward", ⟨["m"], [.call none "setFirst" [.lend "m"]]⟩),
    ("copyOnward", ⟨["m"], [.call none "setFirst" [.byValue (.var "m")]]⟩),
    ("setBeyond", ⟨["m"], [.store "m" (u64 5) (.boolLit true)]⟩),
    ("setInt", ⟨["m"], [.store "m" (u64 0) (u64 1)]⟩) ]

private def lent (cap : Int) (k : List Stmt) : String :=
  (run lendProg cap 1000 (.run k Env.empty [] .empty)).render

/- A lent array is written through; the same argument by value is not. -/
#guard lent 100
  [ .assign "a" (.allocArray (u64 2) (.boolLit false)),
    .call none "setFirst" [.lend "a"],
    .ret (.var "a") ]
  = "done arr [true, false]"

#guard lent 100
  [ .assign "a" (.allocArray (u64 2) (.boolLit false)),
    .call none "setFirst" [.byValue (.var "a")],
    .ret (.var "a") ]
  = "done arr [false, false]"

/- Both ways of leaving a body return the loan: `setFirst` falls off its
end, `setThenLen` returns a value. The result and the loan are separate
destinations. -/
#guard lent 100
  [ .assign "a" (.allocArray (u64 2) (.boolLit false)),
    .call (some "n") "setThenLen" [.lend "a"],
    .ret (.var "a") ]
  = "done arr [true, false]"

#guard lent 100
  [ .assign "a" (.allocArray (u64 2) (.boolLit false)),
    .call (some "n") "setThenLen" [.lend "a"],
    .ret (.var "n") ]
  = "done int 2"

/- Loans compose through frames, and exactly as far as they are written:
a re-lend reaches the original owner, a copy stops at the middle frame. -/
#guard lent 100
  [ .assign "a" (.allocArray (u64 2) (.boolLit false)),
    .call none "lendOnward" [.lend "a"],
    .ret (.var "a") ]
  = "done arr [true, false]"

#guard lent 100
  [ .assign "a" (.allocArray (u64 2) (.boolLit false)),
    .call none "copyOnward" [.lend "a"],
    .ret (.var "a") ]
  = "done arr [false, false]"

/- A trap in the callee is terminal, so no loan is returned. -/
#guard lent 100
  [ .assign "a" (.allocArray (u64 2) (.boolLit false)),
    .call none "setBeyond" [.lend "a"] ]
  = "trap indexOOB 5 2"

/- The payload tag crosses the call with the value: an integer store into a
lent *empty* Boolean array is the tag confusion `undef`, not an OOB trap. -/
#guard lent 100
  [ .assign "a" (.allocArray (u64 0) (.boolLit false)),
    .call none "setInt" [.lend "a"] ]
  = "undef"

/- Lending is reading: an unbound name is the ⊥-read, before the callee
runs at all. -/
#guard lent 100
  [ .call none "setFirst" [.lend "missing"] ]
  = "undef"

/- Nothing about lending is Boolean. -/
#guard lent 100
  [ .assign "a" (.allocArray (u64 2) (u64 0)),
    .call none "setInt" [.lend "a"],
    .ret (.var "a") ]
  = "done arr [1, 0]"


/- Record elements: the element tag is the record's declaration tag.
Alloc, store, read, and field projection are the ordinary payload-generic
operations; a cross-record store is tag confusion (`undef`) and wins over
OOB; the empty record array retains its tag. -/
#guard outcome 100
  [ .recordMake "p" 7 ["x"] [u64 3],
    .assign "a" (.allocArray (u64 2) (.var "p")),
    .ret (.recordField (.index "a" (u64 0)) "x") ]
  = "done int 3"

#guard outcome 100
  [ .recordMake "p" 7 ["x"] [u64 1],
    .recordMake "q" 7 ["x"] [u64 9],
    .assign "a" (.allocArray (u64 2) (.var "p")),
    .store "a" (u64 1) (.var "q"),
    .ret (.recordField (.index "a" (u64 1)) "x") ]
  = "done int 9"

/- A store of a different record's value is tag confusion, before bounds. -/
#guard outcome 100
  [ .recordMake "p" 7 ["x"] [u64 1],
    .recordMake "q" 8 ["x"] [u64 2],
    .assign "a" (.allocArray (u64 1) (.var "p")),
    .store "a" (u64 0) (.var "q") ]
  = "undef"

#guard outcome 100
  [ .recordMake "p" 7 ["x"] [u64 1],
    .recordMake "q" 8 ["x"] [u64 2],
    .assign "a" (.allocArray (u64 0) (.var "p")),
    .store "a" (u64 5) (.var "q") ]
  = "undef"

/- The matching store on the empty record array reaches the bounds trap. -/
#guard outcome 100
  [ .recordMake "p" 7 ["x"] [u64 1],
    .assign "a" (.allocArray (u64 0) (.var "p")),
    .store "a" (u64 0) (.var "p") ]
  = "trap indexOOB 0 0"

/- A scalar store into a record array is tag confusion too. -/
#guard outcome 100
  [ .recordMake "p" 7 ["x"] [u64 1],
    .assign "a" (.allocArray (u64 1) (.var "p")),
    .store "a" (u64 0) (u64 5) ]
  = "undef"

end SVM
end Sable
