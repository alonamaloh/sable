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

end SVM
end Sable
