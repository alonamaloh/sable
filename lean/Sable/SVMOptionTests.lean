/-
Direct executable regressions for ordinary SVM options.

These guards pin the recursive `Option Val` representation introduced for
Boolean payloads. In particular, `some(false)` must remain observably present,
and projecting `none` is the language's `optionNone` trap rather than `undef`.
Integer spellings are retained for compatibility with the differential wire
format that predates Boolean option payloads.
-/

import Sable.SVMEval

namespace Sable
namespace SVM

private def outcome (k : List Stmt) : String :=
  (run Prog.empty 1000000 1000 (.run k Env.empty [] .empty)).render

private def u64 (n : Int) : Expr := .intLit .u64 n

#guard outcome [ .ret (.someE (.boolLit true)) ] = "done opt some true"
#guard outcome [ .ret (.someE (.boolLit false)) ] = "done opt some false"

#guard outcome [ .ret (.optIsSome (.someE (.boolLit false))) ] = "done bool true"
#guard outcome [ .ret (.optIsSome .noneE) ] = "done bool false"

#guard outcome [ .ret (.optValue (.someE (.boolLit false))) ] = "done bool false"
#guard outcome [ .ret (.optValue .noneE) ] = "trap optionNone"

/- Existing integer observations remain byte-for-byte stable. -/
#guard outcome [ .ret (.someE (u64 7)) ] = "done opt some 7"
#guard outcome [ .ret (.optValue (.someE (u64 7))) ] = "done int 7"

/- Accessor shape confusion remains checker-duty `undef`. -/
#guard outcome [ .ret (.optIsSome (u64 7)) ] = "undef"
#guard outcome [ .ret (.optValue (.boolLit true)) ] = "undef"

end SVM
end Sable
