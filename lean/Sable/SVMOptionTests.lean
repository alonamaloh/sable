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

/- Affine take is statement-level and atomic. A stale destination binding is
overwritten (as it is when a lexical local name is reused by a loop), while
the source is observably `none` before the following statement runs. -/
#guard outcome [
  .assign "src" (.someE (.allocArray (u64 2) (.boolLit false))),
  .assign "dst" (.boolLit true),
  .optTake "dst" "src",
  .check "sourceCleared" (.not (.optIsSome (.var "src"))),
  .ret (.var "dst")
] = "done arr [false, false]"

/- Even at length zero the Boolean-array tag survives the move. A mismatched
integer store is rejected by the tag check before the bounds trap; if the
empty array had silently become an integer array this would instead trap OOB. -/
#guard outcome [
  .assign "src" (.someE (.allocArray (u64 0) (.boolLit false))),
  .optTake "dst" "src",
  .store "dst" (u64 0) (u64 1)
] = "undef"

/- Taking an absent payload is the same language trap as projecting `none`;
missing/wrong-shaped sources and destination/source aliasing are fail-closed. -/
#guard outcome [ .assign "src" .noneE, .optTake "dst" "src" ] =
  "trap optionNone"
#guard outcome [ .optTake "dst" "missing" ] = "undef"
#guard outcome [ .assign "src" (.boolLit true), .optTake "dst" "src" ] = "undef"
#guard outcome [
  .assign "src" (.someE (.allocArray (u64 1) (.boolLit true))),
  .optTake "src" "src"
] = "undef"

end SVM
end Sable
