/-
Direct SVM subjects for the raw heap.

These are programs written in the machine's own syntax rather than
lowered from Sable, because the raw operations have no source surface
yet (that is lexical byte exposure, a later rung). They are `#guard`s, so
`lake build` fails if an outcome moves — the same standing-regression
role the agreement proofs play for the rule system, aimed at the
*outcomes* instead.

What they pin: the valid path through alloc/store/load/take/free, and
each way an invalid one reaches `undef` — out of bounds, uninitialized,
use after free, double free, interior free, and a byte taken twice.
`undef` being a defined outcome is what makes these expressible at all.
-/

import Sable.SVMEval

namespace Sable
namespace SVM

/- Run a body from empty locals and an empty heap. -/
private def outcome (k : List Stmt) : String :=
  (run Prog.empty 1000000 1000 (.run k Env.empty [] .empty)).render

private def u64 (n : Int) : Expr := .intLit .u64 n
private def u8 (n : Int) : Expr := .intLit .u8 n

/-! ## The valid path -/

/- Allocate four bytes, write one, read it back. -/
#guard outcome
  [ .rawAlloc "p" (u64 4),
    .rawStore8 (.var "p") (u8 7),
    .rawLoad8 "b" (.var "p"),
    .ret (.var "b") ]
  = "done int 7"

/- Pointer arithmetic reaches the byte it names, and bytes are
independent: writing at `p+2` does not disturb `p+0`. -/
#guard outcome
  [ .rawAlloc "p" (u64 4),
    .rawStore8 (.var "p") (u8 1),
    .rawStore8 (.ptrAdd (.var "p") (u64 2)) (u8 9),
    .rawLoad8 "b" (.var "p"),
    .ret (.var "b") ]
  = "done int 1"

#guard outcome
  [ .rawAlloc "p" (u64 4),
    .rawStore8 (.var "p") (u8 1),
    .rawStore8 (.ptrAdd (.var "p") (u64 2)) (u8 9),
    .rawLoad8 "b" (.ptrAdd (.var "p") (u64 2)),
    .ret (.var "b") ]
  = "done int 9"

/- `take8` returns the byte and leaves the storage uninitialized. The
value comes back; the *next* read is the interesting one. -/
#guard outcome
  [ .rawAlloc "p" (u64 1),
    .rawStore8 (.var "p") (u8 5),
    .rawTake8 "b" (.var "p"),
    .ret (.var "b") ]
  = "done int 5"

/- Two allocations are disjoint: the counter never hands out an id
twice, so writing one cannot be seen through the other. -/
#guard outcome
  [ .rawAlloc "p" (u64 1),
    .rawAlloc "q" (u64 1),
    .rawStore8 (.var "p") (u8 3),
    .rawStore8 (.var "q") (u8 4),
    .rawLoad8 "b" (.var "p"),
    .ret (.var "b") ]
  = "done int 3"

/- A freed allocation's id is not reused: the next allocation gets a
fresh one, and the old pointer stays distinguishable. -/
#guard outcome
  [ .rawAlloc "p" (u64 1),
    .rawStore8 (.var "p") (u8 3),
    .rawFree (.var "p"),
    .rawAlloc "q" (u64 1),
    .rawStore8 (.var "q") (u8 4),
    .rawLoad8 "b" (.var "q"),
    .ret (.var "b") ]
  = "done int 4"

/- Allocation past the cap traps rather than reaching `undef`: running
out of memory is a defined failure, not a program error (§9). -/
#guard (run Prog.empty 4 100 (.run [ .rawAlloc "p" (u64 8) ] Env.empty [] .empty)).render
  = "trap oom 8"

/-! ## Every way to reach `undef` -/

/- Reading past the end of an allocation. -/
#guard outcome
  [ .rawAlloc "p" (u64 2),
    .rawLoad8 "b" (.ptrAdd (.var "p") (u64 2)),
    .ret (.var "b") ]
  = "undef"

/- Writing past the end. -/
#guard outcome
  [ .rawAlloc "p" (u64 2),
    .rawStore8 (.ptrAdd (.var "p") (u64 2)) (u8 1) ]
  = "undef"

/- Reading a byte that was allocated but never written. This is the
distinction `RawByte.uninit` exists for: the storage is in bounds and
live, and there is still nothing there to read. -/
#guard outcome
  [ .rawAlloc "p" (u64 1),
    .rawLoad8 "b" (.var "p"),
    .ret (.var "b") ]
  = "undef"

/- Reading a byte that `take8` emptied. -/
#guard outcome
  [ .rawAlloc "p" (u64 1),
    .rawStore8 (.var "p") (u8 5),
    .rawTake8 "b" (.var "p"),
    .rawLoad8 "c" (.var "p"),
    .ret (.var "c") ]
  = "undef"

/- ...and writing it back makes it readable again. `take8` moves the
byte out; it does not poison the storage. -/
#guard outcome
  [ .rawAlloc "p" (u64 1),
    .rawStore8 (.var "p") (u8 5),
    .rawTake8 "b" (.var "p"),
    .rawStore8 (.var "p") (u8 6),
    .rawLoad8 "c" (.var "p"),
    .ret (.var "c") ]
  = "done int 6"

/- Use after free. -/
#guard outcome
  [ .rawAlloc "p" (u64 1),
    .rawStore8 (.var "p") (u8 5),
    .rawFree (.var "p"),
    .rawLoad8 "b" (.var "p"),
    .ret (.var "b") ]
  = "undef"

/- Double free. Marking the allocation dead rather than removing it is
what makes the second free distinguishable from a free of an id that was
never handed out. -/
#guard outcome
  [ .rawAlloc "p" (u64 1),
    .rawFree (.var "p"),
    .rawFree (.var "p") ]
  = "undef"

/- Freeing an interior pointer. Not a partial release — `free` names a
whole allocation or nothing. -/
#guard outcome
  [ .rawAlloc "p" (u64 4),
    .rawFree (.ptrAdd (.var "p") (u64 1)) ]
  = "undef"

/- Freeing something that is not a pointer at all. -/
#guard outcome [ .rawFree (u64 0) ] = "undef"

/- Storing a value outside `u8`. Representability is checker duty, so
the machine's answer is `undef` rather than a wrap or a trap. -/
#guard outcome
  [ .rawAlloc "p" (u64 1),
    .rawStore8 (.var "p") (.intLit .u64 256) ]
  = "undef"

/- Dereferencing an integer. -/
#guard outcome [ .rawLoad8 "b" (u64 0), .ret (.var "b") ] = "undef"

/- Pointer arithmetic on a non-pointer. -/
#guard outcome
  [ .rawAlloc "p" (u64 1),
    .rawStore8 (.ptrAdd (u64 0) (u64 1)) (u8 1) ]
  = "undef"

/-! ## Pointer arithmetic is pure

A pointer may leave its allocation and come back. Nothing is
dereferenced by `ptrAdd`, so there is no outcome to have until a load or
a store asks. -/
#guard outcome
  [ .rawAlloc "p" (u64 2),
    .rawStore8 (.var "p") (u8 7),
    .assign "q" (.ptrAdd (.ptrAdd (.var "p") (u64 9)) (.intLit .i64 (-9))),
    .rawLoad8 "b" (.var "q"),
    .ret (.var "b") ]
  = "done int 7"

end SVM
end Sable
