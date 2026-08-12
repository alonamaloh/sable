/-
Direct SVM subjects for the raw heap.

These are programs written in the machine's own syntax rather than
lowered from Sable. They are `#guard`s, so `lake build` fails if an
outcome moves — the same standing-regression role the agreement proofs
play for the rule system, aimed at the *outcomes* instead.

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

#guard IntTy.u64.layout = Sable.u64.layout
#guard IntTy.u64.layout.size = 8
#guard IntTy.u64.layout.align = 8

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

/-! ## Abstract typed u64 cells (ADR 0031) -/

#guard outcome
  [ .rawAlloc "p" (u64 8),
    .rawIntoCellU64 (.var "p"),
    .rawCellInitU64 (.var "p") (u64 42),
    .rawCellReadU64 "a" (.var "p"),
    .rawCellTakeU64 "b" (.var "p"),
    .rawFromCellU64 (.var "p"),
    .ret (.var "b") ]
  = "done int 42"

/- Returning an empty cell zero-fills the raw extent. -/
#guard outcome
  [ .rawAlloc "p" (u64 8),
    .rawIntoCellU64 (.var "p"),
    .rawCellInitU64 (.var "p") (u64 9),
    .rawCellDropU64 (.var "p"),
    .rawFromCellU64 (.var "p"),
    .rawLoad8 "b" (.var "p"),
    .ret (.var "b") ]
  = "done int 0"

/- Typed access before initialization is undefined. -/
#guard outcome
  [ .rawAlloc "p" (u64 8),
    .rawIntoCellU64 (.var "p"),
    .rawCellReadU64 "b" (.var "p") ]
  = "undef"

/- Byte access cannot pierce an active typed extent. -/
#guard outcome
  [ .rawAlloc "p" (u64 8),
    .rawIntoCellU64 (.var "p"),
    .rawStore8 (.ptrAdd (.var "p") (u64 3)) (u8 1) ]
  = "undef"

/- Runtime conversion requires an aligned address with eight live bytes.
Exact resource extent is additionally a verifier obligation. -/
#guard outcome
  [ .rawAlloc "p" (u64 9),
    .rawIntoCellU64 (.ptrAdd (.var "p") (u64 1)) ]
  = "undef"

/- Initialization is a transition, not an overwrite operation. -/
#guard outcome
  [ .rawAlloc "p" (u64 8),
    .rawIntoCellU64 (.var "p"),
    .rawCellInitU64 (.var "p") (u64 5),
    .rawCellInitU64 (.var "p") (u64 6) ]
  = "undef"

/- Typed tags do not resurrect when their allocation is released. -/
#guard outcome
  [ .rawAlloc "p" (u64 8),
    .rawIntoCellU64 (.var "p"),
    .rawFree (.var "p"),
    .rawCellInitU64 (.var "p") (u64 1) ]
  = "undef"

/- An initialized cell cannot return to raw storage until taken/dropped. -/
#guard outcome
  [ .rawAlloc "p" (u64 8),
    .rawIntoCellU64 (.var "p"),
    .rawCellInitU64 (.var "p") (u64 5),
    .rawFromCellU64 (.var "p") ]
  = "undef"

/-! ## Abstract typed POD record cells (ADR 0054/0055) -/

private def nodeFields : List String := ["previous", "next", "payload"]
private def nodeArgs (p : Expr) (payload : Int) : List Expr :=
  [.ptrNoneE, .ptrSomeE p, u64 payload]

/- Construct, initialize, copy-read, project, take, and return one abstract
record extent to raw storage. The value is never serialized. -/
#guard outcome
  [ .rawAlloc "p" (u64 24),
    .recordMake "node" 0 nodeFields (nodeArgs (.var "p") 42),
    .rawIntoCellRecord 0 24 8 (.var "p"),
    .rawCellInitRecord 0 (.var "p") (.var "node"),
    .rawCellReadRecord 0 "copy" (.var "p"),
    .assign "payload" (.recordField (.var "copy") "payload"),
    .rawCellTakeRecord 0 "taken" (.var "p"),
    .rawFromCellRecord 0 (.var "p"),
    .rawFree (.var "p"),
    .ret (.var "payload") ]
  = "done int 42"

/- Nullable pointer construction, observation, and projection retain
provenance plus offset. -/
#guard outcome
  [ .rawAlloc "p" (u64 24),
    .recordMake "node" 0 nodeFields (nodeArgs (.var "p") 7),
    .assign "next" (.recordField (.var "node") "next"),
    .assign "q" (.ptrValue (.var "next")),
    .ret (.ptrOffset (.var "q")) ]
  = "done int 0"

/- `.value` on an empty option is a defined language trap, not raw-memory
`undef`; the verifier normally proves this path unreachable. -/
#guard outcome [ .assign "q" (.ptrValue .ptrNoneE) ] = "trap optionNone"

/- Missing record fields remain checker-duty type confusion. -/
#guard outcome
  [ .recordMake "node" 0 nodeFields [.ptrNoneE, .ptrNoneE, u64 7],
    .ret (.recordField (.var "node") "missing") ]
  = "undef"

/- Record outcomes expose their declaration-order fields to the differential
wire format; comparing only the tag would hide value divergences. -/
#guard outcome
  [ .recordMake "node" 0 nodeFields [.ptrNoneE, .ptrNoneE, u64 7],
    .ret (.var "node") ]
  = "done record 0 {previous=ptrOpt none, next=ptrOpt none, payload=int 7}"

/- Dropping then removing a record cell zero-fills its complete raw extent. -/
#guard outcome
  [ .rawAlloc "p" (u64 24),
    .recordMake "node" 0 nodeFields (nodeArgs (.var "p") 9),
    .rawIntoCellRecord 0 24 8 (.var "p"),
    .rawCellInitRecord 0 (.var "p") (.var "node"),
    .rawCellDropRecord 0 (.var "p"),
    .rawFromCellRecord 0 (.var "p"),
    .rawLoad8 "b" (.ptrAdd (.var "p") (u64 23)),
    .ret (.var "b") ]
  = "done int 0"

/- Typed access before initialization. -/
#guard outcome
  [ .rawAlloc "p" (u64 24),
    .rawIntoCellRecord 0 24 8 (.var "p"),
    .rawCellReadRecord 0 "node" (.var "p") ]
  = "undef"

/- Interior bytes are covered, not merely the record's starting address. -/
#guard outcome
  [ .rawAlloc "p" (u64 24),
    .rawIntoCellRecord 0 24 8 (.var "p"),
    .rawStore8 (.ptrAdd (.var "p") (u64 17)) (u8 1) ]
  = "undef"

/- Conversion checks the declared runtime alignment and full extent. -/
#guard outcome
  [ .rawAlloc "p" (u64 25),
    .rawIntoCellRecord 0 24 8 (.ptrAdd (.var "p") (u64 1)) ]
  = "undef"

/- Initialization is not overwrite, and the value tag must match. -/
#guard outcome
  [ .rawAlloc "p" (u64 24),
    .recordMake "node" 0 nodeFields (nodeArgs (.var "p") 5),
    .rawIntoCellRecord 0 24 8 (.var "p"),
    .rawCellInitRecord 0 (.var "p") (.var "node"),
    .rawCellInitRecord 0 (.var "p") (.var "node") ]
  = "undef"

#guard outcome
  [ .rawAlloc "p" (u64 24),
    .recordMake "wrong" 1 nodeFields (nodeArgs (.var "p") 5),
    .rawIntoCellRecord 0 24 8 (.var "p"),
    .rawCellInitRecord 0 (.var "p") (.var "wrong") ]
  = "undef"

/- Access and conversion back require the same static record tag. -/
#guard outcome
  [ .rawAlloc "p" (u64 24),
    .recordMake "node" 0 nodeFields (nodeArgs (.var "p") 5),
    .rawIntoCellRecord 0 24 8 (.var "p"),
    .rawCellInitRecord 0 (.var "p") (.var "node"),
    .rawCellReadRecord 1 "wrong" (.var "p") ]
  = "undef"

#guard outcome
  [ .rawAlloc "p" (u64 24),
    .recordMake "node" 0 nodeFields (nodeArgs (.var "p") 5),
    .rawIntoCellRecord 0 24 8 (.var "p"),
    .rawCellInitRecord 0 (.var "p") (.var "node"),
    .rawFromCellRecord 0 (.var "p") ]
  = "undef"

/- Record and scalar typed extents exclude overlap in both directions. -/
#guard outcome
  [ .rawAlloc "p" (u64 24),
    .rawIntoCellRecord 0 24 8 (.var "p"),
    .rawIntoCellU64 (.ptrAdd (.var "p") (u64 8)) ]
  = "undef"

#guard outcome
  [ .rawAlloc "p" (u64 24),
    .rawIntoCellU64 (.ptrAdd (.var "p") (u64 8)),
    .rawIntoCellRecord 0 24 8 (.var "p") ]
  = "undef"

/- Releasing the allocation makes its record tags inert. -/
#guard outcome
  [ .rawAlloc "p" (u64 24),
    .recordMake "node" 0 nodeFields (nodeArgs (.var "p") 5),
    .rawIntoCellRecord 0 24 8 (.var "p"),
    .rawFree (.var "p"),
    .rawCellInitRecord 0 (.var "p") (.var "node") ]
  = "undef"

end SVM
end Sable
