/-
SVM: operational semantics for a core Sable subset (design §10, ADR 0005).

The scope is deliberately partial — classes, ghost state, and the safe
heap are scoped out with notes; the findings the first draft forced are
resolved in ADR 0005 and design §10. A borrow is not a value here: a
unique one is an argument form (`Arg.lend`, ADR 0069) whose exit value
returns to the caller's local when the frame pops, and a shared one is
the value it names.

Shape:

- **Statements: small-step**, an inductive relation `Step` over
  configurations, as design §10 mandates ("small-step, deterministic").
  Divergence (`while`), normal termination, and traps must be
  distinguishable, and small-step is what makes divergence a real
  behavior rather than a missing derivation.
- **Expressions: big-step**, an inductive relation `Eval`. In this
  fragment expressions are pure and call-free (calls are A-normalized to
  statements, ADR 0005), so evaluation cannot diverge and big-step loses
  no distinctions — but every abnormal-*propagation* rule is still an
  explicit constructor, because evaluation order (hence which trap
  fires) is normative: left-to-right, short-circuit `&&`/`||`.
- **Three terminal outcomes** (ADR 0005): normal termination
  (`Config.done`), traps (`Config.trapped`), and `Config.undef` — the
  outcome of every state the static semantics is responsible for
  excluding (⊥-reads, type confusion, out-of-range literals). The
  machine is total: every syntactically valid program has a meaning
  (pillar 1 holds literally), and the soundness theorem sharpens to
  "verified programs never reach `undef`".
- The machine is parameterized by an allocation capacity `cap`;
  without it, "deterministic" and "alloc failure is a defined OOM trap"
  (§10) contradict each other.

Determinism, totality, and agreement with the functional evaluator are
theorems, not claims — see `Sable/SVMEval.lean`.

Values are exact `Int`s; fixed widths live in the *syntax* (each
arithmetic node carries the `IntTy` at which representability is
checked), matching the compiler's typed AST and the "values are exact
integers" invariant. Division is Euclidean (`Int.ediv`/`Int.emod`,
ADR 0004).
-/
import Sable.Seq
import Sable.Layout

namespace Sable
namespace SVM

/-! ## Integer types

Bounds duplicated from `Sable.Bounds` as a closed enum (the prelude file
exposes them as loose defs for clause authors; the machine needs them as
a function of a syntax-level type tag). -/

inductive IntTy where
  | i8 | i16 | i32 | i64 | u8 | u16 | u32 | u64
  deriving DecidableEq, Repr

def IntTy.min : IntTy → Int
  | .i8  => -128
  | .i16 => -32768
  | .i32 => -2147483648
  | .i64 => -9223372036854775808
  | .u8 | .u16 | .u32 | .u64 => 0

def IntTy.max : IntTy → Int
  | .i8  => 127
  | .i16 => 32767
  | .i32 => 2147483647
  | .i64 => 9223372036854775807
  | .u8  => 255
  | .u16 => 65535
  | .u32 => 4294967295
  | .u64 => 18446744073709551615

def IntTy.bits : IntTy → Nat
  | .i8 | .u8 => 8
  | .i16 | .u16 => 16
  | .i32 | .u32 => 32
  | .i64 | .u64 => 64

/-- Compiler-established geometry. It carries no representation relation. -/
def IntTy.layout : IntTy → Sable.Layout
  | .u8 => Sable.u8.layout
  | .i8 => Sable.i8.layout
  | .u16 => Sable.u16.layout
  | .i16 => Sable.i16.layout
  | .u32 => Sable.u32.layout
  | .i32 => Sable.i32.layout
  | .u64 => Sable.u64.layout
  | .i64 => Sable.i64.layout

/-- The representability side condition every partial arithmetic rule
checks (design §2.2). -/
def IntTy.inRange (t : IntTy) (n : Int) : Prop :=
  t.min ≤ n ∧ n ≤ t.max

instance (t : IntTy) (n : Int) : Decidable (t.inRange n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Two's-complement wrap into `[t.min, t.max]` — the semantics of the
total operator `wrap(·)` (§2.2, ADR 0005: signed `wrap` is
two's-complement). For unsigned `t` this is `n mod 2^bits`. -/
def IntTy.wrap (t : IntTy) (n : Int) : Int :=
  (n - t.min).emod ((2 : Int) ^ t.bits) + t.min

/-! ## Values, traps, and abnormal outcomes -/

/-- The element domains an owned SVM array may carry. A tag is a *name* for
a domain, not a second copy of its values: it exists so that an array keeps
its element type at length zero, where no element is left to imply one. -/
inductive ValTag where
  | int
  | bool
  /-- Record elements carry the declaration tag, so two record types'
  empty arrays stay distinguishable and a cross-record store is tag
  confusion, not a silent structural coincidence. -/
  | record (tag : Int)
  deriving DecidableEq, Repr

/-- Machine values. Integers are exact (`Int`); their widths live in the
typed syntax, and per-operation rules enforce representability — the
value plane never wraps.

Aggregates hold ordinary machine values, so every stage of the machine has
one implementation per operation instead of one per (shape × payload) pair:
an array is a payload tag beside a `Seq Val`, an option is an `Option Val`,
and a record is a tag beside named `Val` fields. The array tag sits *beside*
the elements rather than inside their representation, which keeps an empty
integer array and an empty Boolean array distinguishable — they accept
different stores — while making what an array may hold a checker question
rather than a machine one.

Nullable raw pointers are ordinary options whose present case carries a
`ptr`; there is no separate pointer-option value. Pointers and POD records
remain distinct abstract values with no byte representation (ADR 0054). -/
inductive Val where
  | unit
  | int  (n : Int)
  | bool (b : Bool)
  | arr  (elem : ValTag) (a : Seq Val)
  | opt  (o : Option Val)
  /-- A raw pointer: provenance plus a byte offset, never a machine
  address. Two live pointers may name the same address only if they name
  the same allocation, which is what makes `free` able to invalidate
  exactly the pointers derived from what it released. -/
  | ptr  (alloc off : Int)
  /-- Declaration tag plus fields in declaration order. Names make field
  projection independent of compiler-local record indices; the tag still
  prevents typed-cell confusion. -/
  | record (tag : Int) (fields : List (String × Val))

/-- The domain a value inhabits, when it inhabits one an array can carry.
This is the single admission gate for array elements: widening the machine
to another payload is one arm here, not an arm in every array operation. -/
def Val.tag? : Val → Option ValTag
  | .int _ => some .int
  | .bool _ => some .bool
  | .record tag _ => some (.record tag)
  | _ => none

/-- Type-preserving update of a `Val.arr`'s fields, one implementation for
every payload: `Val.arr` spreads its tag and its elements across two
constructor fields, so the operation takes both. `none` is payload-tag
confusion; bounds are checked separately so a mismatched store wins over an
OOB trap. Filling a length-`n` array is `Seq.replicate`, so this is the only
array operation that needs the tag at all. -/
def Val.arrSet? (elem : ValTag) (a : Seq Val) (i : Int) (w : Val) :
    Option (Seq Val) :=
  if w.tag? = some elem then some (a.set i w) else none

def Val.recordField? : Val → String → Option Val
  | .record _ fields, name =>
      (fields.find? fun field => field.1 = name).map (·.2)
  | _, _ => none

def Val.recordForTag? (v : Val) (tag : Int) : Option Val :=
  match v with
  | .record valueTag _ => if valueTag = tag then some v else none
  | _ => none

/-! ## The raw heap

The safe value plane keeps owned arrays and classes inside `Val`; the
raw heap is a *separate* component of the configuration, and every safe
rule preserves it unchanged. That separation is the point: adding
unsafe Sable does not reinterpret a single existing rule.

Byte state is not `Int`: uninitialized is a distinct state, and it must
stay distinguishable from every inhabitant of a value type (the same
choice `Sable.ByteState` makes for views — this is the machine's copy,
since `SVM.lean` is self-contained). -/

/-- A byte of raw storage. -/
inductive RawByte where
  | uninit : RawByte
  | init : Int → RawByte
  deriving Repr, DecidableEq

/-- One abstract record-typed extent. `value = none` is the typed but
uninitialized state; an initialized value always carries the same tag. -/
structure RecordCell where
  tag : Int
  size : Int
  align : Int
  value : Option Val

/-- One allocation. `live` is kept rather than removed on free, so stale
provenance stays distinguishable from fresh provenance: a released id is
never handed out again. -/
structure Allocation where
  size : Int
  live : Bool
  bytes : Seq RawByte
  /-- Starts of abstract typed `u64` extents. Outer `none` means raw
  bytes; `some none` is an uninitialized cell; `some (some v)` is an
  initialized one (ADR 0031). -/
  cellsU64 : Int → Option (Option Int)
  /-- Record cells are keyed by their starting offset. -/
  cellsRecord : Int → Option RecordCell
  /-- Per-byte ownership by a record start. This makes exclusion of byte
  operations decidable without searching an unbounded partial map. -/
  recordOwner : Int → Option Int

/-- The raw heap: a fresh-provenance counter and a partial map from
allocation ids. Ids at or above `next` are unallocated, which is what
makes a new allocation disjoint from everything already reachable
without inspecting anything (ADR 0022). -/
structure RawHeap where
  next : Int
  allocs : Int → Option Allocation

def RawHeap.empty : RawHeap :=
  { next := 0, allocs := fun _ => none }

/-- A byte offset is in bounds of a live allocation. Decidable by
construction: the machine must be able to *compute* this, since it is
the difference between a store and `undef`. -/
def RawHeap.inBounds (μ : RawHeap) (a k : Int) : Bool :=
  match μ.allocs a with
  | some al =>
      let base := k - k.emod IntTy.u64.layout.align
      al.live && decide (0 ≤ k) && decide (k < al.size) &&
        decide (al.cellsU64 base = none) && decide (al.recordOwner k = none)
  | none => false

/-- The byte at `(a, k)`, if that address is in a live allocation. -/
def RawHeap.byteAt (μ : RawHeap) (a k : Int) : Option RawByte :=
  match μ.allocs a with
  | some al =>
      let base := k - k.emod IntTy.u64.layout.align
      if al.live ∧ 0 ≤ k ∧ k < al.size ∧ al.cellsU64 base = none ∧
          al.recordOwner k = none then
        some (al.bytes.get k)
      else none
  | none => none

/-- The initialized byte at `(a, k)`, if there is one. `none` covers all
three ways a load can be meaningless — absent, dead, out of bounds, or
uninitialized — because the machine's answer is the same for each and
the *checker*'s job is to tell them apart in a diagnostic. -/
def RawHeap.loadByte (μ : RawHeap) (a k : Int) : Option Int :=
  match μ.byteAt a k with
  | some (.init b) => some b
  | _ => none

/-- Whether `free(p)` is meaningful: `p` must name the *start* of a live
allocation. Freeing an interior pointer is not a partial release. -/
def RawHeap.freeable (μ : RawHeap) (a k : Int) : Bool :=
  decide (k = 0) && (match μ.allocs a with | some al => al.live | none => false)

/-- Write one byte. A no-op on a dead or absent allocation; the rules
never reach it, because the bounds premise is checked first. -/
def RawHeap.store (μ : RawHeap) (a k : Int) (b : RawByte) : RawHeap :=
  { μ with allocs := fun i =>
      if i = a then (μ.allocs i).map (fun al => { al with bytes := al.bytes.set k b })
      else μ.allocs i }

/-- Every byte in `[k, k + size)` is currently ordinary raw storage. -/
def RawHeap.rawExtent (μ : RawHeap) (a k size : Int) : Bool :=
  decide (0 ≤ size) &&
    (List.range size.toNat).all fun d => μ.inBounds a (k + (d : Int))

/-- Whether one `u64` layout may change role into one typed cell. -/
def RawHeap.cellConvertibleU64 (μ : RawHeap) (a k : Int) : Bool :=
  decide (k % IntTy.u64.layout.align = 0) &&
    μ.rawExtent a k IntTy.u64.layout.size

def RawHeap.cellAtU64 (μ : RawHeap) (a k : Int) : Option (Option Int) :=
  match μ.allocs a with
  | some al => if al.live then al.cellsU64 k else none
  | none => none

def RawHeap.putCellU64 (μ : RawHeap) (a k : Int) (s : Option Int) : RawHeap :=
  { μ with allocs := fun i =>
      if i = a then (μ.allocs i).map (fun al =>
        { al with cellsU64 := fun j => if j = k then some s else al.cellsU64 j })
      else μ.allocs i }

/-- Remove an uninitialized typed tag and explicitly zero the raw extent.
The zero fill is cleanup, not a byte representation of a typed value. -/
def RawHeap.removeCellU64 (μ : RawHeap) (a k : Int) : RawHeap :=
  { μ with allocs := fun i =>
      if i = a then (μ.allocs i).map (fun al =>
        { al with
          cellsU64 := fun j => if j = k then none else al.cellsU64 j
          bytes := ⟨al.bytes.len, fun j =>
            if k ≤ j ∧ j < k + IntTy.u64.layout.size then .init 0 else al.bytes.get j⟩ })
      else μ.allocs i }

/-- Whether an explicitly described record layout may occupy this raw extent.
The front end proves the stronger layout well-formedness facts; the machine
checks the dynamic size, alignment, bounds, and role exclusion it needs. -/
def RawHeap.cellConvertibleRecord
    (μ : RawHeap) (a k size align : Int) : Bool :=
  decide (0 < size) && decide (0 < align) && decide (k % align = 0) &&
    μ.rawExtent a k size

def RawHeap.putRecordCell
    (μ : RawHeap) (a k tag size align : Int) : RawHeap :=
  { μ with allocs := fun i =>
      if i = a then (μ.allocs i).map (fun al =>
        { al with
          cellsRecord := fun j =>
            if j = k then some ⟨tag, size, align, none⟩ else al.cellsRecord j
          recordOwner := fun j =>
            if k ≤ j ∧ j < k + size then some k else al.recordOwner j })
      else μ.allocs i }

/-- The size of a live, matching, uninitialized record cell. -/
def RawHeap.emptyRecordSize
    (μ : RawHeap) (a k tag : Int) : Option Int :=
  match μ.allocs a with
  | some al =>
      if al.live then
        match al.cellsRecord k with
        | some ⟨cellTag, size, _, none⟩ =>
            if cellTag = tag then some size else none
        | _ => none
      else none
  | none => none

/-- The value of a live, matching, initialized record cell. -/
def RawHeap.recordValueAt
    (μ : RawHeap) (a k tag : Int) : Option Val :=
  match μ.allocs a with
  | some al =>
      if al.live then
        match al.cellsRecord k with
        | some ⟨cellTag, _, _, some value⟩ =>
            if cellTag = tag then some value else none
        | _ => none
      else none
  | none => none

/-- Change only the initialized/uninitialized state of an existing record
cell. Rules call this only after checking the matching tag and state. -/
def RawHeap.setRecordValue
    (μ : RawHeap) (a k : Int) (value : Option Val) : RawHeap :=
  { μ with allocs := fun i =>
      if i = a then (μ.allocs i).map (fun al =>
        { al with cellsRecord := fun j =>
            if j = k then (al.cellsRecord j).map (fun cell => { cell with value })
            else al.cellsRecord j })
      else μ.allocs i }

/-- Remove a matching empty record tag and explicitly zero its raw extent. -/
def RawHeap.removeRecordCell
    (μ : RawHeap) (a k size : Int) : RawHeap :=
  { μ with allocs := fun i =>
      if i = a then (μ.allocs i).map (fun al =>
        { al with
          cellsRecord := fun j => if j = k then none else al.cellsRecord j
          recordOwner := fun j =>
            if k ≤ j ∧ j < k + size then none else al.recordOwner j
          bytes := ⟨al.bytes.len, fun j =>
            if k ≤ j ∧ j < k + size then .init 0 else al.bytes.get j⟩ })
      else μ.allocs i }

/-- Mark an allocation dead. The entry stays, so its id is never reused
and a pointer into it stays distinguishable from a fresh one. -/
def RawHeap.release (μ : RawHeap) (a : Int) : RawHeap :=
  { μ with allocs := fun i =>
      if i = a then (μ.allocs i).map (fun al => { al with live := false })
      else μ.allocs i }

/-- A fresh allocation of `size` uninitialized bytes at id `μ.next`. -/
def RawHeap.fresh (μ : RawHeap) (size : Int) : RawHeap :=
  { next := μ.next + 1,
    allocs := fun i =>
      if i = μ.next then
        some {
          size, live := true, bytes := ⟨size, fun _ => .uninit⟩,
          cellsU64 := fun _ => none,
          cellsRecord := fun _ => none,
          recordOwner := fun _ => none }
      else μ.allocs i }

/-- Terminal trap outcomes, distinct from normal termination. These are
*structural* (they carry the operation and the offending data); the
obligation *names* of §6/§9 are compiler artifacts layered on top —
except for `deferViolation`, where the compiled `defer` check carries its
obligation name into machine syntax (ADR 0005). -/
inductive Trap where
  | overflow  (t : IntTy)
  | divByZero
  | optionNone
  | indexOOB  (i len : Int)
  | narrowOOB (t : IntTy) (n : Int)
  | oom       (len : Int)
  | deferViolation (name : String)
  deriving Repr

/-- An abnormal outcome: a trap, or `undef` — the outcome of every state
the static semantics must exclude (⊥-reads, type confusion, out-of-range
literals; ADR 0005). `undef` is a *defined* outcome, so the machine is
total and pillar 1 holds literally; the soundness theorem sharpens to
"verified programs never reach `undef`". -/
inductive Abort where
  | trap (t : Trap)
  | undef

/-! ## Syntax -/

inductive ArithOp where
  | add | sub | mul
  deriving DecidableEq, Repr

/-- Exact (ℤ-plane) denotation; representability is a separate side
condition in the rules. -/
def ArithOp.denote : ArithOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

inductive CmpOp where
  | lt | le | gt | ge | eq | ne
  deriving DecidableEq, Repr

def CmpOp.denote : CmpOp → Int → Int → Bool
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (b < a)
  | .ge, a, b => decide (b ≤ a)
  | .eq, a, b => decide (a = b)
  | .ne, a, b => decide (a ≠ b)

/-- Expressions. Arithmetic nodes carry the `IntTy` at which the
representability check happens (the compiler's typed AST provides it).
Arrays are referred to by variable, matching the compiler's AST.
Scoped out: function calls (A-normalized to statements, ADR 0005),
method calls, class constructors, borrows as distinct values, and `sat(·)`.
Ordinary and nullable-pointer options have distinct constructors so an
ill-shaped accessor is still `undef` rather than silently crossing domains. -/
inductive Expr where
  | intLit  (t : IntTy) (n : Int)
  | boolLit (b : Bool)
  | var     (x : String)
  | neg     (t : IntTy) (e : Expr)
  | not     (e : Expr)
  | arith   (op : ArithOp) (t : IntTy) (e₁ e₂ : Expr)
  /-- `wrap(a ⊕ b)` — total modular arithmetic (§2.2). An operator
  *modifier*, not a function: an ordinary operand would already have
  trapped on overflow (ADR 0005). -/
  | wrapArith (op : ArithOp) (t : IntTy) (e₁ e₂ : Expr)
  /-- `checked(a ⊕ b)` — `none` on overflow (§2.2). Same caveat. -/
  | checkedArith (op : ArithOp) (t : IntTy) (e₁ e₂ : Expr)
  | div     (t : IntTy) (e₁ e₂ : Expr)
  | mod     (t : IntTy) (e₁ e₂ : Expr)
  | cmp     (op : CmpOp) (e₁ e₂ : Expr)
  | and     (e₁ e₂ : Expr)
  | or      (e₁ e₂ : Expr)
  | len     (x : String)
  | index   (x : String) (i : Expr)
  | widen   (dst : IntTy) (e : Expr)
  | narrow  (dst : IntTy) (e : Expr)
  | allocArray (len init : Expr)
  /-- `p + d`: pointer arithmetic, which is *pure*. Provenance is
  carried along and the offset moves; nothing is dereferenced, so a
  pointer may sit outside its allocation without any outcome at all.
  Only a load or a store asks whether it is in bounds. -/
  | ptrAdd  (p d : Expr)
  /-- Observe the arena-relative component of a pointer. -/
  | ptrOffset (p : Expr)
  /-- Option construction and observation. One family serves every payload,
  nullable raw pointers included: `some(p)` on a pointer is an ordinary
  option carrying a `ptr`. -/
  | someE   (e : Expr)
  | noneE
  | optIsSome (e : Expr)
  | optValue (e : Expr)
  | recordField (record : Expr) (field : String)

/-- A call argument. `byValue` transports whatever its expression
produces. `lend` is the machine's **unique borrow**: it names a caller
local, and the callee's exit value for the parameter that receives it
returns to that local when the frame pops.

Both forms supply the same entry value — `Arg.toExpr` says so — because a
borrow is a second name for storage, not a second kind of value. What
lending adds is only where the value goes back.

Copying in and copying out is faithful precisely because a unique borrow
is exclusive: while the callee runs, no other name reaches that storage,
so no observer can distinguish a cell written through from one restored
at the return. A shared borrow therefore needs no constructor at all —
its whole promise is that the callee does not write, and `byValue` is
exactly that promise. -/
inductive Arg where
  | byValue (e : Expr)
  | lend    (x : String)

/-- The entry value of an argument: lending a local is reading it. -/
def Arg.toExpr : Arg → Expr
  | .byValue e => e
  | .lend x => .var x

/-- Pair each lent argument with the parameter that receives it: the
callee's exit value for `p` returns to the caller's `x`. Positional like
`Env.bind`, and a length mismatch is checker duty — every rule that uses
this has already checked arity. -/
def Arg.loans : List String → List Arg → List (String × String)
  | p :: ps, .lend x :: as => (p, x) :: Arg.loans ps as
  | _ :: ps, _ :: as => Arg.loans ps as
  | _, _ => []

/-- Statements. `while` carries no invariant/variant: loop annotations
are ghost and erased (§4); the machine runs the loop, the verifier proves
it. `check` is the compiled form of `defer P` (§9): evaluate the
monitorable predicate, trap with the obligation's name if false. `call`
is the A-normal form calls take in the machine (ADR 0005): they exist
only at statement level — `x = f(args)`, or `f(args)` for a discarded
result — so expressions stay pure and big-step. -/
inductive Stmt where
  | assign (x : String) (e : Expr)
  /-- `dst = src.take()` for an affine option. Unlike `optValue`, this is
  a statement-level, direct-local operation: a successful step installs
  `none` in `src` and the former payload in `dst` in one transition. The
  untyped core transfers the recursively represented `Val` payload; the
  compiler's supported-subset gate admits only owned Boolean arrays. A
  non-option source or `dst = src` has the explicit `undef` outcome. -/
  | optTake (dst src : String)
  /-- Direct POD construction. Field names and argument expressions are
  parallel lists; a length mismatch is `undef` (checker duty). -/
  | recordMake (dst : String) (tag : Int) (fields : List String) (args : List Expr)
  | store  (x : String) (idx : Expr) (val : Expr)
  | ite    (c : Expr) (thn els : List Stmt)
  | while  (c : Expr) (body : List Stmt)
  | ret    (e : Expr)
  | check  (name : String) (c : Expr)
  | call   (dst : Option String) (f : String) (args : List Arg)
  /-- `dst = alloc(size)` — a fresh root allocation of `size`
  uninitialized bytes, and a pointer to its start. Provenance comes from
  a deterministic counter, so a released id is never handed out twice. -/
  | rawAlloc  (dst : String) (size : Expr)
  /-- `free(p)` — release the whole allocation `p` points at. It must
  point at the *start* of a live allocation: freeing an interior pointer
  is `undef`, not a partial release. -/
  | rawFree   (p : Expr)
  /-- `dst = load8(p)` — read one initialized byte. Out of bounds, dead,
  or uninitialized is `undef`; verified code proves it unreachable. -/
  | rawLoad8  (dst : String) (p : Expr)
  /-- `store8(p, v)` — write one byte, which becomes initialized. -/
  | rawStore8 (p : Expr) (v : Expr)
  /-- `dst = take8(p)` — read one initialized byte *and* leave the
  storage uninitialized. Reading it again is `undef` until it is written
  back, which is what makes a move out of raw memory expressible. -/
  | rawTake8  (dst : String) (p : Expr)
  /-- Change an aligned eight-byte raw extent into an uninitialized
  abstract typed `u64` cell, discarding the former byte contents. -/
  | rawIntoCellU64 (p : Expr)
  /-- Remove an uninitialized typed tag and zero the eight raw bytes. -/
  | rawFromCellU64 (p : Expr)
  | rawCellInitU64 (p v : Expr)
  | rawCellReadU64 (dst : String) (p : Expr)
  | rawCellTakeU64 (dst : String) (p : Expr)
  | rawCellDropU64 (p : Expr)
  | rawIntoCellRecord (tag size align : Int) (p : Expr)
  | rawFromCellRecord (tag : Int) (p : Expr)
  | rawCellInitRecord (tag : Int) (p value : Expr)
  | rawCellReadRecord (tag : Int) (dst : String) (p : Expr)
  | rawCellTakeRecord (tag : Int) (dst : String) (p : Expr)
  | rawCellDropRecord (tag : Int) (p : Expr)
  /-- Test-only selection of the scripted UART profile. The unprofiled
  core gives this statement `undef`; `Sable.SVMUart` supplies its
  profile-specific meaning without changing `Config`. -/
  | testUartProfile (script : Expr)
  /-- Read the selected UART status register into `dst`. As with every
  machine-profile operation, the unprofiled core meaning is `undef`. -/
  | uartStatus (dst : String)
  /-- Write one byte to the selected UART transmitter. The unprofiled
  core meaning is `undef`. -/
  | uartWrite (value : Expr)

/-! ## Environments

One frame of locals. `none` is ⊥ (design §2.3: uninitialized, no default
zero). The model conflates "undeclared" with "declared but ⊥" —
declaration statements are scoped out; reading either is `undef`. -/

def Env := String → Option Val

def Env.empty : Env := fun _ => none

def Env.update (ρ : Env) (x : String) (v : Val) : Env :=
  fun y => if y = x then some v else ρ y

/-- Bind parameters to argument values (left-to-right, later shadows —
duplicate parameter names are checker duty). -/
def Env.bind : Env → List String → List Val → Env
  | ρ, x :: xs, v :: vs => (ρ.update x v).bind xs vs
  | ρ, _, _ => ρ

/-- Bind a call's result at the destination, if any (`f(args)` as a
statement discards it). -/
def Env.bindDst (ρ : Env) (dst : Option String) (v : Val) : Env :=
  match dst with
  | some x => ρ.update x v
  | none => ρ

/-- Return each lent parameter's exit value to the caller's local
(`Arg.lend`). The callee's frame is discarded at the same transition, so
this is the whole trace a unique borrow leaves in the machine.

A parameter is bound when the frame is entered and every statement that
touches it leaves it bound, so `none` is unreachable; leaving the caller's
own binding in place is the total answer that invents no value. -/
def Env.restore (caller : Env) (loans : List (String × String)) (callee : Env) : Env :=
  match loans with
  | [] => caller
  | (p, x) :: rest =>
      (match callee p with
       | some v => caller.update x v
       | none => caller).restore rest callee

/-! ## Programs

A function is parameters plus a body; a program maps names to
functions. Contracts are ghost and erased (§4) — the machine runs
bodies, the verifier proves the contracts. -/

structure FnDef where
  params : List String
  body : List Stmt

def Prog := String → Option FnDef

def Prog.empty : Prog := fun _ => none

/-- Program from an association list (the differential harness's
constructor; first binding wins, duplicates are checker duty). -/
def Prog.ofList (l : List (String × FnDef)) : Prog :=
  fun f => (l.find? (fun p => p.1 = f)).map (·.2)

/-! ## Expression evaluation (big-step) -/

/-- Outcome of evaluating an expression: a value, or an abnormal
outcome (trap / undef). -/
inductive EOut where
  | ok    (v : Val)
  | abort (a : Abort)

/--
`Eval cap ρ e out`: under locals `ρ`, expression `e` evaluates to `out`.

Normative decisions (ADR 0005):
- **Left-to-right operand order**, so the *left* operand's abnormal
  outcome wins; each operand's shape is decided where it is produced
  (a right operand is never evaluated once the left is known ill-shaped).
- **Short-circuit `&&`/`||`**: the right operand (and its abnormal
  outcomes) is unreachable when the left operand decides.
- Reading ⊥ (`ρ x = none`), type confusion, out-of-range literals, and
  negative `alloc_array` lengths (excluded by `u64` typing) evaluate to
  **`undef`** — the machine is total, and the static semantics is
  responsible for making `undef` unreachable.
-/
inductive Eval (cap : Int) : Env → Expr → EOut → Prop where
  -- literals; an out-of-range literal is checker duty, hence undef
  | intLit {ρ : Env} {t : IntTy} {n : Int} (h : t.inRange n) :
      Eval cap ρ (.intLit t n) (.ok (.int n))
  | intLit_undef {ρ : Env} {t : IntTy} {n : Int} (h : ¬ t.inRange n) :
      Eval cap ρ (.intLit t n) (.abort .undef)
  | boolLit {ρ : Env} {b : Bool} :
      Eval cap ρ (.boolLit b) (.ok (.bool b))
  -- variables; reading ⊥ is the canonical undef (§2.3, ADR 0005)
  | var {ρ : Env} {x : String} {v : Val} (h : ρ x = some v) :
      Eval cap ρ (.var x) (.ok v)
  | var_undef {ρ : Env} {x : String} (h : ρ x = none) :
      Eval cap ρ (.var x) (.abort .undef)
  -- unary minus (unary minus on unsigned is a type error — ADR 0005;
  -- the machine still gives the ill-typed term a meaning)
  | neg_ok {ρ : Env} {t : IntTy} {e : Expr} {n : Int}
      (h : Eval cap ρ e (.ok (.int n))) (hr : t.inRange (-n)) :
      Eval cap ρ (.neg t e) (.ok (.int (-n)))
  | neg_overflow {ρ : Env} {t : IntTy} {e : Expr} {n : Int}
      (h : Eval cap ρ e (.ok (.int n))) (hr : ¬ t.inRange (-n)) :
      Eval cap ρ (.neg t e) (.abort (.trap (.overflow t)))
  | neg_undef {ρ : Env} {t : IntTy} {e : Expr} {v : Val}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Eval cap ρ (.neg t e) (.abort .undef)
  | neg_abort {ρ : Env} {t : IntTy} {e : Expr} {a : Abort}
      (h : Eval cap ρ e (.abort a)) :
      Eval cap ρ (.neg t e) (.abort a)
  | not_ok {ρ : Env} {e : Expr} {b : Bool}
      (h : Eval cap ρ e (.ok (.bool b))) :
      Eval cap ρ (.not e) (.ok (.bool (!b)))
  | not_undef {ρ : Env} {e : Expr} {v : Val}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ b, v ≠ .bool b) :
      Eval cap ρ (.not e) (.abort .undef)
  | not_abort {ρ : Env} {e : Expr} {a : Abort}
      (h : Eval cap ρ e (.abort a)) :
      Eval cap ρ (.not e) (.abort a)
  -- checked arithmetic: + - * with the §2.2 representability obligation
  | arith_ok {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b)))
      (hr : t.inRange (op.denote a b)) :
      Eval cap ρ (.arith op t e₁ e₂) (.ok (.int (op.denote a b)))
  | arith_overflow {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b)))
      (hr : ¬ t.inRange (op.denote a b)) :
      Eval cap ρ (.arith op t e₁ e₂) (.abort (.trap (.overflow t)))
  | arith_undef₁ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Eval cap ρ (.arith op t e₁ e₂) (.abort .undef)
  | arith_abort₁ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {a : Abort}
      (h : Eval cap ρ e₁ (.abort a)) :
      Eval cap ρ (.arith op t e₁ e₂) (.abort a)
  | arith_undef₂ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {n : Int} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok v))
      (hv : ∀ m, v ≠ .int m) :
      Eval cap ρ (.arith op t e₁ e₂) (.abort .undef)
  | arith_abort₂ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {n : Int} {a : Abort}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.abort a)) :
      Eval cap ρ (.arith op t e₁ e₂) (.abort a)
  -- wrap(·): total, no overflow rule — but abnormal operands propagate
  | wrap_ok {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b))) :
      Eval cap ρ (.wrapArith op t e₁ e₂) (.ok (.int (t.wrap (op.denote a b))))
  | wrap_undef₁ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Eval cap ρ (.wrapArith op t e₁ e₂) (.abort .undef)
  | wrap_abort₁ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {a : Abort}
      (h : Eval cap ρ e₁ (.abort a)) :
      Eval cap ρ (.wrapArith op t e₁ e₂) (.abort a)
  | wrap_undef₂ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {n : Int} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok v))
      (hv : ∀ m, v ≠ .int m) :
      Eval cap ρ (.wrapArith op t e₁ e₂) (.abort .undef)
  | wrap_abort₂ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {n : Int} {a : Abort}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.abort a)) :
      Eval cap ρ (.wrapArith op t e₁ e₂) (.abort a)
  -- checked(·): none on overflow
  | checked_some {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b)))
      (hr : t.inRange (op.denote a b)) :
      Eval cap ρ (.checkedArith op t e₁ e₂) (.ok (.opt (some (.int (op.denote a b)))))
  | checked_none {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b)))
      (hr : ¬ t.inRange (op.denote a b)) :
      Eval cap ρ (.checkedArith op t e₁ e₂) (.ok (.opt none))
  | checked_undef₁ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Eval cap ρ (.checkedArith op t e₁ e₂) (.abort .undef)
  | checked_abort₁ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {a : Abort}
      (h : Eval cap ρ e₁ (.abort a)) :
      Eval cap ρ (.checkedArith op t e₁ e₂) (.abort a)
  | checked_undef₂ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {n : Int} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok v))
      (hv : ∀ m, v ≠ .int m) :
      Eval cap ρ (.checkedArith op t e₁ e₂) (.abort .undef)
  | checked_abort₂ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {n : Int} {a : Abort}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.abort a)) :
      Eval cap ρ (.checkedArith op t e₁ e₂) (.abort a)
  -- Euclidean division (ADR 0004). The signed MIN / -1 case is the unique
  -- unrepresentable quotient, stated here uniformly as representability.
  | div_ok {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b)))
      (hz : b ≠ 0) (hr : t.inRange (a.ediv b)) :
      Eval cap ρ (.div t e₁ e₂) (.ok (.int (a.ediv b)))
  | div_zero {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {a : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int 0))) :
      Eval cap ρ (.div t e₁ e₂) (.abort (.trap .divByZero))
  | div_overflow {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b)))
      (hz : b ≠ 0) (hr : ¬ t.inRange (a.ediv b)) :
      Eval cap ρ (.div t e₁ e₂) (.abort (.trap (.overflow t)))
  | div_undef₁ {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Eval cap ρ (.div t e₁ e₂) (.abort .undef)
  | div_abort₁ {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {a : Abort}
      (h : Eval cap ρ e₁ (.abort a)) :
      Eval cap ρ (.div t e₁ e₂) (.abort a)
  | div_undef₂ {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {n : Int} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok v))
      (hv : ∀ m, v ≠ .int m) :
      Eval cap ρ (.div t e₁ e₂) (.abort .undef)
  | div_abort₂ {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {n : Int} {a : Abort}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.abort a)) :
      Eval cap ρ (.div t e₁ e₂) (.abort a)
  -- Euclidean remainder: no overflow rule — `emod_inRange` below proves
  -- the result always representable, even at signed extremes.
  | mod_ok {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b)))
      (hz : b ≠ 0) :
      Eval cap ρ (.mod t e₁ e₂) (.ok (.int (a.emod b)))
  | mod_zero {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {a : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int 0))) :
      Eval cap ρ (.mod t e₁ e₂) (.abort (.trap .divByZero))
  | mod_undef₁ {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Eval cap ρ (.mod t e₁ e₂) (.abort .undef)
  | mod_abort₁ {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {a : Abort}
      (h : Eval cap ρ e₁ (.abort a)) :
      Eval cap ρ (.mod t e₁ e₂) (.abort a)
  | mod_undef₂ {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {n : Int} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok v))
      (hv : ∀ m, v ≠ .int m) :
      Eval cap ρ (.mod t e₁ e₂) (.abort .undef)
  | mod_abort₂ {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {n : Int} {a : Abort}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.abort a)) :
      Eval cap ρ (.mod t e₁ e₂) (.abort a)
  -- comparisons (integer operands; `bool ==` is a checker restriction,
  -- so mixed shapes are undef — the machine compares on ℤ)
  | cmp_ok {ρ : Env} {op : CmpOp} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b))) :
      Eval cap ρ (.cmp op e₁ e₂) (.ok (.bool (op.denote a b)))
  | cmp_undef₁ {ρ : Env} {op : CmpOp} {e₁ e₂ : Expr} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Eval cap ρ (.cmp op e₁ e₂) (.abort .undef)
  | cmp_abort₁ {ρ : Env} {op : CmpOp} {e₁ e₂ : Expr} {a : Abort}
      (h : Eval cap ρ e₁ (.abort a)) :
      Eval cap ρ (.cmp op e₁ e₂) (.abort a)
  | cmp_undef₂ {ρ : Env} {op : CmpOp} {e₁ e₂ : Expr} {n : Int} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok v))
      (hv : ∀ m, v ≠ .int m) :
      Eval cap ρ (.cmp op e₁ e₂) (.abort .undef)
  | cmp_abort₂ {ρ : Env} {op : CmpOp} {e₁ e₂ : Expr} {n : Int} {a : Abort}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.abort a)) :
      Eval cap ρ (.cmp op e₁ e₂) (.abort a)
  -- short-circuit && and || (normative, ADR 0005: the guarded-RHS VC
  -- idiom `i < a.len && a[i] > 0` requires it)
  | and_false {ρ : Env} {e₁ e₂ : Expr}
      (h : Eval cap ρ e₁ (.ok (.bool false))) :
      Eval cap ρ (.and e₁ e₂) (.ok (.bool false))
  | and_true {ρ : Env} {e₁ e₂ : Expr} {b : Bool}
      (h₁ : Eval cap ρ e₁ (.ok (.bool true))) (h₂ : Eval cap ρ e₂ (.ok (.bool b))) :
      Eval cap ρ (.and e₁ e₂) (.ok (.bool b))
  | and_undef₁ {ρ : Env} {e₁ e₂ : Expr} {v : Val}
      (h : Eval cap ρ e₁ (.ok v)) (hv : ∀ b, v ≠ .bool b) :
      Eval cap ρ (.and e₁ e₂) (.abort .undef)
  | and_abort₁ {ρ : Env} {e₁ e₂ : Expr} {a : Abort}
      (h : Eval cap ρ e₁ (.abort a)) :
      Eval cap ρ (.and e₁ e₂) (.abort a)
  | and_undef₂ {ρ : Env} {e₁ e₂ : Expr} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok (.bool true))) (h₂ : Eval cap ρ e₂ (.ok v))
      (hv : ∀ b, v ≠ .bool b) :
      Eval cap ρ (.and e₁ e₂) (.abort .undef)
  | and_abort₂ {ρ : Env} {e₁ e₂ : Expr} {a : Abort}
      (h₁ : Eval cap ρ e₁ (.ok (.bool true))) (h₂ : Eval cap ρ e₂ (.abort a)) :
      Eval cap ρ (.and e₁ e₂) (.abort a)
  | or_true {ρ : Env} {e₁ e₂ : Expr}
      (h : Eval cap ρ e₁ (.ok (.bool true))) :
      Eval cap ρ (.or e₁ e₂) (.ok (.bool true))
  | or_false {ρ : Env} {e₁ e₂ : Expr} {b : Bool}
      (h₁ : Eval cap ρ e₁ (.ok (.bool false))) (h₂ : Eval cap ρ e₂ (.ok (.bool b))) :
      Eval cap ρ (.or e₁ e₂) (.ok (.bool b))
  | or_undef₁ {ρ : Env} {e₁ e₂ : Expr} {v : Val}
      (h : Eval cap ρ e₁ (.ok v)) (hv : ∀ b, v ≠ .bool b) :
      Eval cap ρ (.or e₁ e₂) (.abort .undef)
  | or_abort₁ {ρ : Env} {e₁ e₂ : Expr} {a : Abort}
      (h : Eval cap ρ e₁ (.abort a)) :
      Eval cap ρ (.or e₁ e₂) (.abort a)
  | or_undef₂ {ρ : Env} {e₁ e₂ : Expr} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok (.bool false))) (h₂ : Eval cap ρ e₂ (.ok v))
      (hv : ∀ b, v ≠ .bool b) :
      Eval cap ρ (.or e₁ e₂) (.abort .undef)
  | or_abort₂ {ρ : Env} {e₁ e₂ : Expr} {a : Abort}
      (h₁ : Eval cap ρ e₁ (.ok (.bool false))) (h₂ : Eval cap ρ e₂ (.abort a)) :
      Eval cap ρ (.or e₁ e₂) (.abort a)
  -- arrays: length and load; `a.get` is total-with-junk (Sable.Seq) but
  -- the machine only reads it under the bounds check. The index
  -- expression is evaluated before the array lookup (matching stores).
  | len {ρ : Env} {x : String} {t : ValTag} {a : Seq Val}
      (h : ρ x = some (.arr t a)) :
      Eval cap ρ (.len x) (.ok (.int a.len))
  | len_undef {ρ : Env} {x : String}
      (h : ∀ (t : ValTag) (a : Seq Val), ρ x ≠ some (.arr t a)) :
      Eval cap ρ (.len x) (.abort .undef)
  | index_ok {ρ : Env} {x : String} {e : Expr} {t : ValTag} {a : Seq Val} {n : Int}
      (hi : Eval cap ρ e (.ok (.int n))) (ha : ρ x = some (.arr t a))
      (h₀ : 0 ≤ n) (h₁ : n < a.len) :
      Eval cap ρ (.index x e) (.ok (a.get n))
  | index_oob {ρ : Env} {x : String} {e : Expr} {t : ValTag} {a : Seq Val} {n : Int}
      (hi : Eval cap ρ e (.ok (.int n))) (ha : ρ x = some (.arr t a))
      (h : n < 0 ∨ a.len ≤ n) :
      Eval cap ρ (.index x e) (.abort (.trap (.indexOOB n a.len)))
  | index_undef_idx {ρ : Env} {x : String} {e : Expr} {v : Val}
      (hi : Eval cap ρ e (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Eval cap ρ (.index x e) (.abort .undef)
  | index_abort {ρ : Env} {x : String} {e : Expr} {a : Abort}
      (h : Eval cap ρ e (.abort a)) :
      Eval cap ρ (.index x e) (.abort a)
  | index_undef_arr {ρ : Env} {x : String} {e : Expr} {n : Int}
      (hi : Eval cap ρ e (.ok (.int n)))
      (ha : ∀ (t : ValTag) (a : Seq Val), ρ x ≠ some (.arr t a)) :
      Eval cap ρ (.index x e) (.abort .undef)
  -- widen: total and, on the exact-Int value plane, the identity
  | widen_ok {ρ : Env} {dst : IntTy} {e : Expr} {n : Int}
      (h : Eval cap ρ e (.ok (.int n))) :
      Eval cap ρ (.widen dst e) (.ok (.int n))
  | widen_undef {ρ : Env} {dst : IntTy} {e : Expr} {v : Val}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Eval cap ρ (.widen dst e) (.abort .undef)
  | widen_abort {ρ : Env} {dst : IntTy} {e : Expr} {a : Abort}
      (h : Eval cap ρ e (.abort a)) :
      Eval cap ρ (.widen dst e) (.abort a)
  -- narrow<T>: the §2.2 fits-obligation; trap when deferred
  | narrow_ok {ρ : Env} {dst : IntTy} {e : Expr} {n : Int}
      (h : Eval cap ρ e (.ok (.int n))) (hr : dst.inRange n) :
      Eval cap ρ (.narrow dst e) (.ok (.int n))
  | narrow_oob {ρ : Env} {dst : IntTy} {e : Expr} {n : Int}
      (h : Eval cap ρ e (.ok (.int n))) (hr : ¬ dst.inRange n) :
      Eval cap ρ (.narrow dst e) (.abort (.trap (.narrowOOB dst n)))
  | narrow_undef {ρ : Env} {dst : IntTy} {e : Expr} {v : Val}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Eval cap ρ (.narrow dst e) (.abort .undef)
  | narrow_abort {ρ : Env} {dst : IntTy} {e : Expr} {a : Abort}
      (h : Eval cap ρ e (.abort a)) :
      Eval cap ρ (.narrow dst e) (.abort a)
  -- alloc_array(n, v): OOM is a defined trap (§10), decided against the
  -- machine's capacity parameter. Negative length is excluded by `u64`
  -- typing (ADR 0005), hence undef.
  -- pointer arithmetic: no heap access, hence no bounds question here
  | ptrAdd_ok {ρ : Env} {ep ed : Expr} {a k d : Int}
      (hp : Eval cap ρ ep (.ok (.ptr a k))) (hd : Eval cap ρ ed (.ok (.int d))) :
      Eval cap ρ (.ptrAdd ep ed) (.ok (.ptr a (k + d)))
  | ptrAdd_undef₁ {ρ : Env} {ep ed : Expr} {v : Val}
      (hp : Eval cap ρ ep (.ok v)) (hv : ∀ a k, v ≠ .ptr a k) :
      Eval cap ρ (.ptrAdd ep ed) (.abort .undef)
  | ptrAdd_abort₁ {ρ : Env} {ep ed : Expr} {a : Abort}
      (hp : Eval cap ρ ep (.abort a)) :
      Eval cap ρ (.ptrAdd ep ed) (.abort a)
  | ptrAdd_undef₂ {ρ : Env} {ep ed : Expr} {a k : Int} {v : Val}
      (hp : Eval cap ρ ep (.ok (.ptr a k))) (hd : Eval cap ρ ed (.ok v))
      (hv : ∀ d, v ≠ .int d) :
      Eval cap ρ (.ptrAdd ep ed) (.abort .undef)
  | ptrAdd_abort₂ {ρ : Env} {ep ed : Expr} {a k : Int} {ab : Abort}
      (hp : Eval cap ρ ep (.ok (.ptr a k))) (hd : Eval cap ρ ed (.abort ab)) :
      Eval cap ρ (.ptrAdd ep ed) (.abort ab)
  -- Pure raw-pointer observations and nullable raw-pointer values.
  | ptrOffset_ok {ρ : Env} {e : Expr} {a k : Int}
      (h : Eval cap ρ e (.ok (.ptr a k))) :
      Eval cap ρ (.ptrOffset e) (.ok (.int k))
  | ptrOffset_undef {ρ : Env} {e : Expr} {v : Val}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ a k, v ≠ .ptr a k) :
      Eval cap ρ (.ptrOffset e) (.abort .undef)
  | ptrOffset_abort {ρ : Env} {e : Expr} {ab : Abort}
      (h : Eval cap ρ e (.abort ab)) :
      Eval cap ρ (.ptrOffset e) (.abort ab)
  | recordField_ok {ρ : Env} {e : Expr} {field : String} {v value : Val}
      (h : Eval cap ρ e (.ok v)) (hf : v.recordField? field = some value) :
      Eval cap ρ (.recordField e field) (.ok value)
  | recordField_undef {ρ : Env} {e : Expr} {field : String} {v : Val}
      (h : Eval cap ρ e (.ok v)) (hf : v.recordField? field = none) :
      Eval cap ρ (.recordField e field) (.abort .undef)
  | recordField_abort {ρ : Env} {e : Expr} {field : String} {ab : Abort}
      (h : Eval cap ρ e (.abort ab)) :
      Eval cap ρ (.recordField e field) (.abort ab)
  | alloc_ok {ρ : Env} {e₁ e₂ : Expr} {n : Int} {v : Val} {t : ValTag}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok v))
      (ht : v.tag? = some t) (h₀ : 0 ≤ n) (hc : n ≤ cap) :
      Eval cap ρ (.allocArray e₁ e₂) (.ok (.arr t (Seq.replicate n v)))
  -- The abnormal lengths still demand an admissible element: an element the
  -- machine cannot put in an array is `undef` (`alloc_undef₂`) whatever the
  -- length is, so these rules need the element admitted but never need the
  -- domain it was admitted into.
  | alloc_oom {ρ : Env} {e₁ e₂ : Expr} {n : Int} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok v))
      (ht : v.tag? ≠ none) (h₀ : 0 ≤ n) (hc : cap < n) :
      Eval cap ρ (.allocArray e₁ e₂) (.abort (.trap (.oom n)))
  | alloc_neg {ρ : Env} {e₁ e₂ : Expr} {n : Int} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok v))
      (ht : v.tag? ≠ none) (h₀ : n < 0) :
      Eval cap ρ (.allocArray e₁ e₂) (.abort .undef)
  | alloc_undef₁ {ρ : Env} {e₁ e₂ : Expr} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Eval cap ρ (.allocArray e₁ e₂) (.abort .undef)
  | alloc_abort₁ {ρ : Env} {e₁ e₂ : Expr} {a : Abort}
      (h : Eval cap ρ e₁ (.abort a)) :
      Eval cap ρ (.allocArray e₁ e₂) (.abort a)
  | alloc_undef₂ {ρ : Env} {e₁ e₂ : Expr} {n : Int} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok v))
      (hv : v.tag? = none) :
      Eval cap ρ (.allocArray e₁ e₂) (.abort .undef)
  | alloc_abort₂ {ρ : Env} {e₁ e₂ : Expr} {n : Int} {a : Abort}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.abort a)) :
      Eval cap ρ (.allocArray e₁ e₂) (.abort a)
  -- Ordinary options contain values recursively. Shape is checked only by
  -- the accessors: `some(e)` accepts every value that `e` can produce.
  | someE_ok {ρ : Env} {e : Expr} {v : Val}
      (h : Eval cap ρ e (.ok v)) :
      Eval cap ρ (.someE e) (.ok (.opt (some v)))
  | someE_abort {ρ : Env} {e : Expr} {a : Abort}
      (h : Eval cap ρ e (.abort a)) :
      Eval cap ρ (.someE e) (.abort a)
  | noneE {ρ : Env} :
      Eval cap ρ .noneE (.ok (.opt none))
  | optIsSome_ok {ρ : Env} {e : Expr} {o : Option Val}
      (h : Eval cap ρ e (.ok (.opt o))) :
      Eval cap ρ (.optIsSome e) (.ok (.bool o.isSome))
  | optIsSome_undef {ρ : Env} {e : Expr} {v : Val}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ o, v ≠ .opt o) :
      Eval cap ρ (.optIsSome e) (.abort .undef)
  | optIsSome_abort {ρ : Env} {e : Expr} {a : Abort}
      (h : Eval cap ρ e (.abort a)) :
      Eval cap ρ (.optIsSome e) (.abort a)
  | optValue_ok {ρ : Env} {e : Expr} {v : Val}
      (h : Eval cap ρ e (.ok (.opt (some v)))) :
      Eval cap ρ (.optValue e) (.ok v)
  | optValue_none {ρ : Env} {e : Expr}
      (h : Eval cap ρ e (.ok (.opt none))) :
      Eval cap ρ (.optValue e) (.abort (.trap .optionNone))
  | optValue_undef {ρ : Env} {e : Expr} {v : Val}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ o, v ≠ .opt o) :
      Eval cap ρ (.optValue e) (.abort .undef)
  | optValue_abort {ρ : Env} {e : Expr} {a : Abort}
      (h : Eval cap ρ e (.abort a)) :
      Eval cap ρ (.optValue e) (.abort a)

/-- Outcome of evaluating an argument list. -/
inductive AOut where
  | ok    (vs : List Val)
  | abort (a : Abort)

/-- `EvalArgs cap ρ es out`: left-to-right evaluation of a call's
arguments; the first abnormal outcome wins, and nothing to its right
is evaluated. -/
inductive EvalArgs (cap : Int) (ρ : Env) : List Expr → AOut → Prop where
  | nil : EvalArgs cap ρ [] (.ok [])
  | cons_ok {e : Expr} {es : List Expr} {v : Val} {vs : List Val}
      (h : Eval cap ρ e (.ok v)) (hs : EvalArgs cap ρ es (.ok vs)) :
      EvalArgs cap ρ (e :: es) (.ok (v :: vs))
  | cons_abort {e : Expr} {es : List Expr} {a : Abort}
      (h : Eval cap ρ e (.abort a)) :
      EvalArgs cap ρ (e :: es) (.abort a)
  | cons_abort_tail {e : Expr} {es : List Expr} {v : Val} {a : Abort}
      (h : Eval cap ρ e (.ok v)) (hs : EvalArgs cap ρ es (.abort a)) :
      EvalArgs cap ρ (e :: es) (.abort a)

/-! ## Configurations and the small-step relation -/

/-- A suspended caller: where the result goes, what runs next, the
caller's locals, and where this call's lent arguments return to
(`Arg.loans`). -/
structure Frame where
  dst : Option String
  k   : List Stmt
  ρ   : Env
  loans : List (String × String)

/-- A configuration: either running (a continuation of statements, the
current frame's locals, the stack of suspended callers, and the raw
heap — design §10's ⟨code, frames, heap, ghost⟩ with the *safe* heap
absorbed into owned array values, the raw heap explicit, and the ghost
component scoped out), or one of the three terminal outcomes
(ADR 0005): normal termination, a trap, or `undef`.

Every rule that is not a raw operation threads `μ` unchanged. That is
not an accident of the encoding — it is the claim that unsafe Sable adds
a component rather than reinterpreting the machine. -/
inductive Config where
  | run     (k : List Stmt) (ρ : Env) (σ : List Frame) (μ : RawHeap)
  | done    (v : Val)
  | trapped (t : Trap)
  | undef

/-- The terminal configuration an abnormal expression outcome forces. -/
def Abort.toConfig : Abort → Config
  | .trap t => .trapped t
  | .undef  => .undef

/--
`Step P cap c c'`: one machine step of program `P`. Small-step,
deterministic, and total on `run` configurations (§10, ADR 0005) —
determinism and progress are theorems (`Sable/SVMEval.lean`), via
agreement with the functional evaluator.

Normative decisions (ADR 0005):
- `store`: index evaluated, then value, then the bounds check — the
  value's trap beats the OOB trap, matching `interp.rs`.
- `while` unfolds to its body plus itself: loops run by unfolding, the
  invariant/variant having been erased.
- `call`: callee looked up first (an unknown callee is `undef` before
  any argument runs), then arguments left-to-right, then the arity
  check (a mismatch is checker duty, hence `undef`); the callee starts
  from an empty frame with only its parameters bound. A lent argument
  (`Arg.lend`) enters as the value of the local it names and is recorded
  in the frame as a loan.
- `ret` in a callee returns its loans to the caller's locals, pops the
  caller's frame, and binds the destination; at the bottom of the stack
  it is the program's answer. Falling off the end of a body returns
  `unit` the same two ways (procedures are blessed, cf. `swap` §5), and
  returns its loans the same way — a `&mut` parameter is written through
  by a procedure at least as often as by a function.
-/
inductive Step (P : Prog) (cap : Int) : Config → Config → Prop where
  | assign_ok {ρ : Env} {x : String} {e : Expr} {v : Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) :
      Step P cap (.run (.assign x e :: k) ρ σ μ) (.run k (ρ.update x v) σ μ)
  | assign_abort {ρ : Env} {x : String} {e : Expr} {a : Abort} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort a)) :
      Step P cap (.run (.assign x e :: k) ρ σ μ) a.toConfig
  -- Affine option extraction is atomic. The source is cleared before the
  -- destination is installed, and distinct names ensure the latter update
  -- cannot recreate the option owner. Destination freshness is deliberately
  -- not required: flat machine environments reuse lexical-local names across
  -- loop iterations.
  | optTake_ok {ρ : Env} {dst src : String} {value : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hne : dst ≠ src) (hs : ρ src = some (.opt (some value))) :
      Step P cap (.run (.optTake dst src :: k) ρ σ μ)
        (.run k ((ρ.update src (.opt none)).update dst value) σ μ)
  | optTake_none {ρ : Env} {dst src : String}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hne : dst ≠ src) (hs : ρ src = some (.opt none)) :
      Step P cap (.run (.optTake dst src :: k) ρ σ μ) (.trapped .optionNone)
  | optTake_undef_alias {ρ : Env} {dst src : String}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (heq : dst = src) :
      Step P cap (.run (.optTake dst src :: k) ρ σ μ) .undef
  | optTake_undef_src {ρ : Env} {dst src : String}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hne : dst ≠ src) (hs : ∀ value, ρ src ≠ some (.opt value)) :
      Step P cap (.run (.optTake dst src :: k) ρ σ μ) .undef
  | recordMake_ok {ρ : Env} {dst : String} {tag : Int}
      {fields : List String} {args : List Expr} {values : List Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (ha : EvalArgs cap ρ args (.ok values))
      (hn : fields.length = values.length) :
      Step P cap (.run (.recordMake dst tag fields args :: k) ρ σ μ)
        (.run k (ρ.update dst (.record tag (fields.zip values))) σ μ)
  | recordMake_undef_arity {ρ : Env} {dst : String} {tag : Int}
      {fields : List String} {args : List Expr} {values : List Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (ha : EvalArgs cap ρ args (.ok values))
      (hn : fields.length ≠ values.length) :
      Step P cap (.run (.recordMake dst tag fields args :: k) ρ σ μ) .undef
  | recordMake_abort {ρ : Env} {dst : String} {tag : Int}
      {fields : List String} {args : List Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (ha : EvalArgs cap ρ args (.abort ab)) :
      Step P cap (.run (.recordMake dst tag fields args :: k) ρ σ μ) ab.toConfig
  -- The store rules check the value's shape before they look the array up:
  -- a value no array can hold is `undef` (`store_undef_val`) before `x` is
  -- consulted, and a value some array can hold but *this* one cannot is
  -- `undef` (`store_undef_tag`) even when the index is out of bounds. `hw`
  -- states that first check in every store rule — in `store_ok`/`store_oob`
  -- it also follows from `hs` — and no rule needs *which* domain admitted
  -- the value, only that one did.
  | store_ok {ρ : Env} {x : String} {ei ev : Expr} {n : Int} {w : Val}
      {t : ValTag} {a a' : Seq Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hi : Eval cap ρ ei (.ok (.int n))) (hv : Eval cap ρ ev (.ok w))
      (hw : w.tag? ≠ none)
      (ha : ρ x = some (.arr t a)) (hs : Val.arrSet? t a n w = some a')
      (h₀ : 0 ≤ n) (h₁ : n < a.len) :
      Step P cap (.run (.store x ei ev :: k) ρ σ μ)
        (.run k (ρ.update x (.arr t a')) σ μ)
  | store_oob {ρ : Env} {x : String} {ei ev : Expr} {n : Int} {w : Val}
      {t : ValTag} {a a' : Seq Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hi : Eval cap ρ ei (.ok (.int n))) (hv : Eval cap ρ ev (.ok w))
      (hw : w.tag? ≠ none)
      (ha : ρ x = some (.arr t a)) (hs : Val.arrSet? t a n w = some a')
      (h : n < 0 ∨ a.len ≤ n) :
      Step P cap (.run (.store x ei ev :: k) ρ σ μ) (.trapped (.indexOOB n a.len))
  | store_abort_idx {ρ : Env} {x : String} {ei ev : Expr} {a : Abort} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hi : Eval cap ρ ei (.abort a)) :
      Step P cap (.run (.store x ei ev :: k) ρ σ μ) a.toConfig
  | store_undef_idx {ρ : Env} {x : String} {ei ev : Expr} {v : Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hi : Eval cap ρ ei (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Step P cap (.run (.store x ei ev :: k) ρ σ μ) .undef
  | store_abort_val {ρ : Env} {x : String} {ei ev : Expr} {n : Int} {a : Abort} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hi : Eval cap ρ ei (.ok (.int n))) (hv : Eval cap ρ ev (.abort a)) :
      Step P cap (.run (.store x ei ev :: k) ρ σ μ) a.toConfig
  | store_undef_val {ρ : Env} {x : String} {ei ev : Expr} {n : Int} {v : Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hi : Eval cap ρ ei (.ok (.int n))) (hv : Eval cap ρ ev (.ok v))
      (hw : v.tag? = none) :
      Step P cap (.run (.store x ei ev :: k) ρ σ μ) .undef
  | store_undef_arr {ρ : Env} {x : String} {ei ev : Expr} {n : Int} {w : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hi : Eval cap ρ ei (.ok (.int n))) (hv : Eval cap ρ ev (.ok w))
      (hw : w.tag? ≠ none)
      (ha : ∀ (t : ValTag) (a : Seq Val), ρ x ≠ some (.arr t a)) :
      Step P cap (.run (.store x ei ev :: k) ρ σ μ) .undef
  | store_undef_tag {ρ : Env} {x : String} {ei ev : Expr} {n : Int} {w : Val}
      {t : ValTag} {a : Seq Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hi : Eval cap ρ ei (.ok (.int n))) (hv : Eval cap ρ ev (.ok w))
      (hw : w.tag? ≠ none)
      (ha : ρ x = some (.arr t a)) (hs : Val.arrSet? t a n w = none) :
      Step P cap (.run (.store x ei ev :: k) ρ σ μ) .undef
  | ite_true {ρ : Env} {c : Expr} {thn els k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ c (.ok (.bool true))) :
      Step P cap (.run (.ite c thn els :: k) ρ σ μ) (.run (thn ++ k) ρ σ μ)
  | ite_false {ρ : Env} {c : Expr} {thn els k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ c (.ok (.bool false))) :
      Step P cap (.run (.ite c thn els :: k) ρ σ μ) (.run (els ++ k) ρ σ μ)
  | ite_undef {ρ : Env} {c : Expr} {thn els k : List Stmt} {v : Val} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ c (.ok v)) (hv : ∀ b, v ≠ .bool b) :
      Step P cap (.run (.ite c thn els :: k) ρ σ μ) .undef
  | ite_abort {ρ : Env} {c : Expr} {thn els k : List Stmt} {a : Abort} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ c (.abort a)) :
      Step P cap (.run (.ite c thn els :: k) ρ σ μ) a.toConfig
  | while_true {ρ : Env} {c : Expr} {body k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ c (.ok (.bool true))) :
      Step P cap (.run (.while c body :: k) ρ σ μ) (.run (body ++ .while c body :: k) ρ σ μ)
  | while_false {ρ : Env} {c : Expr} {body k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ c (.ok (.bool false))) :
      Step P cap (.run (.while c body :: k) ρ σ μ) (.run k ρ σ μ)
  | while_undef {ρ : Env} {c : Expr} {body k : List Stmt} {v : Val} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ c (.ok v)) (hv : ∀ b, v ≠ .bool b) :
      Step P cap (.run (.while c body :: k) ρ σ μ) .undef
  | while_abort {ρ : Env} {c : Expr} {body k : List Stmt} {a : Abort} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ c (.abort a)) :
      Step P cap (.run (.while c body :: k) ρ σ μ) a.toConfig
  -- compiled `defer` (§9): "true or halt", carrying the obligation name
  | check_pass {ρ : Env} {name : String} {c : Expr} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ c (.ok (.bool true))) :
      Step P cap (.run (.check name c :: k) ρ σ μ) (.run k ρ σ μ)
  | check_fail {ρ : Env} {name : String} {c : Expr} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ c (.ok (.bool false))) :
      Step P cap (.run (.check name c :: k) ρ σ μ) (.trapped (.deferViolation name))
  | check_undef {ρ : Env} {name : String} {c : Expr} {k : List Stmt} {v : Val} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ c (.ok v)) (hv : ∀ b, v ≠ .bool b) :
      Step P cap (.run (.check name c :: k) ρ σ μ) .undef
  | check_abort {ρ : Env} {name : String} {c : Expr} {k : List Stmt} {a : Abort} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ c (.abort a)) :
      Step P cap (.run (.check name c :: k) ρ σ μ) a.toConfig
  -- calls (A-normal, ADR 0005): lookup, then arguments, then arity
  | call_undef_fn {ρ : Env} {dst : Option String} {f : String} {args : List Arg} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hf : P f = none) :
      Step P cap (.run (.call dst f args :: k) ρ σ μ) .undef
  | call_abort {ρ : Env} {dst : Option String} {f : String} {args : List Arg} {fd : FnDef} {a : Abort} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hf : P f = some fd) (ha : EvalArgs cap ρ (args.map Arg.toExpr) (.abort a)) :
      Step P cap (.run (.call dst f args :: k) ρ σ μ) a.toConfig
  | call_undef_arity {ρ : Env} {dst : Option String} {f : String} {args : List Arg} {fd : FnDef} {vs : List Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hf : P f = some fd) (ha : EvalArgs cap ρ (args.map Arg.toExpr) (.ok vs))
      (hn : fd.params.length ≠ vs.length) :
      Step P cap (.run (.call dst f args :: k) ρ σ μ) .undef
  | call_enter {ρ : Env} {dst : Option String} {f : String} {args : List Arg} {fd : FnDef} {vs : List Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hf : P f = some fd) (ha : EvalArgs cap ρ (args.map Arg.toExpr) (.ok vs))
      (hn : fd.params.length = vs.length) :
      Step P cap (.run (.call dst f args :: k) ρ σ μ)
        (.run fd.body (Env.empty.bind fd.params vs)
          (⟨dst, k, ρ, Arg.loans fd.params args⟩ :: σ) μ)
  -- returns: pop a caller, or answer the program
  | ret_ok {ρ : Env} {e : Expr} {v : Val} {k : List Stmt} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) :
      Step P cap (.run (.ret e :: k) ρ [] μ) (.done v)
  | ret_pop {ρ : Env} {e : Expr} {v : Val} {k : List Stmt} {fr : Frame} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) :
      Step P cap (.run (.ret e :: k) ρ (fr :: σ) μ)
        (.run fr.k ((fr.ρ.restore fr.loans ρ).bindDst fr.dst v) σ μ)
  | ret_abort {ρ : Env} {e : Expr} {a : Abort} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort a)) :
      Step P cap (.run (.ret e :: k) ρ σ μ) a.toConfig
  -- raw allocation: fresh provenance, uninitialized bytes
  | alloc_ok {ρ : Env} {dst : String} {e : Expr} {n : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.int n))) (h₀ : 0 ≤ n) (hc : n ≤ cap) :
      Step P cap (.run (.rawAlloc dst e :: k) ρ σ μ)
        (.run k (ρ.update dst (.ptr μ.next 0)) σ (μ.fresh n))
  | alloc_oom {ρ : Env} {dst : String} {e : Expr} {n : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.int n))) (h₀ : 0 ≤ n) (hc : cap < n) :
      Step P cap (.run (.rawAlloc dst e :: k) ρ σ μ) (.trapped (.oom n))
  | alloc_neg {ρ : Env} {dst : String} {e : Expr} {n : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.int n))) (h₀ : n < 0) :
      Step P cap (.run (.rawAlloc dst e :: k) ρ σ μ) .undef
  | alloc_undef_size {ρ : Env} {dst : String} {e : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Step P cap (.run (.rawAlloc dst e :: k) ρ σ μ) .undef
  | alloc_abort {ρ : Env} {dst : String} {e : Expr} {a : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort a)) :
      Step P cap (.run (.rawAlloc dst e :: k) ρ σ μ) a.toConfig
  -- free: the pointer must name the start of a live allocation
  | free_ok {ρ : Env} {e : Expr} {a k' : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hf : μ.freeable a k' = true) :
      Step P cap (.run (.rawFree e :: k) ρ σ μ) (.run k ρ σ (μ.release a))
  | free_undef_dead {ρ : Env} {e : Expr} {a k' : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hf : μ.freeable a k' = false) :
      Step P cap (.run (.rawFree e :: k) ρ σ μ) .undef
  | free_undef_ptr {ρ : Env} {e : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawFree e :: k) ρ σ μ) .undef
  | free_abort {ρ : Env} {e : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort ab)) :
      Step P cap (.run (.rawFree e :: k) ρ σ μ) ab.toConfig
  -- load8: in bounds, live, and initialized
  | load8_ok {ρ : Env} {dst : String} {e : Expr} {a k' b : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hb : μ.loadByte a k' = some b) :
      Step P cap (.run (.rawLoad8 dst e :: k) ρ σ μ)
        (.run k (ρ.update dst (.int b)) σ μ)
  | load8_undef_byte {ρ : Env} {dst : String} {e : Expr} {a k' : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hb : μ.loadByte a k' = none) :
      Step P cap (.run (.rawLoad8 dst e :: k) ρ σ μ) .undef
  | load8_undef_ptr {ρ : Env} {dst : String} {e : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawLoad8 dst e :: k) ρ σ μ) .undef
  | load8_abort {ρ : Env} {dst : String} {e : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort ab)) :
      Step P cap (.run (.rawLoad8 dst e :: k) ρ σ μ) ab.toConfig
  -- store8: in bounds and live; the byte becomes initialized. An
  -- out-of-`u8`-range value is checker duty, hence undef.
  | store8_ok {ρ : Env} {ep ev : Expr} {a k' w : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.ok (.ptr a k'))) (hv : Eval cap ρ ev (.ok (.int w)))
      (hr : IntTy.u8.inRange w) (hb : μ.inBounds a k' = true) :
      Step P cap (.run (.rawStore8 ep ev :: k) ρ σ μ)
        (.run k ρ σ (μ.store a k' (.init w)))
  | store8_undef_addr {ρ : Env} {ep ev : Expr} {a k' w : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.ok (.ptr a k'))) (hv : Eval cap ρ ev (.ok (.int w)))
      (hbad : ¬ IntTy.u8.inRange w ∨ μ.inBounds a k' = false) :
      Step P cap (.run (.rawStore8 ep ev :: k) ρ σ μ) .undef
  | store8_undef_val {ρ : Env} {ep ev : Expr} {a k' : Int} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.ok (.ptr a k'))) (hv : Eval cap ρ ev (.ok v))
      (hw : ∀ w, v ≠ .int w) :
      Step P cap (.run (.rawStore8 ep ev :: k) ρ σ μ) .undef
  | store8_abort_val {ρ : Env} {ep ev : Expr} {a k' : Int} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.ok (.ptr a k'))) (hv : Eval cap ρ ev (.abort ab)) :
      Step P cap (.run (.rawStore8 ep ev :: k) ρ σ μ) ab.toConfig
  | store8_undef_ptr {ρ : Env} {ep ev : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawStore8 ep ev :: k) ρ σ μ) .undef
  | store8_abort_ptr {ρ : Env} {ep ev : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.abort ab)) :
      Step P cap (.run (.rawStore8 ep ev :: k) ρ σ μ) ab.toConfig
  -- take8: load, and leave the storage uninitialized
  | take8_ok {ρ : Env} {dst : String} {e : Expr} {a k' b : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hb : μ.loadByte a k' = some b) :
      Step P cap (.run (.rawTake8 dst e :: k) ρ σ μ)
        (.run k (ρ.update dst (.int b)) σ (μ.store a k' .uninit))
  | take8_undef_byte {ρ : Env} {dst : String} {e : Expr} {a k' : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hb : μ.loadByte a k' = none) :
      Step P cap (.run (.rawTake8 dst e :: k) ρ σ μ) .undef
  | take8_undef_ptr {ρ : Env} {dst : String} {e : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawTake8 dst e :: k) ρ σ μ) .undef
  | take8_abort {ρ : Env} {dst : String} {e : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort ab)) :
      Step P cap (.run (.rawTake8 dst e :: k) ρ σ μ) ab.toConfig
  -- typed u64 cells (ADR 0031): role conversion is explicit, and byte
  -- operations cannot observe an extent while its typed tag is present.
  | intoCellU64_ok {ρ : Env} {e : Expr} {a k' : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hc : μ.cellConvertibleU64 a k' = true) :
      Step P cap (.run (.rawIntoCellU64 e :: k) ρ σ μ)
        (.run k ρ σ (μ.putCellU64 a k' none))
  | intoCellU64_bad {ρ : Env} {e : Expr} {a k' : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hc : μ.cellConvertibleU64 a k' = false) :
      Step P cap (.run (.rawIntoCellU64 e :: k) ρ σ μ) .undef
  | intoCellU64_undef_ptr {ρ : Env} {e : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawIntoCellU64 e :: k) ρ σ μ) .undef
  | intoCellU64_abort {ρ : Env} {e : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort ab)) :
      Step P cap (.run (.rawIntoCellU64 e :: k) ρ σ μ) ab.toConfig
  | fromCellU64_ok {ρ : Env} {e : Expr} {a k' : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hc : μ.cellAtU64 a k' = some none) :
      Step P cap (.run (.rawFromCellU64 e :: k) ρ σ μ)
        (.run k ρ σ (μ.removeCellU64 a k'))
  | fromCellU64_bad {ρ : Env} {e : Expr} {a k' : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hc : μ.cellAtU64 a k' ≠ some none) :
      Step P cap (.run (.rawFromCellU64 e :: k) ρ σ μ) .undef
  | fromCellU64_undef_ptr {ρ : Env} {e : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawFromCellU64 e :: k) ρ σ μ) .undef
  | fromCellU64_abort {ρ : Env} {e : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort ab)) :
      Step P cap (.run (.rawFromCellU64 e :: k) ρ σ μ) ab.toConfig
  | cellInitU64_ok {ρ : Env} {ep ev : Expr} {a k' w : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.ok (.ptr a k'))) (hv : Eval cap ρ ev (.ok (.int w)))
      (hr : IntTy.u64.inRange w) (hc : μ.cellAtU64 a k' = some none) :
      Step P cap (.run (.rawCellInitU64 ep ev :: k) ρ σ μ)
        (.run k ρ σ (μ.putCellU64 a k' (some w)))
  | cellInitU64_bad {ρ : Env} {ep ev : Expr} {a k' w : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.ok (.ptr a k'))) (hv : Eval cap ρ ev (.ok (.int w)))
      (hbad : ¬ IntTy.u64.inRange w ∨ μ.cellAtU64 a k' ≠ some none) :
      Step P cap (.run (.rawCellInitU64 ep ev :: k) ρ σ μ) .undef
  | cellInitU64_undef_val {ρ : Env} {ep ev : Expr} {a k' : Int} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.ok (.ptr a k'))) (hv : Eval cap ρ ev (.ok v))
      (hw : ∀ w, v ≠ .int w) :
      Step P cap (.run (.rawCellInitU64 ep ev :: k) ρ σ μ) .undef
  | cellInitU64_abort_val {ρ : Env} {ep ev : Expr} {a k' : Int} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.ok (.ptr a k'))) (hv : Eval cap ρ ev (.abort ab)) :
      Step P cap (.run (.rawCellInitU64 ep ev :: k) ρ σ μ) ab.toConfig
  | cellInitU64_undef_ptr {ρ : Env} {ep ev : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawCellInitU64 ep ev :: k) ρ σ μ) .undef
  | cellInitU64_abort_ptr {ρ : Env} {ep ev : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.abort ab)) :
      Step P cap (.run (.rawCellInitU64 ep ev :: k) ρ σ μ) ab.toConfig
  | cellReadU64_ok {ρ : Env} {dst : String} {e : Expr} {a k' w : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hc : μ.cellAtU64 a k' = some (some w)) :
      Step P cap (.run (.rawCellReadU64 dst e :: k) ρ σ μ)
        (.run k (ρ.update dst (.int w)) σ μ)
  | cellReadU64_bad {ρ : Env} {dst : String} {e : Expr} {a k' : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hc : ∀ w, μ.cellAtU64 a k' ≠ some (some w)) :
      Step P cap (.run (.rawCellReadU64 dst e :: k) ρ σ μ) .undef
  | cellReadU64_undef_ptr {ρ : Env} {dst : String} {e : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawCellReadU64 dst e :: k) ρ σ μ) .undef
  | cellReadU64_abort {ρ : Env} {dst : String} {e : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort ab)) :
      Step P cap (.run (.rawCellReadU64 dst e :: k) ρ σ μ) ab.toConfig
  | cellTakeU64_ok {ρ : Env} {dst : String} {e : Expr} {a k' w : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hc : μ.cellAtU64 a k' = some (some w)) :
      Step P cap (.run (.rawCellTakeU64 dst e :: k) ρ σ μ)
        (.run k (ρ.update dst (.int w)) σ (μ.putCellU64 a k' none))
  | cellTakeU64_bad {ρ : Env} {dst : String} {e : Expr} {a k' : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hc : ∀ w, μ.cellAtU64 a k' ≠ some (some w)) :
      Step P cap (.run (.rawCellTakeU64 dst e :: k) ρ σ μ) .undef
  | cellTakeU64_undef_ptr {ρ : Env} {dst : String} {e : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawCellTakeU64 dst e :: k) ρ σ μ) .undef
  | cellTakeU64_abort {ρ : Env} {dst : String} {e : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort ab)) :
      Step P cap (.run (.rawCellTakeU64 dst e :: k) ρ σ μ) ab.toConfig
  | cellDropU64_ok {ρ : Env} {e : Expr} {a k' w : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hc : μ.cellAtU64 a k' = some (some w)) :
      Step P cap (.run (.rawCellDropU64 e :: k) ρ σ μ)
        (.run k ρ σ (μ.putCellU64 a k' none))
  | cellDropU64_bad {ρ : Env} {e : Expr} {a k' : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k'))) (hc : ∀ w, μ.cellAtU64 a k' ≠ some (some w)) :
      Step P cap (.run (.rawCellDropU64 e :: k) ρ σ μ) .undef
  | cellDropU64_undef_ptr {ρ : Env} {e : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawCellDropU64 e :: k) ρ σ μ) .undef
  | cellDropU64_abort {ρ : Env} {e : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort ab)) :
      Step P cap (.run (.rawCellDropU64 e :: k) ρ σ μ) ab.toConfig
  -- Abstract record cells (ADR 0054): the layout and record tag are explicit
  -- machine operands; values remain abstract and byte-inaccessible.
  | intoCellRecord_ok {ρ : Env} {tag size align : Int} {e : Expr} {a k' : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k')))
      (hc : μ.cellConvertibleRecord a k' size align = true) :
      Step P cap (.run (.rawIntoCellRecord tag size align e :: k) ρ σ μ)
        (.run k ρ σ (μ.putRecordCell a k' tag size align))
  | intoCellRecord_bad {ρ : Env} {tag size align : Int} {e : Expr} {a k' : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k')))
      (hc : μ.cellConvertibleRecord a k' size align = false) :
      Step P cap (.run (.rawIntoCellRecord tag size align e :: k) ρ σ μ) .undef
  | intoCellRecord_undef_ptr {ρ : Env} {tag size align : Int} {e : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawIntoCellRecord tag size align e :: k) ρ σ μ) .undef
  | intoCellRecord_abort {ρ : Env} {tag size align : Int} {e : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort ab)) :
      Step P cap (.run (.rawIntoCellRecord tag size align e :: k) ρ σ μ) ab.toConfig
  | fromCellRecord_ok {ρ : Env} {tag : Int} {e : Expr} {a k' size : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k')))
      (hc : μ.emptyRecordSize a k' tag = some size) :
      Step P cap (.run (.rawFromCellRecord tag e :: k) ρ σ μ)
        (.run k ρ σ (μ.removeRecordCell a k' size))
  | fromCellRecord_bad {ρ : Env} {tag : Int} {e : Expr} {a k' : Int}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k')))
      (hc : μ.emptyRecordSize a k' tag = none) :
      Step P cap (.run (.rawFromCellRecord tag e :: k) ρ σ μ) .undef
  | fromCellRecord_undef_ptr {ρ : Env} {tag : Int} {e : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawFromCellRecord tag e :: k) ρ σ μ) .undef
  | fromCellRecord_abort {ρ : Env} {tag : Int} {e : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort ab)) :
      Step P cap (.run (.rawFromCellRecord tag e :: k) ρ σ μ) ab.toConfig
  | cellInitRecord_ok {ρ : Env} {tag : Int} {ep ev : Expr}
      {a k' size : Int} {value : Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.ok (.ptr a k'))) (hv : Eval cap ρ ev (.ok value))
      (ht : ∃ stored, value.recordForTag? tag = some stored)
      (hc : μ.emptyRecordSize a k' tag = some size) :
      Step P cap (.run (.rawCellInitRecord tag ep ev :: k) ρ σ μ)
        (.run k ρ σ (μ.setRecordValue a k' (some value)))
  | cellInitRecord_bad {ρ : Env} {tag : Int} {ep ev : Expr}
      {a k' : Int} {value : Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.ok (.ptr a k'))) (hv : Eval cap ρ ev (.ok value))
      (hbad : value.recordForTag? tag = none ∨ μ.emptyRecordSize a k' tag = none) :
      Step P cap (.run (.rawCellInitRecord tag ep ev :: k) ρ σ μ) .undef
  | cellInitRecord_abort_val {ρ : Env} {tag : Int} {ep ev : Expr}
      {a k' : Int} {ab : Abort} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.ok (.ptr a k'))) (hv : Eval cap ρ ev (.abort ab)) :
      Step P cap (.run (.rawCellInitRecord tag ep ev :: k) ρ σ μ) ab.toConfig
  | cellInitRecord_undef_ptr {ρ : Env} {tag : Int} {ep ev : Expr} {value : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.ok value)) (hv : ∀ a k', value ≠ .ptr a k') :
      Step P cap (.run (.rawCellInitRecord tag ep ev :: k) ρ σ μ) .undef
  | cellInitRecord_abort_ptr {ρ : Env} {tag : Int} {ep ev : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hp : Eval cap ρ ep (.abort ab)) :
      Step P cap (.run (.rawCellInitRecord tag ep ev :: k) ρ σ μ) ab.toConfig
  | cellReadRecord_ok {ρ : Env} {tag : Int} {dst : String} {e : Expr}
      {a k' : Int} {value : Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k')))
      (hc : μ.recordValueAt a k' tag = some value) :
      Step P cap (.run (.rawCellReadRecord tag dst e :: k) ρ σ μ)
        (.run k (ρ.update dst value) σ μ)
  | cellReadRecord_bad {ρ : Env} {tag : Int} {dst : String} {e : Expr}
      {a k' : Int} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k')))
      (hc : μ.recordValueAt a k' tag = none) :
      Step P cap (.run (.rawCellReadRecord tag dst e :: k) ρ σ μ) .undef
  | cellReadRecord_undef_ptr {ρ : Env} {tag : Int} {dst : String} {e : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawCellReadRecord tag dst e :: k) ρ σ μ) .undef
  | cellReadRecord_abort {ρ : Env} {tag : Int} {dst : String} {e : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort ab)) :
      Step P cap (.run (.rawCellReadRecord tag dst e :: k) ρ σ μ) ab.toConfig
  | cellTakeRecord_ok {ρ : Env} {tag : Int} {dst : String} {e : Expr}
      {a k' : Int} {value : Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k')))
      (hc : μ.recordValueAt a k' tag = some value) :
      Step P cap (.run (.rawCellTakeRecord tag dst e :: k) ρ σ μ)
        (.run k (ρ.update dst value) σ (μ.setRecordValue a k' none))
  | cellTakeRecord_bad {ρ : Env} {tag : Int} {dst : String} {e : Expr}
      {a k' : Int} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k')))
      (hc : μ.recordValueAt a k' tag = none) :
      Step P cap (.run (.rawCellTakeRecord tag dst e :: k) ρ σ μ) .undef
  | cellTakeRecord_undef_ptr {ρ : Env} {tag : Int} {dst : String} {e : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawCellTakeRecord tag dst e :: k) ρ σ μ) .undef
  | cellTakeRecord_abort {ρ : Env} {tag : Int} {dst : String} {e : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort ab)) :
      Step P cap (.run (.rawCellTakeRecord tag dst e :: k) ρ σ μ) ab.toConfig
  | cellDropRecord_ok {ρ : Env} {tag : Int} {e : Expr}
      {a k' : Int} {value : Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k')))
      (hc : μ.recordValueAt a k' tag = some value) :
      Step P cap (.run (.rawCellDropRecord tag e :: k) ρ σ μ)
        (.run k ρ σ (μ.setRecordValue a k' none))
  | cellDropRecord_bad {ρ : Env} {tag : Int} {e : Expr}
      {a k' : Int} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok (.ptr a k')))
      (hc : μ.recordValueAt a k' tag = none) :
      Step P cap (.run (.rawCellDropRecord tag e :: k) ρ σ μ) .undef
  | cellDropRecord_undef_ptr {ρ : Env} {tag : Int} {e : Expr} {v : Val}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ a k', v ≠ .ptr a k') :
      Step P cap (.run (.rawCellDropRecord tag e :: k) ρ σ μ) .undef
  | cellDropRecord_abort {ρ : Env} {tag : Int} {e : Expr} {ab : Abort}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort ab)) :
      Step P cap (.run (.rawCellDropRecord tag e :: k) ρ σ μ) ab.toConfig
  -- Machine-profile operations have no meaning in the unprofiled core.
  -- A selected profile must intercept them before delegating to `Step`.
  | testUartProfile_undef {ρ : Env} {script : Expr}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap} :
      Step P cap (.run (.testUartProfile script :: k) ρ σ μ) .undef
  | uartStatus_undef {ρ : Env} {dst : String}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap} :
      Step P cap (.run (.uartStatus dst :: k) ρ σ μ) .undef
  | uartWrite_undef {ρ : Env} {value : Expr}
      {k : List Stmt} {σ : List Frame} {μ : RawHeap} :
      Step P cap (.run (.uartWrite value :: k) ρ σ μ) .undef
  -- fall off the end of a body: return unit
  | nil_ret {ρ : Env} {μ : RawHeap} :
      Step P cap (.run [] ρ [] μ) (.done .unit)
  | nil_pop {ρ : Env} {fr : Frame} {σ : List Frame} {μ : RawHeap} :
      Step P cap (.run [] ρ (fr :: σ) μ)
        (.run fr.k ((fr.ρ.restore fr.loans ρ).bindDst fr.dst .unit) σ μ)

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps (P : Prog) (cap : Int) : Config → Config → Prop where
  | refl {c : Config} : Steps P cap c c
  | head {c₁ c₂ c₃ : Config} (h : Step P cap c₁ c₂) (hs : Steps P cap c₂ c₃) :
      Steps P cap c₁ c₃

/-- Terminal configurations: normal return, trap, or undef. `run`
configurations are never terminal — the machine is total (progress is a
theorem in `Sable/SVMEval.lean`). -/
def Config.Terminal : Config → Prop
  | .run .. => False
  | .done _ => True
  | .trapped _ => True
  | .undef => True

/-- Behavior of a function body `k` from locals `ρ`: normal return. -/
def Returns (P : Prog) (cap : Int) (k : List Stmt) (ρ : Env) (v : Val) : Prop :=
  Steps P cap (.run k ρ [] .empty) (.done v)

/-- Behavior: terminal trap. -/
def TrapsWith (P : Prog) (cap : Int) (k : List Stmt) (ρ : Env) (t : Trap) : Prop :=
  Steps P cap (.run k ρ [] .empty) (.trapped t)

/-- Behavior: the undef outcome — what the static semantics must prove
unreachable for checked programs. -/
def ReachesUndef (P : Prog) (cap : Int) (k : List Stmt) (ρ : Env) : Prop :=
  Steps P cap (.run k ρ [] .empty) .undef

/-- Divergence: every reachable configuration can still step. This is
what `partial fn` (§8) permits and totality forbids — and with frames,
what unbounded recursion exhibits. -/
def Diverges (P : Prog) (cap : Int) (c : Config) : Prop :=
  ∀ c', Steps P cap c c' → ∃ c'', Step P cap c' c''

/-! ## Sanity theorems -/

/-- Terminal outcomes really are terminal: `done` has no successor. -/
theorem done_no_step {P : Prog} {cap : Int} {v : Val} {c : Config} :
    ¬ Step P cap (.done v) c := nofun

/-- ... and neither does a trap: traps are not recoverable (§9: no
catching; a `defer` failure halts the machine). -/
theorem trapped_no_step {P : Prog} {cap : Int} {t : Trap} {c : Config} :
    ¬ Step P cap (.trapped t) c := nofun

/-- ... nor `undef`. -/
theorem undef_no_step {P : Prog} {cap : Int} {c : Config} :
    ¬ Step P cap .undef c := nofun

/-- The Euclidean remainder is representable whenever the divisor is —
even at signed extremes (e.g. `i8`: `|b| ≤ 128` gives `a emod b ≤ 127`).
This is why `mod` has no overflow rule while `div` needs one for MIN / -1:
it turns §2.2's shared obligation row for `/` and `%` (and ADR 0004's
remark that `T.min % -1 = 0` is fine) into a theorem. -/
theorem IntTy.emod_inRange (t : IntTy) {a b : Int}
    (hb : b ≠ 0) (hbr : t.inRange b) : t.inRange (a.emod b) := by
  have h0 : 0 ≤ a.emod b := Int.emod_nonneg a hb
  have hlt : a.emod b < b ∨ a.emod b < -b := by
    rcases (by omega : 0 < b ∨ b < 0) with hpos | hneg
    · exact Or.inl (Int.emod_lt_of_pos a hpos)
    · have h : a % (-b) < -b := Int.emod_lt_of_pos a (by omega)
      rw [Int.emod_neg] at h
      exact Or.inr h
  obtain ⟨hbl, hbu⟩ := hbr
  generalize a.emod b = r at h0 hlt
  cases t <;> simp only [IntTy.inRange, IntTy.min, IntTy.max] at hbl hbu ⊢ <;> omega

/-! ## Smoke tests: tiny derivations exercising the outcome kinds -/

private def ρ₀ : Env := Env.empty
private def P₀ : Prog := Prog.empty

/-- `x = 1; return x + 1` returns 2. -/
example :
    Returns P₀ 1000
      [.assign "x" (.intLit .i32 1),
       .ret (.arith .add .i32 (.var "x") (.intLit .i32 1))]
      ρ₀ (.int 2) := by
  have hx : (ρ₀.update "x" (.int 1)) "x" = some (.int 1) := by
    simp [Env.update]
  have h1 : Eval 1000 ρ₀ (.intLit .i32 1) (.ok (.int 1)) :=
    .intLit (by decide)
  have h2 : Eval 1000 (ρ₀.update "x" (.int 1))
      (.arith .add .i32 (.var "x") (.intLit .i32 1)) (.ok (.int 2)) :=
    .arith_ok (.var hx) (.intLit (by decide)) (by decide)
  exact .head (.assign_ok h1) (.head (.ret_ok h2) .refl)

/-- `return 7 / 0` ends in the div-by-zero trap, not a return. -/
example :
    TrapsWith P₀ 1000 [.ret (.div .i32 (.intLit .i32 7) (.intLit .i32 0))]
      ρ₀ .divByZero :=
  .head (.ret_abort (.div_zero (.intLit (by decide)) (.intLit (by decide)))) .refl

/-- `return (255 + 1 : u8)` ends in the overflow trap. -/
example :
    TrapsWith P₀ 1000 [.ret (.arith .add .u8 (.intLit .u8 255) (.intLit .u8 1))]
      ρ₀ (.overflow .u8) :=
  .head (.ret_abort (.arith_overflow (.intLit (by decide)) (.intLit (by decide))
    (by decide))) .refl

/-- `return x` with `x` uninitialized ends in `undef`: the ⊥-read has a
defined outcome (ADR 0005), which checked programs never reach. -/
example : ReachesUndef P₀ 1000 [.ret (.var "x")] ρ₀ :=
  .head (.ret_abort (.var_undef rfl)) .refl

/-- `x = id(41); return x + 1` through a one-function program: enter,
return through the frame, resume the caller. -/
example :
    Returns (Prog.ofList [("id", ⟨["a"], [.ret (.var "a")]⟩)]) 1000
      [.call (some "x") "id" [.byValue (.intLit .i32 41)],
       .ret (.arith .add .i32 (.var "x") (.intLit .i32 1))]
      ρ₀ (.int 42) := by
  have hf : Prog.ofList [("id", ⟨["a"], [.ret (.var "a")]⟩)] "id"
      = some ⟨["a"], [.ret (.var "a")]⟩ := rfl
  have hargs : EvalArgs 1000 ρ₀ [.intLit .i32 41] (.ok [.int 41]) :=
    .cons_ok (.intLit (by decide)) .nil
  have ha : (Env.empty.bind ["a"] [.int 41]) "a" = some (.int 41) := by
    simp [Env.bind, Env.update]
  have hx : ((ρ₀.restore [] (Env.empty.bind ["a"] [.int 41])).bindDst (some "x")
      (.int 41)) "x" = some (.int 41) := by
    simp [Env.bindDst, Env.update]
  refine .head (.call_enter hf hargs rfl) (.head (.ret_pop (.var ha)) (.head (.ret_ok ?_) .refl))
  exact .arith_ok (.var hx) (.intLit (by decide)) (by decide)

end SVM
end Sable
