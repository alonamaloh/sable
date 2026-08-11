/-
SVM: operational semantics for a core Sable subset (design §10, ADR 0005).

The scope is deliberately partial — classes, borrows as distinct values,
function calls, ghost state, and the heap are scoped out with notes; the
findings the first draft forced are resolved in ADR 0005 and design §10.

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

/-- Machine values. Integers are exact (`Int`); their widths live in the
typed syntax, and per-operation rules enforce representability — the
value plane never wraps. Arrays are `Sable.Seq Int` (owned `[T]` of a
scalar element type; the ghost lift is then the identity). Options are
scoped to integer payloads. -/
inductive Val where
  | unit
  | int  (n : Int)
  | bool (b : Bool)
  | arr  (a : Seq Int)
  | opt  (o : Option Int)
  /-- A raw pointer: provenance plus a byte offset, never a machine
  address. Two live pointers may name the same address only if they name
  the same allocation, which is what makes `free` able to invalidate
  exactly the pointers derived from what it released. -/
  | ptr  (alloc off : Int)

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

/-- One allocation. `live` is kept rather than removed on free, so stale
provenance stays distinguishable from fresh provenance: a released id is
never handed out again. -/
structure Allocation where
  size : Int
  live : Bool
  bytes : Seq RawByte

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
  | some al => al.live && decide (0 ≤ k) && decide (k < al.size)
  | none => false

/-- The byte at `(a, k)`, if that address is in a live allocation. -/
def RawHeap.byteAt (μ : RawHeap) (a k : Int) : Option RawByte :=
  match μ.allocs a with
  | some al => if al.live ∧ 0 ≤ k ∧ k < al.size then some (al.bytes.get k) else none
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
      if i = μ.next then some ⟨size, true, ⟨size, fun _ => .uninit⟩⟩ else μ.allocs i }

/-- Terminal trap outcomes, distinct from normal termination. These are
*structural* (they carry the operation and the offending data); the
obligation *names* of §6/§9 are compiler artifacts layered on top —
except for `deferViolation`, where the compiled `defer` check carries its
obligation name into machine syntax (ADR 0005). -/
inductive Trap where
  | overflow  (t : IntTy)
  | divByZero
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
method calls, class constructors, borrows as distinct values, `sat(·)`,
option accessors. -/
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
  | someE   (e : Expr)
  | noneE

/-- Statements. `while` carries no invariant/variant: loop annotations
are ghost and erased (§4); the machine runs the loop, the verifier proves
it. `check` is the compiled form of `defer P` (§9): evaluate the
monitorable predicate, trap with the obligation's name if false. `call`
is the A-normal form calls take in the machine (ADR 0005): they exist
only at statement level — `x = f(args)`, or `f(args)` for a discarded
result — so expressions stay pure and big-step. -/
inductive Stmt where
  | assign (x : String) (e : Expr)
  | store  (x : String) (idx : Expr) (val : Expr)
  | ite    (c : Expr) (thn els : List Stmt)
  | while  (c : Expr) (body : List Stmt)
  | ret    (e : Expr)
  | check  (name : String) (c : Expr)
  | call   (dst : Option String) (f : String) (args : List Expr)
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
      Eval cap ρ (.checkedArith op t e₁ e₂) (.ok (.opt (some (op.denote a b))))
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
  | len {ρ : Env} {x : String} {a : Seq Int}
      (h : ρ x = some (.arr a)) :
      Eval cap ρ (.len x) (.ok (.int a.len))
  | len_undef {ρ : Env} {x : String}
      (h : ∀ a : Seq Int, ρ x ≠ some (.arr a)) :
      Eval cap ρ (.len x) (.abort .undef)
  | index_ok {ρ : Env} {x : String} {e : Expr} {a : Seq Int} {n : Int}
      (hi : Eval cap ρ e (.ok (.int n))) (ha : ρ x = some (.arr a))
      (h₀ : 0 ≤ n) (h₁ : n < a.len) :
      Eval cap ρ (.index x e) (.ok (.int (a.get n)))
  | index_oob {ρ : Env} {x : String} {e : Expr} {a : Seq Int} {n : Int}
      (hi : Eval cap ρ e (.ok (.int n))) (ha : ρ x = some (.arr a))
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
      (ha : ∀ a : Seq Int, ρ x ≠ some (.arr a)) :
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
  | alloc_ok {ρ : Env} {e₁ e₂ : Expr} {n v : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok (.int v)))
      (h₀ : 0 ≤ n) (hc : n ≤ cap) :
      Eval cap ρ (.allocArray e₁ e₂) (.ok (.arr ⟨n, fun _ => v⟩))
  | alloc_oom {ρ : Env} {e₁ e₂ : Expr} {n v : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok (.int v)))
      (h₀ : 0 ≤ n) (hc : cap < n) :
      Eval cap ρ (.allocArray e₁ e₂) (.abort (.trap (.oom n)))
  | alloc_neg {ρ : Env} {e₁ e₂ : Expr} {n v : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok (.int v)))
      (h₀ : n < 0) :
      Eval cap ρ (.allocArray e₁ e₂) (.abort .undef)
  | alloc_undef₁ {ρ : Env} {e₁ e₂ : Expr} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Eval cap ρ (.allocArray e₁ e₂) (.abort .undef)
  | alloc_abort₁ {ρ : Env} {e₁ e₂ : Expr} {a : Abort}
      (h : Eval cap ρ e₁ (.abort a)) :
      Eval cap ρ (.allocArray e₁ e₂) (.abort a)
  | alloc_undef₂ {ρ : Env} {e₁ e₂ : Expr} {n : Int} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok v))
      (hv : ∀ m, v ≠ .int m) :
      Eval cap ρ (.allocArray e₁ e₂) (.abort .undef)
  | alloc_abort₂ {ρ : Env} {e₁ e₂ : Expr} {n : Int} {a : Abort}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.abort a)) :
      Eval cap ρ (.allocArray e₁ e₂) (.abort a)
  -- options (integer payload)
  | someE_ok {ρ : Env} {e : Expr} {n : Int}
      (h : Eval cap ρ e (.ok (.int n))) :
      Eval cap ρ (.someE e) (.ok (.opt (some n)))
  | someE_undef {ρ : Env} {e : Expr} {v : Val}
      (h : Eval cap ρ e (.ok v)) (hv : ∀ n, v ≠ .int n) :
      Eval cap ρ (.someE e) (.abort .undef)
  | someE_abort {ρ : Env} {e : Expr} {a : Abort}
      (h : Eval cap ρ e (.abort a)) :
      Eval cap ρ (.someE e) (.abort a)
  | noneE {ρ : Env} :
      Eval cap ρ .noneE (.ok (.opt none))

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

/-- A suspended caller: where the result goes, what runs next, and the
caller's locals. -/
structure Frame where
  dst : Option String
  k   : List Stmt
  ρ   : Env

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
  from an empty frame with only its parameters bound.
- `ret` in a callee pops the caller's frame and binds the destination;
  at the bottom of the stack it is the program's answer. Falling off
  the end of a body returns `unit` the same two ways (procedures are
  blessed, cf. `swap` §5).
-/
inductive Step (P : Prog) (cap : Int) : Config → Config → Prop where
  | assign_ok {ρ : Env} {x : String} {e : Expr} {v : Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) :
      Step P cap (.run (.assign x e :: k) ρ σ μ) (.run k (ρ.update x v) σ μ)
  | assign_abort {ρ : Env} {x : String} {e : Expr} {a : Abort} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.abort a)) :
      Step P cap (.run (.assign x e :: k) ρ σ μ) a.toConfig
  | store_ok {ρ : Env} {x : String} {ei ev : Expr} {n w : Int} {a : Seq Int} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hi : Eval cap ρ ei (.ok (.int n))) (hv : Eval cap ρ ev (.ok (.int w)))
      (ha : ρ x = some (.arr a)) (h₀ : 0 ≤ n) (h₁ : n < a.len) :
      Step P cap (.run (.store x ei ev :: k) ρ σ μ) (.run k (ρ.update x (.arr (a.set n w))) σ μ)
  | store_oob {ρ : Env} {x : String} {ei ev : Expr} {n w : Int} {a : Seq Int} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hi : Eval cap ρ ei (.ok (.int n))) (hv : Eval cap ρ ev (.ok (.int w)))
      (ha : ρ x = some (.arr a)) (h : n < 0 ∨ a.len ≤ n) :
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
      (hw : ∀ m, v ≠ .int m) :
      Step P cap (.run (.store x ei ev :: k) ρ σ μ) .undef
  | store_undef_arr {ρ : Env} {x : String} {ei ev : Expr} {n w : Int} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hi : Eval cap ρ ei (.ok (.int n))) (hv : Eval cap ρ ev (.ok (.int w)))
      (ha : ∀ a : Seq Int, ρ x ≠ some (.arr a)) :
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
  | call_undef_fn {ρ : Env} {dst : Option String} {f : String} {args : List Expr} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hf : P f = none) :
      Step P cap (.run (.call dst f args :: k) ρ σ μ) .undef
  | call_abort {ρ : Env} {dst : Option String} {f : String} {args : List Expr} {fd : FnDef} {a : Abort} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hf : P f = some fd) (ha : EvalArgs cap ρ args (.abort a)) :
      Step P cap (.run (.call dst f args :: k) ρ σ μ) a.toConfig
  | call_undef_arity {ρ : Env} {dst : Option String} {f : String} {args : List Expr} {fd : FnDef} {vs : List Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hf : P f = some fd) (ha : EvalArgs cap ρ args (.ok vs))
      (hn : fd.params.length ≠ vs.length) :
      Step P cap (.run (.call dst f args :: k) ρ σ μ) .undef
  | call_enter {ρ : Env} {dst : Option String} {f : String} {args : List Expr} {fd : FnDef} {vs : List Val} {k : List Stmt} {σ : List Frame} {μ : RawHeap}
      (hf : P f = some fd) (ha : EvalArgs cap ρ args (.ok vs))
      (hn : fd.params.length = vs.length) :
      Step P cap (.run (.call dst f args :: k) ρ σ μ)
        (.run fd.body (Env.empty.bind fd.params vs) (⟨dst, k, ρ⟩ :: σ) μ)
  -- returns: pop a caller, or answer the program
  | ret_ok {ρ : Env} {e : Expr} {v : Val} {k : List Stmt} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) :
      Step P cap (.run (.ret e :: k) ρ [] μ) (.done v)
  | ret_pop {ρ : Env} {e : Expr} {v : Val} {k : List Stmt} {fr : Frame} {σ : List Frame} {μ : RawHeap}
      (h : Eval cap ρ e (.ok v)) :
      Step P cap (.run (.ret e :: k) ρ (fr :: σ) μ) (.run fr.k (fr.ρ.bindDst fr.dst v) σ μ)
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
  -- fall off the end of a body: return unit
  | nil_ret {ρ : Env} {μ : RawHeap} :
      Step P cap (.run [] ρ [] μ) (.done .unit)
  | nil_pop {ρ : Env} {fr : Frame} {σ : List Frame} {μ : RawHeap} :
      Step P cap (.run [] ρ (fr :: σ) μ) (.run fr.k (fr.ρ.bindDst fr.dst .unit) σ μ)

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
      [.call (some "x") "id" [.intLit .i32 41],
       .ret (.arith .add .i32 (.var "x") (.intLit .i32 1))]
      ρ₀ (.int 42) := by
  have hf : Prog.ofList [("id", ⟨["a"], [.ret (.var "a")]⟩)] "id"
      = some ⟨["a"], [.ret (.var "a")]⟩ := rfl
  have hargs : EvalArgs 1000 ρ₀ [.intLit .i32 41] (.ok [.int 41]) :=
    .cons_ok (.intLit (by decide)) .nil
  have ha : (Env.empty.bind ["a"] [.int 41]) "a" = some (.int 41) := by
    simp [Env.bind, Env.update]
  have hx : (ρ₀.bindDst (some "x") (.int 41)) "x" = some (.int 41) := by
    simp [Env.bindDst, Env.update]
  refine .head (.call_enter hf hargs rfl) (.head (.ret_pop (.var ha)) (.head (.ret_ok ?_) .refl))
  exact .arith_ok (.var hx) (.intLit (by decide)) (by decide)

end SVM
end Sable
