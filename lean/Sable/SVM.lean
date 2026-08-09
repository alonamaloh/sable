/-
SVM: operational semantics for a core Sable subset (design §10).

DESIGN-AUDIT ARTIFACT (parallel track, docs/PLAN.md). The point of this
file is to force the prose design into rules and surface the places where
the prose is ambiguous or inconsistent; the findings live in
`docs/notes/svm-draft.md`. It is deliberately incomplete — classes,
borrows as distinct values, function calls, ghost state, and the heap are
scoped out with notes.

Shape (justified in the notes file):

- **Statements: small-step**, an inductive relation `Step` over
  configurations, as design §10 mandates ("small-step, deterministic").
  Divergence (`while`), normal termination, and traps must be
  distinguishable, and small-step is what makes divergence a real
  behavior rather than a missing derivation.
- **Expressions: big-step**, an inductive relation `Eval`. In this
  fragment expressions are pure and call-free, so evaluation cannot
  diverge and big-step loses no distinctions — but every trap and every
  trap-*propagation* rule is still an explicit constructor, because
  evaluation order (hence which trap fires) is exactly the kind of
  decision the prose never made.
- **Traps are terminal outcomes** (`Config.trapped`), distinct from
  normal termination (`Config.done`). Reading uninitialized memory (⊥)
  has deliberately *no* rule: such configurations are stuck, which is the
  §2.3/§10 tension discussed in the notes.
- The machine is parameterized by an allocation capacity `cap`; without
  it, "deterministic" (§10) and "alloc failure is a defined OOM trap"
  (§10) contradict each other. See the notes.

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
total operator `wrap(·)` (§2.2). For unsigned `t` this is `n mod 2^bits`.
NOTE (audit): the design only shows `wrap` on unsigned; two's-complement
behavior on signed types is this file's choice, not the prose's. -/
def IntTy.wrap (t : IntTy) (n : Int) : Int :=
  (n - t.min).emod ((2 : Int) ^ t.bits) + t.min

/-! ## Values and traps -/

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

/-- Terminal trap outcomes, distinct from normal termination. These are
*structural* (they carry the operation and the offending data); the
obligation *names* of §6/§9 are compiler artifacts layered on top —
except for `deferViolation`, where the compiled `defer` check carries its
obligation name into machine syntax. See notes. -/
inductive Trap where
  | overflow  (t : IntTy)
  | divByZero
  | indexOOB  (i len : Int)
  | narrowOOB (t : IntTy) (n : Int)
  | oom       (len : Int)
  | deferViolation (name : String)
  deriving Repr

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
Arrays are referred to by variable, matching the compiler's AST — array
*expressions* as index/store bases are an unforced surface question.
Scoped out: function calls, method calls, class constructors, borrows as
distinct values, `sat(·)`, `match`. -/
inductive Expr where
  | intLit  (t : IntTy) (n : Int)
  | boolLit (b : Bool)
  | var     (x : String)
  | neg     (t : IntTy) (e : Expr)
  | not     (e : Expr)
  | arith   (op : ArithOp) (t : IntTy) (e₁ e₂ : Expr)
  /-- `wrap(a ⊕ b)` — total modular arithmetic, §2.2. Necessarily a
  *variant of the operator*, not a function on a computed value: an
  ordinary operand would already have trapped on overflow. See notes. -/
  | wrapArith (op : ArithOp) (t : IntTy) (e₁ e₂ : Expr)
  /-- `checked(a ⊕ b)` — `none` on overflow, §2.2. Same caveat. -/
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
  | someE   (e : Expr)
  | noneE

/-- Statements. `while` carries no invariant/variant: loop annotations
are ghost and erased (§4); the machine runs the loop, the verifier proves
it. `check` is the compiled form of `defer P` (§9): evaluate the
monitorable predicate, trap with the obligation's name if false. -/
inductive Stmt where
  | assign (x : String) (e : Expr)
  | store  (x : String) (idx : Expr) (val : Expr)
  | ite    (c : Expr) (thn els : List Stmt)
  | while  (c : Expr) (body : List Stmt)
  | ret    (e : Expr)
  | check  (name : String) (c : Expr)

/-! ## Environments

One frame of locals. `none` is ⊥ (design §2.3: uninitialized, no default
zero). Note the model conflates "undeclared" with "declared but ⊥" —
frames in §10 hold `Val ∪ ⊥` per local, which suggests declarations
allocate ⊥ slots; declaration statements are scoped out here. -/

def Env := String → Option Val

def Env.empty : Env := fun _ => none

def Env.update (ρ : Env) (x : String) (v : Val) : Env :=
  fun y => if y = x then some v else ρ y

/-! ## Expression evaluation (big-step) -/

/-- Outcome of evaluating an expression: a value, or a trap. -/
inductive EOut where
  | ok   (v : Val)
  | trap (t : Trap)

/--
`Eval cap ρ e out`: under locals `ρ`, expression `e` evaluates to `out`.

Decisions the prose forced but never made (see notes for the full list):
- **Left-to-right operand order**, so the *left* operand's trap wins.
- **Short-circuit `&&`/`||`**: the right operand (and its traps) is
  unreachable when the left operand decides.
- Reading ⊥ (`ρ x = none`), non-bool `if` conditions, out-of-range
  literals, negative `alloc_array` lengths: **no rule — stuck**. These
  are the states the static semantics must exclude; pillar 1's "every
  syntactically valid program has a meaning" is not honored by this
  relation and must be restated against *checked* programs.
-/
inductive Eval (cap : Int) : Env → Expr → EOut → Prop where
  -- literals; an out-of-range literal has no meaning (typechecker duty)
  | intLit {ρ : Env} {t : IntTy} {n : Int} (h : t.inRange n) :
      Eval cap ρ (.intLit t n) (.ok (.int n))
  | boolLit {ρ : Env} {b : Bool} :
      Eval cap ρ (.boolLit b) (.ok (.bool b))
  -- variables; `ρ x = none` (⊥) has no rule: stuck, per §2.3
  | var {ρ : Env} {x : String} {v : Val} (h : ρ x = some v) :
      Eval cap ρ (.var x) (.ok v)
  -- unary minus (audit: on unsigned this traps unless the operand is 0;
  -- whether unary minus is even legal on unsigned is unstated)
  | neg_ok {ρ : Env} {t : IntTy} {e : Expr} {n : Int}
      (h : Eval cap ρ e (.ok (.int n))) (hr : t.inRange (-n)) :
      Eval cap ρ (.neg t e) (.ok (.int (-n)))
  | neg_overflow {ρ : Env} {t : IntTy} {e : Expr} {n : Int}
      (h : Eval cap ρ e (.ok (.int n))) (hr : ¬ t.inRange (-n)) :
      Eval cap ρ (.neg t e) (.trap (.overflow t))
  | neg_trap {ρ : Env} {t : IntTy} {e : Expr} {tr : Trap}
      (h : Eval cap ρ e (.trap tr)) :
      Eval cap ρ (.neg t e) (.trap tr)
  | not_ok {ρ : Env} {e : Expr} {b : Bool}
      (h : Eval cap ρ e (.ok (.bool b))) :
      Eval cap ρ (.not e) (.ok (.bool (!b)))
  | not_trap {ρ : Env} {e : Expr} {tr : Trap}
      (h : Eval cap ρ e (.trap tr)) :
      Eval cap ρ (.not e) (.trap tr)
  -- checked arithmetic: + - * with the §2.2 representability obligation
  | arith_ok {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b)))
      (hr : t.inRange (op.denote a b)) :
      Eval cap ρ (.arith op t e₁ e₂) (.ok (.int (op.denote a b)))
  | arith_overflow {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b)))
      (hr : ¬ t.inRange (op.denote a b)) :
      Eval cap ρ (.arith op t e₁ e₂) (.trap (.overflow t))
  | arith_trap₁ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {tr : Trap}
      (h : Eval cap ρ e₁ (.trap tr)) :
      Eval cap ρ (.arith op t e₁ e₂) (.trap tr)
  | arith_trap₂ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {v : Val} {tr : Trap}
      (h₁ : Eval cap ρ e₁ (.ok v)) (h₂ : Eval cap ρ e₂ (.trap tr)) :
      Eval cap ρ (.arith op t e₁ e₂) (.trap tr)
  -- wrap(·): total, no overflow rule — but operand traps still propagate
  | wrap_ok {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b))) :
      Eval cap ρ (.wrapArith op t e₁ e₂) (.ok (.int (t.wrap (op.denote a b))))
  | wrap_trap₁ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {tr : Trap}
      (h : Eval cap ρ e₁ (.trap tr)) :
      Eval cap ρ (.wrapArith op t e₁ e₂) (.trap tr)
  | wrap_trap₂ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {v : Val} {tr : Trap}
      (h₁ : Eval cap ρ e₁ (.ok v)) (h₂ : Eval cap ρ e₂ (.trap tr)) :
      Eval cap ρ (.wrapArith op t e₁ e₂) (.trap tr)
  -- checked(·): none on overflow
  | checked_some {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b)))
      (hr : t.inRange (op.denote a b)) :
      Eval cap ρ (.checkedArith op t e₁ e₂) (.ok (.opt (some (op.denote a b))))
  | checked_none {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b)))
      (hr : ¬ t.inRange (op.denote a b)) :
      Eval cap ρ (.checkedArith op t e₁ e₂) (.ok (.opt none))
  | checked_trap₁ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {tr : Trap}
      (h : Eval cap ρ e₁ (.trap tr)) :
      Eval cap ρ (.checkedArith op t e₁ e₂) (.trap tr)
  | checked_trap₂ {ρ : Env} {op : ArithOp} {t : IntTy} {e₁ e₂ : Expr} {v : Val} {tr : Trap}
      (h₁ : Eval cap ρ e₁ (.ok v)) (h₂ : Eval cap ρ e₂ (.trap tr)) :
      Eval cap ρ (.checkedArith op t e₁ e₂) (.trap tr)
  -- Euclidean division (ADR 0004). The signed MIN / -1 case is the unique
  -- unrepresentable quotient, stated here uniformly as representability.
  | div_ok {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b)))
      (hz : b ≠ 0) (hr : t.inRange (a.ediv b)) :
      Eval cap ρ (.div t e₁ e₂) (.ok (.int (a.ediv b)))
  | div_zero {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok v)) (h₂ : Eval cap ρ e₂ (.ok (.int 0))) :
      Eval cap ρ (.div t e₁ e₂) (.trap .divByZero)
  | div_overflow {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b)))
      (hz : b ≠ 0) (hr : ¬ t.inRange (a.ediv b)) :
      Eval cap ρ (.div t e₁ e₂) (.trap (.overflow t))
  | div_trap₁ {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {tr : Trap}
      (h : Eval cap ρ e₁ (.trap tr)) :
      Eval cap ρ (.div t e₁ e₂) (.trap tr)
  | div_trap₂ {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {v : Val} {tr : Trap}
      (h₁ : Eval cap ρ e₁ (.ok v)) (h₂ : Eval cap ρ e₂ (.trap tr)) :
      Eval cap ρ (.div t e₁ e₂) (.trap tr)
  -- Euclidean remainder: no overflow rule — `emod_inRange` below proves
  -- the result always representable, even at signed extremes.
  | mod_ok {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b)))
      (hz : b ≠ 0) :
      Eval cap ρ (.mod t e₁ e₂) (.ok (.int (a.emod b)))
  | mod_zero {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {v : Val}
      (h₁ : Eval cap ρ e₁ (.ok v)) (h₂ : Eval cap ρ e₂ (.ok (.int 0))) :
      Eval cap ρ (.mod t e₁ e₂) (.trap .divByZero)
  | mod_trap₁ {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {tr : Trap}
      (h : Eval cap ρ e₁ (.trap tr)) :
      Eval cap ρ (.mod t e₁ e₂) (.trap tr)
  | mod_trap₂ {ρ : Env} {t : IntTy} {e₁ e₂ : Expr} {v : Val} {tr : Trap}
      (h₁ : Eval cap ρ e₁ (.ok v)) (h₂ : Eval cap ρ e₂ (.trap tr)) :
      Eval cap ρ (.mod t e₁ e₂) (.trap tr)
  -- comparisons (integer operands only; bool == bool is scoped out)
  | cmp_ok {ρ : Env} {op : CmpOp} {e₁ e₂ : Expr} {a b : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int a))) (h₂ : Eval cap ρ e₂ (.ok (.int b))) :
      Eval cap ρ (.cmp op e₁ e₂) (.ok (.bool (op.denote a b)))
  | cmp_trap₁ {ρ : Env} {op : CmpOp} {e₁ e₂ : Expr} {tr : Trap}
      (h : Eval cap ρ e₁ (.trap tr)) :
      Eval cap ρ (.cmp op e₁ e₂) (.trap tr)
  | cmp_trap₂ {ρ : Env} {op : CmpOp} {e₁ e₂ : Expr} {v : Val} {tr : Trap}
      (h₁ : Eval cap ρ e₁ (.ok v)) (h₂ : Eval cap ρ e₂ (.trap tr)) :
      Eval cap ρ (.cmp op e₁ e₂) (.trap tr)
  -- short-circuit && and || (the prose never states short-circuiting;
  -- the guarded-RHS VC idiom `i < a.len && a[i] > 0` requires it)
  | and_false {ρ : Env} {e₁ e₂ : Expr}
      (h : Eval cap ρ e₁ (.ok (.bool false))) :
      Eval cap ρ (.and e₁ e₂) (.ok (.bool false))
  | and_true {ρ : Env} {e₁ e₂ : Expr} {b : Bool}
      (h₁ : Eval cap ρ e₁ (.ok (.bool true))) (h₂ : Eval cap ρ e₂ (.ok (.bool b))) :
      Eval cap ρ (.and e₁ e₂) (.ok (.bool b))
  | and_trap₁ {ρ : Env} {e₁ e₂ : Expr} {tr : Trap}
      (h : Eval cap ρ e₁ (.trap tr)) :
      Eval cap ρ (.and e₁ e₂) (.trap tr)
  | and_trap₂ {ρ : Env} {e₁ e₂ : Expr} {tr : Trap}
      (h₁ : Eval cap ρ e₁ (.ok (.bool true))) (h₂ : Eval cap ρ e₂ (.trap tr)) :
      Eval cap ρ (.and e₁ e₂) (.trap tr)
  | or_true {ρ : Env} {e₁ e₂ : Expr}
      (h : Eval cap ρ e₁ (.ok (.bool true))) :
      Eval cap ρ (.or e₁ e₂) (.ok (.bool true))
  | or_false {ρ : Env} {e₁ e₂ : Expr} {b : Bool}
      (h₁ : Eval cap ρ e₁ (.ok (.bool false))) (h₂ : Eval cap ρ e₂ (.ok (.bool b))) :
      Eval cap ρ (.or e₁ e₂) (.ok (.bool b))
  | or_trap₁ {ρ : Env} {e₁ e₂ : Expr} {tr : Trap}
      (h : Eval cap ρ e₁ (.trap tr)) :
      Eval cap ρ (.or e₁ e₂) (.trap tr)
  | or_trap₂ {ρ : Env} {e₁ e₂ : Expr} {tr : Trap}
      (h₁ : Eval cap ρ e₁ (.ok (.bool false))) (h₂ : Eval cap ρ e₂ (.trap tr)) :
      Eval cap ρ (.or e₁ e₂) (.trap tr)
  -- arrays: length and load; `a.get` is total-with-junk (Sable.Seq) but
  -- the machine only reads it under the bounds check
  | len {ρ : Env} {x : String} {a : Seq Int}
      (h : ρ x = some (.arr a)) :
      Eval cap ρ (.len x) (.ok (.int a.len))
  | index_ok {ρ : Env} {x : String} {e : Expr} {a : Seq Int} {n : Int}
      (ha : ρ x = some (.arr a)) (hi : Eval cap ρ e (.ok (.int n)))
      (h₀ : 0 ≤ n) (h₁ : n < a.len) :
      Eval cap ρ (.index x e) (.ok (.int (a.get n)))
  | index_oob {ρ : Env} {x : String} {e : Expr} {a : Seq Int} {n : Int}
      (ha : ρ x = some (.arr a)) (hi : Eval cap ρ e (.ok (.int n)))
      (h : n < 0 ∨ a.len ≤ n) :
      Eval cap ρ (.index x e) (.trap (.indexOOB n a.len))
  | index_trap {ρ : Env} {x : String} {e : Expr} {tr : Trap}
      (h : Eval cap ρ e (.trap tr)) :
      Eval cap ρ (.index x e) (.trap tr)
  -- widen: total and, on the exact-Int value plane, the identity
  | widen_ok {ρ : Env} {dst : IntTy} {e : Expr} {n : Int}
      (h : Eval cap ρ e (.ok (.int n))) :
      Eval cap ρ (.widen dst e) (.ok (.int n))
  | widen_trap {ρ : Env} {dst : IntTy} {e : Expr} {tr : Trap}
      (h : Eval cap ρ e (.trap tr)) :
      Eval cap ρ (.widen dst e) (.trap tr)
  -- narrow<T>: the §2.2 fits-obligation; trap when deferred
  | narrow_ok {ρ : Env} {dst : IntTy} {e : Expr} {n : Int}
      (h : Eval cap ρ e (.ok (.int n))) (hr : dst.inRange n) :
      Eval cap ρ (.narrow dst e) (.ok (.int n))
  | narrow_oob {ρ : Env} {dst : IntTy} {e : Expr} {n : Int}
      (h : Eval cap ρ e (.ok (.int n))) (hr : ¬ dst.inRange n) :
      Eval cap ρ (.narrow dst e) (.trap (.narrowOOB dst n))
  | narrow_trap {ρ : Env} {dst : IntTy} {e : Expr} {tr : Trap}
      (h : Eval cap ρ e (.trap tr)) :
      Eval cap ρ (.narrow dst e) (.trap tr)
  -- alloc_array(n, v): OOM is a defined trap (§10), decided against the
  -- machine's capacity parameter. Negative length: no rule (typing).
  | alloc_ok {ρ : Env} {e₁ e₂ : Expr} {n v : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok (.int v)))
      (h₀ : 0 ≤ n) (hc : n ≤ cap) :
      Eval cap ρ (.allocArray e₁ e₂) (.ok (.arr ⟨n, fun _ => v⟩))
  | alloc_oom {ρ : Env} {e₁ e₂ : Expr} {n v : Int}
      (h₁ : Eval cap ρ e₁ (.ok (.int n))) (h₂ : Eval cap ρ e₂ (.ok (.int v)))
      (h₀ : 0 ≤ n) (hc : cap < n) :
      Eval cap ρ (.allocArray e₁ e₂) (.trap (.oom n))
  | alloc_trap₁ {ρ : Env} {e₁ e₂ : Expr} {tr : Trap}
      (h : Eval cap ρ e₁ (.trap tr)) :
      Eval cap ρ (.allocArray e₁ e₂) (.trap tr)
  | alloc_trap₂ {ρ : Env} {e₁ e₂ : Expr} {v : Val} {tr : Trap}
      (h₁ : Eval cap ρ e₁ (.ok v)) (h₂ : Eval cap ρ e₂ (.trap tr)) :
      Eval cap ρ (.allocArray e₁ e₂) (.trap tr)
  -- options (integer payload)
  | someE_ok {ρ : Env} {e : Expr} {n : Int}
      (h : Eval cap ρ e (.ok (.int n))) :
      Eval cap ρ (.someE e) (.ok (.opt (some n)))
  | someE_trap {ρ : Env} {e : Expr} {tr : Trap}
      (h : Eval cap ρ e (.trap tr)) :
      Eval cap ρ (.someE e) (.trap tr)
  | noneE {ρ : Env} :
      Eval cap ρ .noneE (.ok (.opt none))

/-! ## Configurations and the small-step relation -/

/-- A configuration: either running (a continuation of statements plus
one frame of locals — design §10's ⟨code, frames, heap, ghost⟩ with the
frame stack collapsed to one frame, the heap absorbed into owned array
values, and the ghost component scoped out), or one of the two terminal
outcomes. Traps are terminal and distinct from normal termination. -/
inductive Config where
  | run     (k : List Stmt) (ρ : Env)
  | done    (v : Val)
  | trapped (t : Trap)

/--
`Step cap c c'`: one machine step. Small-step, deterministic (§10) —
determinism is by construction of the rule side conditions (each pair of
rules for the same head statement is separated by mutually exclusive
conditions on the same left-to-right evaluation); proving it is the first
follow-up theorem, deliberately not attempted in this draft.

Decisions the prose forced (see notes):
- `store`: index evaluated, then value, then the bounds check — the
  value's trap beats the OOB trap, matching `interp.rs` (itself
  undocumented in the design).
- `while` unfolds to its body plus itself: loops run by unfolding, the
  invariant/variant having been erased.
- an empty continuation returns `unit` (fall-off-the-end, cf. `swap` §5
  which has no `return`; the prose never mentions unit-valued functions).
-/
inductive Step (cap : Int) : Config → Config → Prop where
  | assign_ok {ρ : Env} {x : String} {e : Expr} {v : Val} {k : List Stmt}
      (h : Eval cap ρ e (.ok v)) :
      Step cap (.run (.assign x e :: k) ρ) (.run k (ρ.update x v))
  | assign_trap {ρ : Env} {x : String} {e : Expr} {tr : Trap} {k : List Stmt}
      (h : Eval cap ρ e (.trap tr)) :
      Step cap (.run (.assign x e :: k) ρ) (.trapped tr)
  | store_ok {ρ : Env} {x : String} {ei ev : Expr} {n w : Int} {a : Seq Int} {k : List Stmt}
      (hi : Eval cap ρ ei (.ok (.int n))) (hv : Eval cap ρ ev (.ok (.int w)))
      (ha : ρ x = some (.arr a)) (h₀ : 0 ≤ n) (h₁ : n < a.len) :
      Step cap (.run (.store x ei ev :: k) ρ) (.run k (ρ.update x (.arr (a.set n w))))
  | store_oob {ρ : Env} {x : String} {ei ev : Expr} {n w : Int} {a : Seq Int} {k : List Stmt}
      (hi : Eval cap ρ ei (.ok (.int n))) (hv : Eval cap ρ ev (.ok (.int w)))
      (ha : ρ x = some (.arr a)) (h : n < 0 ∨ a.len ≤ n) :
      Step cap (.run (.store x ei ev :: k) ρ) (.trapped (.indexOOB n a.len))
  | store_trap_idx {ρ : Env} {x : String} {ei ev : Expr} {tr : Trap} {k : List Stmt}
      (hi : Eval cap ρ ei (.trap tr)) :
      Step cap (.run (.store x ei ev :: k) ρ) (.trapped tr)
  | store_trap_val {ρ : Env} {x : String} {ei ev : Expr} {vi : Val} {tr : Trap} {k : List Stmt}
      (hi : Eval cap ρ ei (.ok vi)) (hv : Eval cap ρ ev (.trap tr)) :
      Step cap (.run (.store x ei ev :: k) ρ) (.trapped tr)
  | ite_true {ρ : Env} {c : Expr} {thn els k : List Stmt}
      (h : Eval cap ρ c (.ok (.bool true))) :
      Step cap (.run (.ite c thn els :: k) ρ) (.run (thn ++ k) ρ)
  | ite_false {ρ : Env} {c : Expr} {thn els k : List Stmt}
      (h : Eval cap ρ c (.ok (.bool false))) :
      Step cap (.run (.ite c thn els :: k) ρ) (.run (els ++ k) ρ)
  | ite_trap {ρ : Env} {c : Expr} {thn els k : List Stmt} {tr : Trap}
      (h : Eval cap ρ c (.trap tr)) :
      Step cap (.run (.ite c thn els :: k) ρ) (.trapped tr)
  | while_true {ρ : Env} {c : Expr} {body k : List Stmt}
      (h : Eval cap ρ c (.ok (.bool true))) :
      Step cap (.run (.while c body :: k) ρ) (.run (body ++ .while c body :: k) ρ)
  | while_false {ρ : Env} {c : Expr} {body k : List Stmt}
      (h : Eval cap ρ c (.ok (.bool false))) :
      Step cap (.run (.while c body :: k) ρ) (.run k ρ)
  | while_trap {ρ : Env} {c : Expr} {body k : List Stmt} {tr : Trap}
      (h : Eval cap ρ c (.trap tr)) :
      Step cap (.run (.while c body :: k) ρ) (.trapped tr)
  | ret_ok {ρ : Env} {e : Expr} {v : Val} {k : List Stmt}
      (h : Eval cap ρ e (.ok v)) :
      Step cap (.run (.ret e :: k) ρ) (.done v)
  | ret_trap {ρ : Env} {e : Expr} {tr : Trap} {k : List Stmt}
      (h : Eval cap ρ e (.trap tr)) :
      Step cap (.run (.ret e :: k) ρ) (.trapped tr)
  -- compiled `defer` (§9): "true or halt", carrying the obligation name
  | check_pass {ρ : Env} {name : String} {c : Expr} {k : List Stmt}
      (h : Eval cap ρ c (.ok (.bool true))) :
      Step cap (.run (.check name c :: k) ρ) (.run k ρ)
  | check_fail {ρ : Env} {name : String} {c : Expr} {k : List Stmt}
      (h : Eval cap ρ c (.ok (.bool false))) :
      Step cap (.run (.check name c :: k) ρ) (.trapped (.deferViolation name))
  | check_trap {ρ : Env} {name : String} {c : Expr} {k : List Stmt} {tr : Trap}
      (h : Eval cap ρ c (.trap tr)) :
      Step cap (.run (.check name c :: k) ρ) (.trapped tr)
  -- fall off the end of the body: return unit
  | nil_ret {ρ : Env} :
      Step cap (.run [] ρ) (.done .unit)

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps (cap : Int) : Config → Config → Prop where
  | refl {c : Config} : Steps cap c c
  | head {c₁ c₂ c₃ : Config} (h : Step cap c₁ c₂) (hs : Steps cap c₂ c₃) :
      Steps cap c₁ c₃

/-- Terminal configurations: normal return or trap. Stuck `run`
configurations (⊥-reads, type confusion) are *not* terminal — they are
the states the static semantics must prove unreachable. -/
def Config.Terminal : Config → Prop
  | .run .. => False
  | .done _ => True
  | .trapped _ => True

/-- Behavior of a function body `k` from locals `ρ`: normal return. -/
def Returns (cap : Int) (k : List Stmt) (ρ : Env) (v : Val) : Prop :=
  Steps cap (.run k ρ) (.done v)

/-- Behavior: terminal trap. -/
def TrapsWith (cap : Int) (k : List Stmt) (ρ : Env) (t : Trap) : Prop :=
  Steps cap (.run k ρ) (.trapped t)

/-- Divergence: every reachable configuration can still step. This is
what `partial fn` (§8) permits and totality forbids. -/
def Diverges (cap : Int) (c : Config) : Prop :=
  ∀ c', Steps cap c c' → ∃ c'', Step cap c' c''

/-! ## Sanity theorems -/

/-- Terminal outcomes really are terminal: `done` has no successor. -/
theorem done_no_step {cap : Int} {v : Val} {c : Config} :
    ¬ Step cap (.done v) c := nofun

/-- ... and neither does a trap: traps are not recoverable (§9: no
catching; a `defer` failure halts the machine). -/
theorem trapped_no_step {cap : Int} {t : Trap} {c : Config} :
    ¬ Step cap (.trapped t) c := nofun

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

/-! ## Smoke tests: tiny derivations exercising both outcome kinds -/

private def ρ₀ : Env := Env.empty

/-- `x = 1; return x + 1` returns 2. -/
example :
    Returns 1000
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
    TrapsWith 1000 [.ret (.div .i32 (.intLit .i32 7) (.intLit .i32 0))]
      ρ₀ .divByZero :=
  .head (.ret_trap (.div_zero (.intLit (by decide)) (.intLit (by decide)))) .refl

/-- `return (255 + 1 : u8)` ends in the overflow trap. -/
example :
    TrapsWith 1000 [.ret (.arith .add .u8 (.intLit .u8 255) (.intLit .u8 1))]
      ρ₀ (.overflow .u8) :=
  .head (.ret_trap (.arith_overflow (.intLit (by decide)) (.intLit (by decide))
    (by decide))) .refl

end SVM
end Sable
