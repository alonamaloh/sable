# ADR 0069 — a lending argument is the machine's unique borrow

**Decided 2026-08-16.** Extends ADR 0068 to the formal SVM, and gives the
machine its first parameter that is not a value.

## Context

ADR 0068 opened `&[bool]` and `&mut [bool]` parameters through the checker, VC
generation, the interpreter, and the dynamic monitor, and left the formal SVM
refusing them by name. That refusal was not payload-specific: `lower_fn_entry`
admitted integers, `bool`, and record shapes as parameters and nothing else, so
the machine had no array parameter of *any* element type. `&[u64]` was outside
the SVM core subset for exactly the same reason `&[bool]` was.

The value plane was already ready. ADR 0062 made an array `Val.arr (elem :
ValTag) (a : Seq Val)` — a payload tag beside ordinary machine values, one
implementation of length, index, allocation, and store over the tag — so a
Boolean array is not a new value shape and a borrowed one is not a new value
shape either. What was missing sat at the call boundary. `Step.call_enter`
copies argument values into a fresh environment and `Step.ret_pop` restores the
caller's, so a store through a `&mut` parameter died with the callee's frame.
The Rust interpreter has no such gap: `ExprKind::Borrow` clones the `Rc` and
the callee writes into the caller's storage by construction. Lowering
`f(&mut a)` as an ordinary value argument would therefore have been a
*divergence*, not a missing feature — and `corpus/svm-diff/` exists to catch
exactly that.

## Decision

**A call argument is either a value or a lending, and a lending is the
machine's unique borrow.**

```lean
inductive Arg where
  | byValue (e : Expr)
  | lend    (x : String)

def Arg.toExpr : Arg → Expr
  | .byValue e => e
  | .lend x => .var x
```

`Stmt.call` carries `List Arg`. Both forms supply the same entry value —
`Arg.toExpr` says so, and `Step.call_*` still evaluate
`args.map Arg.toExpr` left to right, so evaluation order, the ⊥-read, and
argument traps are untouched. What lending adds is *where the value goes back*:

```lean
def Arg.loans : List String → List Arg → List (String × String)
```

pairs each lent argument with the parameter that receives it, `call_enter`
records that list in the frame, and both ways of leaving a body — `ret_pop` and
`nil_pop` — apply `Env.restore` before binding the destination. A procedure
writes through a `&mut` parameter at least as often as a function does, so the
fall-off-the-end rule needs it as much as `ret` does.

**Why copy-in/copy-out is the whole story.** A unique borrow is exclusive: the
checker rejects any second name reaching that storage while the callee runs
(`borrow.conflict`, ADR 0022/0023), and the machine has no concurrency. So no
observer can distinguish a cell written through from one restored at the pop.
That is a statement about Sable's borrow discipline, not a convenience: the
model is faithful because the language guarantees exclusivity, and it would
stop being faithful the moment a shared mutable alias existed.

**A shared borrow gets no constructor.** Its whole promise is that the callee
does not write, and a value is exactly that promise. Giving `&[T]` a return
trip would model a write that the type forbids; giving it a distinct value
would be a second representation for storage the caller keeps.

**The loan list is derived, not declared.** `Arg.loans` reads it off the
argument list and the callee's parameter names, so the syntax has one place
that says "this argument is a lending". A separate annotation beside the
arguments would have let the two disagree.

**Nothing here is Boolean.** `Arg.lend` is payload-blind and shape-blind; the
Rust lowerer admits it for a unique borrow of an array of any element type,
because `resolve_array` and the store/index/length rules were already
payload-generic. `&[u64]` and `&mut [u64]` become lowerable parameters at the
same time as `&[bool]`, which is the honest consequence of the gate that
refused them being one gate.

## Consequences

### The machine

`Frame` gains `loans : List (String × String)`. `Stmt.call`'s argument list
changes type. Nothing else in the rule system moves: the raw heap, every
expression rule, `store`, `while`, `check`, and the trap and `undef` outcomes
are untouched, and a trap remains terminal, so a callee that traps returns no
loan.

The rules, the functional evaluator (`stepF`), and both directions of the
agreement theorem (`Step.stepF_eq`, `stepF_sound`) moved together, as they must
— the build fails otherwise. **No proof needed real work.** Every arm is the
same shape it was: agreement for a call is still `simp [stepF, hf,
ha.evalArgs_eq, hn]` with the argument list mapped through `Arg.toExpr`, and
agreement for a pop is still `rfl`, because `Env.restore` is a total function
that both sides name identically. Determinism, totality, and progress follow
from agreement exactly as before. That is the payoff of stating the write-back
as a function rather than as a case split in the relation.

`Sable/SVMArrayTests.lean` pins the behaviour directly, independently of the
agreement theorem: a lent array is written through and the same argument by
value is not; both ways of leaving a body return the loan; the result binding
and the loan are separate destinations; loans compose through frames and stop
exactly where a copy replaces a lending; a callee trap returns nothing; the
payload tag crosses the call, so an integer store into a lent *empty* Boolean
array is tag confusion rather than an OOB trap; lending an unbound name is the
⊥-read; and an integer array lends identically.

### The Rust bridge

`validate_parameter_ty` refuses the *owner* (`is_owned_array_of(&Ty::Bool)`)
rather than the array, and `lower_fn_entry` admits a borrowed array parameter
of any payload. This is the same owner/sequence split ADR 0068 made in VC
generation and the interpreter, applied to the third stage.

`lower_arg` decides the argument form from the argument's *type*, not its
syntax: a unique array borrow is `Arg.lend` whether it is written `&mut a` or
is a reborrow named directly, and everything else is `Arg.byValue`. Deciding by
syntax would have silently dropped the write-back for a reborrow passed on by
name. A unique borrow that names no local fails closed
(`svm.array_borrow_place`) — a loan needs somewhere to return to.

`docs/shape-admission.md` moves exactly two cells: `&[bool]` and
`&mut [bool]` × `svm parameter`, from `svm.bool_array_position_unsupported` to
`yes`. `[bool]` × `svm parameter` stays refused, because an owner still does
not cross a call boundary. `docs/type-matrix.md` does not move.

`corpus/svm-diff/bool_array_borrows.sable` compares ten zero-argument subjects
against `interp.rs`: write-through, a shared borrow reading the caller's
stores, length preservation, a loan reaching through two frames, a reborrow
naming the same storage, an empty loan keeping its payload, a callee trap, a
lent write followed by a caller trap, a store beyond a lent empty array, and an
integer array lending the same way. Removing the `lend` arm makes three of them
diverge, which is the check that the model is load-bearing rather than
decorative.

## What this change does not do

- **No borrow value.** `Val` is unchanged; a borrow is an argument form, and
  `Expr` still has no way to produce one. `&mut self`, `&mut` records, and
  `&mut` class receivers stay outside the core subset.
- **No owned array parameter.** The language has none, and passing an owner by
  value would have no lending semantics to give it.
- **No native lowering.** The LLVM emitter still refuses a borrowed Boolean
  array by name (`backend.unsupported`), and `&[bool]` still has no `llvm_ty`;
  leaving that allow-list closed is what keeps the missing IR type
  unreachable. That is a stage of its own.

`docs/design/sable-language-design.md` §10's formalization-status note said
"scalar parameters only — borrows stay scoped out". It is updated to describe
lending; the sentence was a status report, not a rule.
