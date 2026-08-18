# ADR 0085 — an owned array crosses a call

**Decided 2026-08-18.** An owned array is transferred at a call boundary the
way every other owned value is: a bare array name is a move into an owned
parameter, `return` moves one out, and the caller of an array-returning
function receives sole ownership of storage it never named.
`docs/type-matrix.md` opens `[u64]`, `[bool]`, and `[record]` at `return` and
at `param`.

## Context

ADR 0030 states the rule this slice completes: *a move is one operation, and
every sink performs it* — a declaration, an assignment, a field assignment, a
call/constructor/method argument, and a return all take a value. Owned arrays
are affine (`Ty::is_affine`, ADR 0067) and already move at three of those
sinks: an array literal or allocation initializes a declaration, and
`self.buf = nb;` moves an owner into a field with `array.use_after_move`
guarding the source. The two missing sinks were exactly the two that cross a
call: **argument** and **return**.

Neither was missing because the semantics were unwritten. The proof path is
payload-generic and already builds every fact a transferred array needs:
`fresh_state_for`'s `Ty::Array` arm (ADR 0074) is one binder of
`lean_array_ty`, a length fact, and the payload's element fact, and it is what
a `&mut [T]` argument's post-call state has been built from all along. The
interpreter's `eval_moved` already clears an `RtVal::Arr` source place, and
`drop_owned_params` already matches `Ty::Array(_)` so an owned array parameter
dies with the callee's frame. The formal machine's `call_enter` and `ret_pop`
are `Val`-generic (ADR 0069), and `svm.rs` already lowered a function whose
declared return type is an array.

What refused the two sinks was a set of gates:

| refusal | where | what it said |
|---|---|---|
| `type.param_unsupported` | `Parser::admits`, `P::Param` row | an owned array is not a parameter |
| `type.array_return` | `check::return_ty` | arrays cannot be returned yet |
| `type.array_value` | `check_expr`'s `Var` arm | an array name is not a value |
| `internal.vcgen.call_return_unsupported` | the call-result binder | an array has no call-result state |
| `internal.vcgen.type_error` | `validate_vc_type_position` | an owned `[bool]` is a local or a field |
| `interp.array_position_unsupported` | the interpreter's validator | a `[bool]` owner is a local |

`type.array_return`'s own note names the gap it was holding: *an owned array
local has no ownership-transfer rule across a return boundary.* This ADR is
that rule.

Two earlier ADRs are superseded on their own terms rather than contradicted.
ADR 0068 kept "an owned array is not a parameter" only as *an unchanged rule
living in one place*, on a corpus-convention argument about where a diagnostic
may live — it defended nothing. ADR 0069's reason was machine-side and is now
satisfied by ADR 0069 itself: "passing an owner by value would have no lending
semantics to give it" was true before `Arg.byValue` existed as a form distinct
from `Arg.lend`, and an owner crossing by value is precisely the form that
records no loan. The design doc, meanwhile, has said since v0.4 that "by-value
passing **moves** ownership unless the type is `copy`", and an array is not
`copy` — so the compiler was behind the design here, not ahead of it.

## Decisions

1. **A returned array is a move out of the callee, and the caller assumes it
   is fresh storage.** The call-result binder is
   `fresh_state_for(ret, sym, base, LenFact::Bounded)` — the same dispatch
   parameter entry and every havoc consume, so the result carries the binder,
   the length fact, and the payload's element fact (integer ranges; nothing for
   `Bool`, whose domain is complete; elementwise `R.wf` for a record) that
   every checked inhabitant of the type satisfies. The callee's posts over
   `result` then say the rest.

   **`LenFact::Bounded`, never `LenFact::Eq`, is the load-bearing half.** A
   `&mut [T]` argument comes back in a fresh state whose length is *equated to
   the pre-call chain*, because it is the same storage and `Seq.len_set`
   preserves length. A returned array is storage the caller never held, so
   there is no prior chain to equate it to and no length to preserve. A caller
   that wants to know `result.len` reads it from a post. Writing `Eq` here
   would fabricate a relation between two unrelated sequences, which is the
   stale-chain shape ADR 0074 exists to prevent.

2. **An owned array parameter is a move into the callee, which owns it and
   drops it with its frame.** The caller's place dies at the argument sink
   through the one `transfer`, and `array.use_after_move` already names the
   violation. Nothing about the callee's entry state is new: an owned parameter
   binds under its own source name with `LenFact::Bounded` facts, exactly as a
   `&[T]` parameter does, and has no `_old_` twin because no havoc will replace
   it.

3. **An argument's form follows the parameter's binding mode.** A borrowed
   array parameter takes an explicit borrow and an owned one takes a bare owned
   place. `type.array_arg_borrow` narrows to the borrow case rather than
   disappearing: "array arguments are passed by explicit borrow" stops being
   true of every array parameter and stays true of every borrowed one.

   **A moved owner may not overlap a borrow in the same call**
   (`array.moved_while_borrowed`). This is ADR 0022/0023's overlap rule seen
   from the other side, and the new sink genuinely needed it: `f(&mut a, a)`
   hands the callee a borrow promising the caller keeps the storage *and* the
   storage itself, so VC generation havocs `m` into a fresh sequence while `xs`
   keeps the entry value, and one write reaches both. That combination verified
   a false postcondition before this rule existed. Argument order is why it
   needs stating separately: a borrow *after* a move meets
   `array.use_after_move`, because the move already killed the place, while a
   move after a borrow leaves the borrow recorded and nothing relating them.
   The shared case is refused too — a promise the caller keeps the storage is
   broken by giving it away, whatever either name goes on to do.

   The rule is stated for owned arrays rather than for every affine argument,
   and the class case was checked rather than assumed: `f(&mut c, c)` is
   admitted and is *not* exploitable, because a by-value class parameter binds
   a fresh state carrying field facts and the invariant rather than an equation
   to the caller's value, so the logic never relates the two names closely
   enough to contradict itself. That is a property of how class arguments are
   modelled, not of the overlap rule — if a later slice ties a class parameter
   to its caller's state, this is the rule to widen.

4. **An owned array parameter is not writable, because no parameter is.**
   Element stores need the exclusive right to storage, which a `mut` owner and
   a unique borrow have; a parameter has no `mut` spelling in the language, so
   `mut.store_immutable` refuses a store through one. This is not an array
   rule and this ADR does not invent one: `mut` parameters would apply to every
   type at once and are a separate decision with their own spelling to design.
   The consequence is worth stating plainly — an owned array parameter is for
   *keeping or passing on* an array, and `&mut [T]` remains how a callee
   writes one.

   It also removes a divergence rather than merely leaving it unobserved. The
   interpreter shares the caller's `Rc` with the callee (ADR 0068) while the
   formal machine copies the argument value at `call_enter` (ADR 0069). A
   callee that could write through an owned parameter would write the caller's
   storage in one implementation and its own copy in the other. What keeps that
   unobservable is that the caller's place is dead for the rest of its scope —
   and the one arrangement where it was *not* dead, `f(&mut a, a)`, is exactly
   what decision 3's overlap rule had to close. An unwritable parameter makes
   the divergence unwritable rather than leaving it resting on the reachability
   argument alone.

5. **An owned array always has a place.** A discarded array-valued call result
   would be an owner with no name and no lexical death, so it is refused:
   `type.bool_array_temporary` widens to `type.array_temporary` and covers every
   owned array. One rule in one name, the same reason ADR 0068 deleted
   `type.bool_array_param` rather than narrowing it. A call result therefore
   reaches a declaration, which is where the producer rule already lives —
   `type.owned_array_outside_test`'s initializer set gains the call that returns
   an owner, beside the allocation and the literal.

6. **A bare array name is a value exactly where a move consumes it.** The
   `Var` arm's escape fires when a sink supplies the array's own type as the
   expected type — a return and an owned argument — which is word for word the
   rule `type.class_value` already states ("class values cannot be copied or
   moved yet — returning a local is the exception"). `var ys = xs;` stays
   refused because an inferred declaration supplies no expected type, and a
   typed local-to-local move stays refused outside a test by the declaration's
   own producer rule. Naming an array anywhere a move does not consume it —
   an index base, a length receiver, a lending argument — is unchanged.

7. **Members and traits stay closed, each in its own name.** `return_ty` is
   shared by ordinary functions, class methods, and trait methods, so opening
   it would open three positions at once. A class method returning an array is
   refused by `type.member_array_return`, mirroring `type.member_record_return`
   — the method call boundary carries its own argument-reification and
   receiver-state machinery that has never seen an array, and the interpreter's
   `invoke`/`construct` paths lack the array arms `call` has. A trait method
   returning an array joins `type.trait_return_unsupported`, for the reason
   `type.trait_param_unsupported` already gives about array parameters: an
   abstract trait call substitutes integer arguments into its contract, and a
   sequence is not one. Owned array init and method parameters stay closed under
   `type.member_param`.

8. **The borrow-family return never gets a second fence.** `-> &[T]` was
   refused only by the parser's `TyPos::Return` row; `check::return_ty` would
   have accepted `Ty::Borrow(_, Array)`, which the shape-admission table
   recorded as `yes`. A slice that rewrites that function must not leave the
   never-cell resting on the layer it is rewriting, so the checker now states
   the rule too, under the parser's own name (`type.return_unsupported`) — one
   rule, one name, two layers.

9. **The formal machine leg opens; the native leg stays closed.** The SVM needs
   no Lean edit at all: `call_enter` binds whatever the argument evaluated to
   and `ret_pop` binds whatever came back, the agreement proofs are shape-blind
   over both, and the change is `lower_fn_entry` admitting an owned array
   parameter plus the Boolean-array gates narrowing to the boundaries that
   remain. One rule is worth naming because the lowerer had to learn it in two
   places at once: reading an owned array's name is refused everywhere, because
   binding its value elsewhere would leave two names for one sequence in the
   machine's environment — and a return and an owned argument are exactly the
   two places where it would not, since the frame that held it stops naming it.
   `moved_owner` is that rule, consulted by both sinks.

   That leg is worth opening precisely because the two executables disagree by
   construction — the interpreter hands over the `Rc` the caller held, the
   machine copies a value into a fresh environment — so a differential subject
   is evidence and not a formality. LLVM keeps refusing the shapes under
   `backend.unsupported`, as it does for `option<u64>` parameters the checker
   admits; `docs/shape-admission.md`'s LLVM columns are the guard that it
   stayed closed.

10. **A contract still speaks about a parameter the body handed on.** An owned
    array parameter is snapshotted into the monitor's entry values at the call,
    deeply rather than by sharing the `Rc`, so a callee that moves its parameter
    on — `passthrough` hands it straight back out — keeps posts that name it
    monitorable. That is ADR 0030's rule applied to a new type, not a new rule:
    a value outlives the transfer of authority over it. A *borrowed* array keeps
    the established convention, where clauses read current contents and `old p`
    is the entry snapshot.

## Consequences

`docs/type-matrix.md` opens six cells — `[u64]`, `[bool]`, and `[record]` at
`return` and at `param` — taking it from 75 to 81 of 180 intended. The
`init param` and `method param` cells for those rows stay closed but change
their recorded closing diagnostic from `type.param_unsupported` to
`type.member_param`, because the parser row that fired first is gone and the
member gate that always meant it now answers; each flip is corpus-pinned.

`docs/shape-admission.md` gains `vc return position`, `interp return`, and
`svm return`. With `type.array_return` deleted, the stage gates behind it were
watched by no ratchet at all, and a table that cannot see the new frontier is
not a guard. Adding them first is what made the change legible: it showed
before any gate moved that an integer or record array was refused at
`check return` alone, with every stage behind it already answering yes, while
a Boolean array was fenced at all four.

`corpus/verifies/array_return.sable` proves 57 obligations with no hand
discharge and `array_param.sable` 68 with one — the record payload's `wf`
unfolding, which a borrowed record array needs too. The negations keep a
borrow from being laundered into an owner (`fn f(&mut [u64] m) -> [u64]`
names a value it does not own), an owner from being read out of a field, a
member or trait result from inheriting the ordinary function's rule, a
discarded result from existing at all, a store from reaching through a
parameter, and an array from being lent and handed over in one call — that
last one carries the false postcondition it used to prove, in both borrow
modes, because a fence is worth more when it shows what it caught. Two `same-run` pairs compare a return against building in place
and a move against a lend. `corpus/svm-diff/array_return.sable` and
`array_param.sable` put the interpreter's shared `Rc` and the machine's copied
value on the same outcomes in both directions.

`corpus/must-fail/param_owned_array.sable` is deleted rather than edited: it
pinned the rule this ADR reverses, and its comment asserted it in so many
words.
