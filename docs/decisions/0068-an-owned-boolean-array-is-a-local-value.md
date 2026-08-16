# ADR 0068 — an owned Boolean array is a local value; a borrowed one is a borrowed array

**Decided 2026-08-16.** The first payoff of ADRs 0062–0067: a shape opens
because the semantics were already written, and the only thing that changed is
which gates ask which question.

## Context

`[bool]` locals were proved, interpreted, monitored, modelled in the formal
SVM, and lowered to LLVM. `&[u64]` / `&mut [u64]` parameters were proved,
interpreted, monitored, and lowered. Their intersection —

```sable
/// post result ≤ m.len
pub fn count_true(&[bool] m) -> u64 { ... }
```

— was refused by `type.bool_array_param`, whose note claimed "parameter
transport must land together in every backend". That claim was not the
project's rule: `&[u64]` is `backend.unsupported` in LLVM today while `&[u32]`
is lowered, and G1.4b landed checker + VC + interpreter + monitor for owned
`[bool]` while both backends refused it.

The survey behind this change found **no integer-specific semantics anywhere in
the array-parameter path.** Every stage that gives an array parameter meaning
is already keyed on the payload or blind to it:

| what | where | already generic |
|---|---|---|
| Lean type | `vcgen::lean_array_ty` | `Ty::Bool => "Sable.Seq Bool"` |
| parameter binder, `_old_` twin | `vcgen`'s `Ty::Array(elem)` arm | `p.ty.binding_mode()` names it, `lean_array_ty` types it |
| element facts | `vcgen::array_element_range_prop` | `Ty::Bool => None` |
| loop havoc | `vcgen` | shared borrows filtered once, then `lean_array_ty` |
| call-site `&mut` havoc | `vcgen` | `as_unique_borrow().and_then(as_owned_array)` |
| element read | `vcgen`'s `Index` arm | `Ty::Bool => Val::Prop("... = true")` |
| element store | `vcgen`'s store bridge | `lean_bool_value` reifies the proposition |
| `Sable.Seq` and its four lemmas | `lean/Sable/Seq.lean` | polymorphic in `α` |

What refused the shape was a set of *gates* that spell `[bool]` with
`Ty::is_array_of(&Ty::Bool)`, and `is_array_of` looks **through** the borrow
(it is `self.referent()` plus a payload comparison). One accessor is why
`[bool]`, `&[bool]`, and `&mut [bool]` all landed on the same refusal in five
files.

## Decision

**Every gate that was written about the owned Boolean array now says so.**
`is_owned_array_of(&Ty::Bool)` replaces `is_array_of(&Ty::Bool)` at the gates
whose rule is about an owner, and the gates whose rule is about a sequence keep
looking through the borrow.

The distinction is not a spelling convenience. It is the same one ADR 0067
made terminal in `Ty::is_affine`: **a bare type owns and a borrow never does**,
so a rule that exists to keep an owner in one place has nothing to say about a
borrow, and a rule about what a sequence *is* has nothing to say about who owns
it.

Concretely:

- `vcgen::validate_vc_type_position` restricts only the owned array, to
  `Expression` and `Local`. A borrowed Boolean array carries a proof model at
  every position, so this gate stops answering for it and the positions a
  borrow may be *written* in stay `Parser::admits`'s `BorrowParam` row and
  `check::borrow_referent_ty`'s to state (ADR 0067).
- `vcgen`'s producer allow-list (literal / allocation / consistent named local)
  applies to the owned array only: an owner has to come from somewhere the
  ownership rules know about, while a borrow is not produced at all.
- `reject_owned_bool_array_value` — the call, field, return, statement, and
  field-store boundaries — likewise.
- `check::parameter_ty` loses its Boolean-array refusal outright, and
  `check::bool_array_borrow` with all three of its call sites.
- `interp::validate_interp_ty` stops refusing a borrowed Boolean array
  altogether; `validate_interp_nonlocal_option_position`, the executable-value
  producer list, `validate_interp_sink`'s transport rule, and
  `reject_owned_bool_array_transport` restrict the owner only; and
  `ExprKind::Borrow`'s Boolean-array refusal is deleted, because lending is
  what a borrow is for.

**Two diagnostics are deleted rather than narrowed**, and that is the load-
bearing half of the decision:

- `type.bool_array_param`. Narrowing it to the owned case would leave a
  non-`internal.` diagnostic that no source program can produce — the parser's
  `P::Param` row refuses `S::Array` for *every* element type under
  `type.param_unsupported` — so no `corpus/must-fail/` subject could pin it,
  which the corpus convention forbids. `[u64]` already reads `yes` at this
  gate for exactly that reason, and `[bool]` now matches it. The rule "an owned
  array is not a parameter" is unchanged; it lives in one place instead of two.
- `type.bool_array_borrow`. `var view = &flags;` on a `[bool]` is now legal
  because it is legal on a `[u64]`, and there was no second rule to keep.

### The proof side: which facts a Boolean array parameter carries

- **binder**: `m : Sable.Seq Bool` for `&[bool]`; `_old_m : Sable.Seq Bool` for
  `&mut [bool]`, registered in `entry_states` so `old m` resolves to it.
- **`h_m_len : 0 ≤ m.len ∧ m.len ≤ u64.max`** — unconditional, and it is a
  fact the target program's own overflow VC needs (`c ≤ i < m.len ≤ u64.max`
  is what makes `c + 1` representable).
- **no element fact.** This is an answer, not a gap. An integer array's
  `h_a_elems` states that every element inhabits its width; `Bool` *is* its
  complete value domain, so the analogous proposition does not exist and a
  fabricated numeric bound would not even be well-typed.
  `array_element_range_prop` already returned `None` for `Ty::Bool`, with that
  reasoning written down.
- **loop havoc, shared borrow**: nothing. A `&[bool]` is never a store target,
  so it never enters the mutation set and `m` survives the loop head unchanged
  — which is exactly what a shared borrow guarantees, and what makes
  `post result ≤ m.len` provable from `invariant c ≤ i`.
- **loop havoc and call havoc, unique borrow**: a fresh binder plus
  `name.len = _old_name.len`, and nothing about elements. Sound for the same
  reason it is sound for integers: stores are the only mutation and
  `Seq.len_set` preserves length by construction.

No Lean lemma was needed. `Sable.Seq` and all four of its lemmas are
polymorphic in `α`; the `Seq Int`-only vocabulary in `Sable/Specs.lean`
(`sorted`, `contains`, `perm`, `count`) is unreachable from this feature and
remains a separate, purely additive decision.

### The execution side: aliasing, ownership, and the entry snapshot

The interpreter needed no new execution code, and that is the same fact stated
at a different stage. `RtArray` carries its payload tag beside its values, so
length, an index read, and an element store are one implementation over the
tag rather than a Boolean copy of an integer one. `ExprKind::Borrow` clones the
`Rc<RefCell<RtArray>>`, so a `&mut [bool]` argument *is* the caller's storage
and a callee's writes are visible without a write-back step. `drop_owned_params`
matches the bare constructors, so a lent array is destroyed by its owner at the
end of the owner's scope and never by the callee — the property ADR 0067 made
unwritable rather than merely unwritten.

The dynamic monitor needed none either. A frame snapshots a unique borrow's
array at entry (`RtArray::to_spec`) and binds it as `old p`, and that snapshot
is payload-carrying: `SpecArray` keeps the checked payload, `SpecVal::Bool` is
an ordinary specification value, and `SpecVal::default_of(Ty::Bool)` is `false`,
which is Lean's `default` for `Bool` — so even an out-of-range `m.get k` in a
clause has the value Lean gives it rather than reaching `monitor.no_junk_value`.
A borrowed Boolean array is therefore monitorable at **zero skipped clauses**:
`m.len`, `m.get k`, a bounded `∀`, an `↔`, and `(old m).get k` all evaluate.

### A trait signature may not name an array

Deleting the Boolean-array parameter refusal exposed a panic that predates it:
`type.trait_param_unsupported` matched only `Ty::Bool | Ty::Record(_)`, so an
array in a trait method signature reached `vcgen`'s `TraitCall` arm and hit
`unreachable!("checked: int args")`. That was reachable from source with
`&[u64]` before this change; `&[bool]` would have joined it.

The gate now refuses an array in any binding mode. An abstract trait call
substitutes integer arguments into the trait's contract, and a `Sable.Seq T` is
not one — so the refusal belongs at the signature, where a reader can act on
it, rather than at the call that would need the missing model.
`corpus/must-fail/trait_array_param_unsupported.sable` pins the integer case
and `bool_array_trait_param.sable` the Boolean one, because the rule is about
the abstract call and not about the payload.

## What this change does *not* do

The formal SVM and the LLVM emitter still refuse a borrowed Boolean array **by
name** — `svm.bool_array_position_unsupported` and `backend.unsupported`. That
is an ordinary state in this compiler, and both fences are load-bearing rather
than incidental:

- `corpus/verifies`, `corpus/must-fail`, and `corpus/tests` reach the checker,
  VC generation, Lean, and the interpreter, never `svm.rs` or `llvm.rs`, so a
  `&[bool]` parameter in one of those subjects cannot reach either backend.
- `corpus/svm-diff` lowers **every** function in each file and treats a
  lowering failure as a hard failure, so no subject there may carry one.
- `&[bool]` has no `llvm_ty`. Leaving `require_parameter_value`'s allow-list
  untouched is what keeps that `unreachable!` unreachable.

The formal SVM has no array parameter of *any* payload — `lower_fn_entry`
admits scalars and record shapes — so opening it means giving the formal
machine borrow semantics, which is a larger question than this shape.

> **ADR 0069 supersedes the formal-SVM half of this section.** The machine now
> has a lending call argument, `lower_fn_entry` admits a borrowed array
> parameter of any payload, and `corpus/svm-diff/bool_array_borrows.sable`
> carries one. The LLVM half stands: `&[bool]` still has no `llvm_ty`, and
> `require_parameter_value`'s allow-list is still what keeps that
> `unreachable!` unreachable.

## Consequences

**`docs/type-matrix.md` moves exactly two cells**, `[bool]` × `param` and
`[bool]` × `param &mut`, both `no → yes`; `Open cells: 33/81 → 35/81`; two rows
leave "What closes each cell" (`type.param_unsupported` and
`type.bool_array_param`). Nothing else moved — in particular
`option<[bool]>` × `param` still reads `type.affine_option_param`, because
`parameter_ty` asks `is_affine_option` *before* anything else and the ordering
is what protects it.

**`docs/shape-admission.md` moves nine cells, three rows:**

| row | gate | was | is |
|---|---|---|---|
| `[bool]` | check parameter | `type.bool_array_param` | yes |
| `&[bool]`, `&mut [bool]` | check parameter | `type.bool_array_param` | yes |
| `&[bool]`, `&mut [bool]` | vc local position | `internal.vcgen.type_error` | yes |
| `&[bool]`, `&mut [bool]` | vc parameter position | `internal.vcgen.type_error` | yes |
| `&[bool]`, `&mut [bool]` | interp type | `interp.array_position_unsupported` | yes |

`vc local position` is not optional company: with the borrow refusal gone,
`var view = &flags;` is checkable, and an `internal.`-namespaced error a source
program can reach is a bug.

Everything else held, and the cells worth naming because they *did not* move
are the ones that would have signalled a lost gate rather than a written
semantics: `[bool]` × `vc parameter position` stays `internal.vcgen.type_error`
(the gate was refined, not dropped); all three Boolean-array rows keep
`svm.bool_array_position_unsupported` at `svm parameter` and
`backend.unsupported` at every LLVM column except `[bool]`'s owned local; and
no `[u64]`, `[u32]`, `class`, `record`, option, or nested row changed at all,
which is the evidence that `is_array_of` itself was left alone. Changing that
accessor instead of the individual gates would have moved a dozen cells at once
and lost real rules — it has call sites in class fields, exposure, method
receivers, exposure sources, and transport rejections.

**Corpus.** `bool_array_param.sable` and `bool_array_borrow.sable` are deleted
— they pinned rules that no longer exist. `bool_array_extern_param.sable`
retargets to `extern.param_abi` and `bool_array_trait_param.sable` to
`type.trait_param_unsupported`, both of which are the honest answer for a
borrowed array of any payload;
`trait_array_param_unsupported.sable` is new.
`corpus/verifies/bool_array_params.sable` verifies 37/37 obligations across six
functions with one hand discharge — reads, a loop invariant over elements, a
shared borrow passed on to a second function, an owner lending a literal, a
`&mut [bool]` writer with `old m`, and a `&mut` round trip whose postcondition
is provable only from the callee's posts over the fresh post-call sequence.
`corpus/tests/test_bool_array_params.sable` runs those same contracts: seven
dynamic tests, **zero skipped clauses, and no `expect-skip` fence**. It observes
what a borrow is for — a `&mut` argument's writes appearing in the caller's
array, a `&` argument leaving it alone, a reborrow naming the same storage, an
empty borrowed array keeping its Boolean payload, and lending twice being two
borrows and no transfer.

No new diagnostic is introduced, so no new `corpus/must-fail/` subject is owed.
The rules a borrowed Boolean array can now break are the ones every borrow has:
`type.store_shared` refuses `m[0] = true` on a `&[bool]`, and
`borrow.conflict`, `mut.borrow_immutable`, and `type.mut_borrow_shared` are
already pinned for arrays of any payload.

**ADR 0063's prose is superseded in one place**: its "what a position demands
beyond a spelling" paragraph cites `type.bool_array_param` as an example of a
checker gate the parser table defers to. The example is gone; the paragraph's
claim is not, and `type.option_param` and the affine-option boundary still
illustrate it.

## What did not land

The formal SVM is the next stage, and it needs borrow semantics for the formal
machine before it can have an array parameter at all — ADR 0069 is that stage.
Then LLVM, which needs an IR type for `&[bool]` before its parameter allow-list
may widen.

A Boolean-array contract still cannot write `count(m, true)`: the
specification vocabulary in `Sable/Specs.lean` is `Seq Int`-only. Nothing in
this change depends on that, and widening it is additive.
