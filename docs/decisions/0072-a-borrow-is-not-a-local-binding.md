# ADR 0072 — a borrow is not a local binding

**Decided 2026-08-16.** Closes a soundness hole: `var view = &mut a;` proved
false contracts, for every payload and every referent, in the checker, VC
generation, the class and resource paths, and inside `unsafe`.

## Context

The symbolic environment VC generation carries is a map from **source name** to
symbolic value:

```rust
env: HashMap<String, Val>
```

Every rule that touches storage is written against that map by name. A store
writes back under the store target's name; the call-site havoc for a `&mut`
argument writes back under the argument's name; `havoc_mut_borrow_args` and the
loop-head havoc build their assigned sets out of syntactic names; `old p`
resolves through `entry_states`, which is keyed the same way. Most of the
sixty-odd `env.insert` sites in `vcgen.rs` key off a syntactic name.

That model is correct exactly when **each name is the only name for its
storage**. Inside a callee body that is true of a `&mut` parameter: the
parameter is created once from its `_old_p` binder, read through that key,
written through that key, and havocked through that key, and the language gives
the referent no second spelling in that scope. The parameter path is not
accidentally sound — it is sound *given* exclusivity.

`var view = &mut a;` removes exclusivity. `ExprKind::Borrow` evaluated to a
**snapshot of the owner's current term**, and `Stmt::VarDecl` stored that
snapshot under the new name, so `a ↦ Arr(S)` and `view ↦ Arr(S)` became two
independent entries holding equal terms. The first store through either name
moved only that entry. Both names were then believed, and they disagreed:

```
/// post ¬result
pub fn f() -> bool {
    mut [bool] a = alloc_array<bool>(3, false);
    var view = &mut a;
    view[0] = true;
    return a[0];
}
```

`sable check`: *fully verified, 3 obligations, 3 proved.* At run time `a[0]` is
`true`, so `result` is true and the post is false. `sable test` caught it; the
proof did not.

The hole was payload-independent and referent-independent. The same program over
`[u32]`, over a class (`var r = &mut c; r.bump(); c.get()`), over a class field
(`var cells = &b.cells; b.poke();`), over a resource inside `unsafe expose`, and
through a shared borrow with the owner written directly all verified false
contracts. It reached further than the function containing the borrow: an
aliased pair of arguments handed to an ordinary borrow-free callee —
`g(&mut a, &mut view)` — proved that callee's false post, because the
`Place::overlaps` check that correctly rejects `g(&mut a, &mut a)` compares
roots and `view` is its own root. And a `&mut` array borrow live at a loop head
indexed `entry_states` for a name only a parameter ever has, which was a panic
rather than a diagnostic.

Two things kept it invisible. The corpus contained exactly **one** local-borrow
declaration in 395 subjects, in a must-fail subject fenced on a different rule
(`option.affine_borrow`), so no subject exercised the construct. And both
admission ratchets measured what each stage *admits*, not what any of it
*means*, so they read green truthfully: `docs/type-matrix.md` probes through the
parser and a borrow has no declared local spelling to probe, and
`docs/shape-admission.md` had no local-declaration column at all.

## Decision

**A borrow is an argument form and a parameter binding mode. It is not a local
binding.** `check::local_ty` refuses a local whose type is not owned, under
`type.borrow_local_unsupported`, at the initializer's span.

The rule is keyed on `Ty::binding_mode()` and nothing else. It does not ask what
the borrow names, so it covers an array of every payload, a class, a class
field, a resource, an option, a raw pointer, and any reborrow of those, and it
cannot be narrowed to one payload by accident. That is deliberately the same
shape as ADR 0067's `Ty::is_affine`: the question is about the binding mode, so
the answer is read off the binding mode.

`var x = <borrow expression>` is the only door. A borrow has no declared local
spelling (`&mut [bool] view = ...` is a parse error, since the borrow prefixes
are a separate production from the recursive type core), it is not admitted as a
return type, so no call result is borrow-typed, and `expose` binds a `raw<u8>`
and an owned resource rather than a borrow. The one initializer form that does
not *look* like a borrow is a bare name that already holds one — `var d = c;`
where `c` is a `&mut C` parameter — and it goes through the same gate, because
the gate reads the inferred type rather than the syntax.

Two supporting changes state the same rule where the rest of the pipeline can
see it:

- `validate_vc_type_position` refuses `Ty::Borrow` in `VcTypePosition::Local`.
  VC generation has no honest answer for the shape either, and the preflight is
  where that is said rather than deep in `-> Val` recursion.
- The loop-head havoc's `entry_states[name]` becomes a lookup with a named
  fail-closed refusal instead of a `HashMap` index. Only a parameter has an
  entry state; if some other name reaches that arm the length relation has
  nothing to be relative to, and refusing is the answer the file already gives
  elsewhere.

`docs/shape-admission.md` gains a `check local` column, so the rule is a blessed
cell for every shape rather than a line of code. Adding that column made fifteen
borrowed shapes newly *distinguished* from their owned form, which
`every_distinguished_binding_mode_is_probed` demanded samples for — the audit
widening itself, as its comment says it should.

## What this does not do

**It fences the hole; it does not build an aliasing model.** The checker still
records no loan. `Place` has no root→owner relation, `contains`/`overlaps` is
consulted only within one call's argument list, and there is no loan liveness.
What makes the tree sound today is that a borrow now exists only where the
compiler already relates it to its owner: written at a call, bound to a
parameter for the length of the call, with the argument-overlap rule (ADR
0022/0023) enforcing exclusivity across that one call. No *borrow* gives one
storage a second name that survives a statement boundary, so the name-keyed
environment's premise holds for every borrow.

It does not hold everywhere. `unsafe expose` binds a raw pointer and a resource
over an array's bytes and leaves the owner's name in scope for the body, so
`a[0] = 1` beside a `raw_load8` of `a`'s own address are two names for one
buffer, and both are believed. Programs asserting contradictory things about
the two verify. The proof, the interpreter, and the formal machine all agree
today only because all three model exposure as copy-in/copy-out; the premise
under which that is faithful — ADR 0069's, that no second name reaches the
storage — is the one exposure does not establish. The fix has the same shape as
this rule, one scope wider: freeze the exposed array for the body. It is not in
this change, and until it lands the defect class is fenced for borrows and open
for exposure.

> **Amendment (ADR 0073).** The exposure gap this paragraph leaves open is
> closed: an open exposure now freezes its owner's name for the body
> (`expose.owner_frozen`), which also refuses nested exposure of one array.

The alternative was to make the environment resolve through an alias relation:
bind a borrow local to a place, canonicalise to the owner at every write-back
site (all five of them), re-derive aliases from the fresh owner binder at each
loop head, decide what `old` through a borrow means, and give `Place` a loan map
that `contains`/`overlaps` follows. The vcgen half is mechanical; the checker
half is NLL-shaped loan liveness — when a loan ends, whether the owner may be
used while a shared loan is live, whether two shared loans may coexist — which
is a design the language does not have and would need its own ADR, its own
must-fail family, and its own ways of being subtly wrong. Doing it first would
mean the tree kept proving false theorems for however long that took, including
about ordinary `&mut`-parameter functions that contain no borrow at all.

So the refusal is the decision, and it is not a placeholder for a rewrite that
is scheduled. If borrow locals are wanted later they arrive with an aliasing
model, and this rule is what they replace.

**Nothing true is lost.** The only dynamically-correct thing the construct could
express was writing and reading consistently through one borrow, and that is the
owner's own name spelled differently.
`corpus/verifies/borrow_is_an_argument.sable` is every refused program's
rewrite, in both forms the diagnostic names: use the owner's name, or write the
borrow at the call. `corpus/tests/test_borrow_is_an_argument.sable` runs the
same functions, because the lesson of this hole is that a proof answer with no
run answer beside it is unwatched.

## Consequences

- `type.borrow_local_unsupported` is a named, spanned refusal with a note that
  says what to write instead. Seven `corpus/must-fail/` subjects reach it, one
  per referent family — Boolean array, integer array, shared array borrow,
  class, class field, resource, and a bare name that already holds a borrow — so
  a future narrowing to one family fails a subject rather than reopening a hole.
- `corpus/must-fail/affine_option_borrow.sable` still fails earlier, under
  `option.affine_borrow`. That refusal is about there being no borrowed
  conditional-owner representation, and it says more than this rule would.
- No program that verifies today stops verifying except ones whose contracts
  were false. This rule moves no cell of `docs/type-matrix.md`: a borrow has no
  local spelling for it to probe, which is why the rule needed the stage-gate
  table instead. The file does move in the same change, two cells, for ADR
  0068's reasons.
- `corpus/test-fails/borrow_argument_aliases_the_owner.sable` pins the
  positive fact the fix leaves standing — a `&mut` argument *is* the caller's
  storage — from the run side, and `sable check` refuses the same contract, so
  the two answers agree in both directions.
- Boolean array *parameters* (ADR 0068) are untouched and sound. That work
  deleted `type.bool_array_borrow`, which had fenced `[bool]` — and only
  `[bool]` — out of the borrow-expression position; integer arrays were never
  behind it and had been in this hole since ADR 0023. The deletion was correct
  on its own terms and is not resurrected: a payload-specific,
  expression-position-specific refusal is exactly the arrangement that produced
  a hole one payload wide. Its replacement is a binding-mode rule.
