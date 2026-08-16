# ADR 0067 — one borrow constructor: a bare type owns

**Decided 2026-08-16.** Completes the remaining item on ADR 0064's "what did
not land" list, and reverses one sentence of it (see "Resource borrows fold
too").

## Context

ADR 0064 made container payloads full types and ADR 0065 made
`Ty::Option(Box<Ty>)` the only option constructor. Binding mode was the last
thing the grammar encoded positionally: mutability was carried *inline* by the
constructors that could be borrowed.

```text
Ty::Array(Box<Ty>, Mutability)      // [T], &[T], &mut [T]
Ty::ClassRef(usize, Mutability)     // &C, &mut C
Ty::ResRef(ResKind, Mutability)     // resource &K, resource &mut K
```

Three consequences, each of which the tree paid for:

- `&Nat` and `&[u64]` were two unrelated shapes even though they are one shape
  in the grammar, and any future borrowable constructor had to add its own
  `Mutability` field rather than inherit one;
- `Mutability` had a third variant, `Owned`, whose doc comment described a
  *non*-borrow. It appeared in `ClassRef` and `ResRef` nowhere in the tree, so
  two of the three constructors could spell a state they never meant;
- one question — "is this uniquely borrowed?" — was three patterns.
  `preprocess_old_params`, the caller-side `old p` substitution map, the loop
  havoc, and the call-site havoc each listed
  `Array(_, Mut) | ClassRef(_, Mut) | ResRef(_, Mut)`, and a fourth borrowable
  shape would have meant editing all of them.

Worst of all, ownership was not readable off the shape. `Ty::is_affine` had to
distinguish `Array(_, Owned)` from `Array(_, Shared | Mut)` inside one
constructor, which is the same "which constructor did the parser happen to
build" hazard ADR 0065 removed from options.

## Decision

**`Ty::Borrow(Mutability, Box<Ty>)` is the only borrow, and a bare type owns.**
`Ty::ClassRef` and `Ty::ResRef` are deleted; `Ty::Array(Box<Ty>)` carries only
its element. `Mutability` has two cases, `Shared` and `Mut`, because owning is
the *absence* of a borrow rather than a kind of one.

The parser's borrow production stops rebuilding its referent:

```rust
TypeSyntaxKind::Borrow { mutability, referent } => {
    self.check_admits(TypeShape::Borrow, pos, syntax.span)?;
    let referent = self.lower_type(referent, TyPos::BorrowParam)?;
    Ok(Ty::borrow(*mutability, referent))
}
```

### Ownership becomes structural

```rust
pub fn is_affine(&self) -> bool {
    match self {
        Ty::Class(_) | Ty::Res(_) | Ty::Array(_) => true,
        Ty::Option(payload) => payload.is_affine(),
        Ty::Borrow(..) => false,
        Ty::Int(_) | Ty::Bool | Ty::Param(_) | Ty::Record(_)
        | Ty::OptionRaw(_) | Ty::Raw(_) | Ty::RawRecord(_) | Ty::Unit => false,
    }
}
```

**The `Borrow` arm is terminal, and that is the load-bearing line.** Writing
`Ty::Borrow(_, referent) => referent.is_affine()` — a traversal where a gate
belongs — would make `&mut [u64]` and `&Nat` affine; `check::mark_moved` would
then insert the borrow's place into the moved set, and
`interp::drop_owned_params` would free storage the caller still names. The
opposite mistake, dropping `Ty::Array(_)` from the owning list, duplicates an
owner by the other door.

Both mistakes are checked rather than argued.
`ast::affinity_agrees_with_the_ownership_rule` states the rule a second time
over the whole sample battery — and now derives it from the type's *spelling*
rather than from a constructor list, because a second copy is only worth having
if it can be wrong differently. Two copies that both enumerate constructors can
be edited identically-wrong in one sitting and the test still passes.

### Three named accessors replace the constructor patterns

| accessor | question |
|---|---|
| `Ty::binding_mode() -> BindingMode` | owned / shared / unique, for the rules that need three answers |
| `Ty::as_unique_borrow() -> Option<&Ty>` | the `&mut T` question |
| `Ty::referent() -> &Ty` | what a borrow names, for stages whose answer does not depend on binding mode |

`BindingMode { Owned, Shared, Mut }` is *derived*, never stored: it is a
question about a type, and `BindingMode::bind` turns it back into one. That is
what lets the shape-admission battery enumerate modes without any constructor
carrying one.

`as_unique_borrow` is the payoff. The three-constructor triple at
`preprocess_old_params`, at the caller-side `old p` substitution, at the two
`_old_` twins, and at the call-site array havoc all collapse to
`p.ty.is_unique_borrow()`: a unique borrow is the only type through which a
callee can change storage its caller still names, so it is the only one with an
entry-state twin.

`referent()` is the other side. `lean_ty` is blind to binding mode — `[T]`,
`&[T]`, and `&mut [T]` are one `Sable.Seq T`, and a class or resource borrow is
the same structure or view its owner is — so every Lean-type site dispatches on
`ty.referent()` and has one arm per shape instead of two. The LLVM *IR type* is
blind too (`ptr` for either class-borrow mode); the mangled symbol is not, and
`type_code` is the one place that distinguishes them.

### Resource borrows fold too

ADR 0064 said `ResRef` would not fold, "because `resource &K` is spelled with
the `resource` keyword and classified as its own shape, so folding it would
make a shape function disagree with `Parser::admits` about the same spelling."
That is reversed here, and the reason it was safe to reverse is that the
disagreement it feared does not exist: **nothing in the tree computes a
`TypeShape` from a `Ty`.** `TypeShape` is a *syntactic* classification, read off
`TypeSyntaxKind` before any lowering; `resource &K` keeps `TypeShape::Resource`
and keeps being admitted exactly where `S::Resource` is admitted. What folds is
the checked representation underneath it.

Keeping `ResRef` would have cost the thing the fold is for: the unique-borrow
predicate would still have been two patterns rather than one, and
`Ty::is_resource` would still have been a two-constructor question. The one
place the spelling has to reappear is printing, and `Ty::name` handles it in
four lines:

```rust
fn borrow_name(mutability: Mutability, referent: &Ty) -> String {
    let marker = match mutability { Shared => "&", Mut => "&mut " };
    match referent {
        Ty::Res(kind) => format!("resource {marker}{}", kind.name()),
        other => format!("{marker}{}", other.name()),
    }
}
```

`resource &K` puts the marker *after* the keyword; everything else is a prefix
on the referent's own name, so the printing stays compositional and a new
borrowable referent prints without an edit. That compositionality is what makes
the snapshot oracle's empty diff evidence about the whole grammar.

### What was closed by representation is now closed by a rule

This is the point of the change, and it is also its risk. `Ty::Borrow` holds
every referent, so `&u64`, `&record`, `&option<T>`, `&raw<u8>`, `&()`, and
`&&[u64]` all became *representable*. Two protections disappeared with the old
constructors:

1. **The parser's `unrepresentable` backstop in the borrow arm is gone.** There
   is no `other` case left: every lowered referent wraps.
2. **`admitted_shapes_match_their_lowering` stopped pinning `BorrowParam`.** Its
   row read `matches!(shape, S::Class | S::Array)` with the reason "the borrow
   lowering rebinds the referent's mutability, which only a class reference and
   an array carry". That reason evaporated, so `BorrowParam` moves into the
   "lowers to a plain `Ty`, which holds every shape" group.

What replaces both is a **gate with a name**. `check::borrow_referent_ty` is an
allow-list — class, array, resource authority — ending in
`type.borrow_param_unsupported`, which is the name `Parser::admits` already uses
at `TyPos::BorrowParam`. A reader asking "what may `&` be written on" gets one
answer whichever rule answered, exactly as ADR 0063 arranged for array elements
and option payloads. `check::parameter_ty` calls it *before* the payload
traversal, so `&record` is told the borrow rule rather than an inner payload
rule it did not break.

The six `param &mut` cells of `docs/type-matrix.md` therefore stay closed, and
they are now closed twice — by the parser table for what a program can spell,
and by the checker gate for a type that reached it some other way.

### What the later stages answer, and why that is not a hole

`docs/shape-admission.md` records `yes` for `&u64` at `vc type`,
`interp type`, `svm type`, and `svm parameter` — the same `yes` those columns
already record for `&class` and `resource &`. That is not a lost refusal: those
stages ask *their own* questions (does this type have a proof model, an
interpretable value, a machine value), and for a borrow they ask them of the
referent. `&u64`'s proof model is an `Int` binder, and saying so is true.

"Which referents may be borrowed" is a *position* question, and it is answered
where borrows are written — at a parameter — by the two rules above. Inventing a
third and a fourth copy in stages a refused type never reaches would have meant
new diagnostic names that no `.sable` source can produce, which the corpus rule
has no way to cover.

## Consequences

**Sites that changed meaning, and how each was checked.** The mechanical part of
this fold is that `Ty::Array(x, _)` — "an array in any binding mode" — becomes
`ty.as_array()`, while `Ty::Array(x, Mutability::Owned)` becomes the bare
pattern `Ty::Array(x)`. Getting that backwards is silent: an arity change is a
compile error, but `Ty::Array(..)` matches either arity, so a site that meant
"any binding mode" narrows to "owned" without a word from the compiler. Nine
such sites existed — `check::array_elem_ty`, four `locals.get(array)` lookups in
`vcgen`, three in `interp`, plus one each in `llvm` and `svm` — and every one of
them was found by the snapshot oracle, not by a test.

**Ownership rules, each made explicit.**

| rule | where | what it asks now |
|---|---|---|
| move | `check::mark_moved` → `Ty::is_affine` | structural: bare owns, `Ty::Borrow` never |
| drop (parameters) | `interp::drop_owned_params` | `matches!(p.ty, Ty::Class(_) \| Ty::Array(_))` — bare constructors only |
| drop (values) | `interp::drop_place`, `drop_value` | keyed on `RtVal`, untouched by this change |
| place writability | `check` store/expose/borrow, `svm::resolve_array` | `Ty::binding_mode()`, three-way |
| loop havoc | `vcgen` | a shared borrow is filtered out once, before the arms |
| call-site havoc | `vcgen` | `p.ty.as_unique_borrow().and_then(Ty::as_owned_array)` |

Two guards are worth naming because they are what keep a mistake in one of these
from becoming an immediate double free. `interp::drop_owned_params` matches the
bare constructors, and a borrow's runtime value is *the same `Rc`* the caller
holds — so `Ty::Borrow` being a separate constructor is what makes the double
free unwritable rather than merely unwritten. And the interpreter's move/no-move
split is syntactic plus value-shaped, never type-shaped: `source_place` returns
`None` for `ExprKind::Borrow`, so a borrow argument can never clear its source
place regardless of what its type says.

**What verifies the claim.**

- **The snapshot oracle** (`compiler/scripts/type-snapshot.sh`), run against a
  binary built at the pre-fold commit: the Lean half is an **empty diff over
  114,517 lines** — every `corpus/verifies` subject, every mangled declaration
  name, every emitted Lean type. The diagnostic half, 3,485 lines over every
  `corpus/must-fail` subject, is **additions only**: the fourteen lines of the
  one subject added here, with **no line removed or changed**.
- **`docs/type-matrix.md` is byte-identical**, `Open cells: 33/81`.
- **`docs/shape-admission.md` is additions-only**: 43 lines added, 0 removed.
  All 45 previously recorded rows agree **cell for cell** across all 25 gates.
- **The binding-mode battery got stronger and demanded the new rows.**
  `every_distinguished_binding_mode_is_probed` used to range over array element
  types; because `Ty::Borrow` holds every referent, it now ranges over every
  owned sample and asks the stages whether owned, shared, and unique get
  different answers. It named 42 shapes — `&u64` through `&mut option<[[bool]]>`
  — that no sample probed, and each is now a row. Every one of them shows
  `type.borrow_param_unsupported` at `check parameter`. A `&&[u64]` row covers
  `Ty::Borrow` as a *referent*.
- **Corpus subjects that go red if the distinction lapses**, each verified by
  making the lapse and watching it:
  - `corpus/tests/test_borrows_own_nothing.sable` — lending a `Token` three
    times. Changing `drop_owned_params` to look through the borrow makes it
    trap on the invariant the first drop falsified. It also pins that two lends
    are not a use-after-move, and that a `&mut [T]` writes through and composes.
  - `corpus/must-fail/mut_array_call_havoc.sable` — the survey's riskiest site.
    Losing the call-site `&mut` array havoc is *silently unsound*: the callee's
    post is asserted over the pre-call state, the hypothesis set becomes
    inconsistent, and everything is provable. This subject's false
    postcondition goes green under exactly that loss, as does the older
    `stale_state_after_call.sable`, which guards the same rule through an
    owned local. This subject earns its place by reaching the rule through a
    `&mut [T]` *parameter* instead, so it exercises the entry-state and `old`
    machinery the local path never touches. It is the weaker of the two
    fences: it fails by exhausting the automation budget rather than by a
    definitive refusal, which makes it sensitive to that budget and slower
    than a decisive failure would be.
  - `corpus/must-fail/array_double_move_into_fields.sable` (pre-existing) is the
    owner direction: dropping `Ty::Array(_)` from `is_affine` makes it verify.
- **`check::a_borrow_of_an_unborrowable_referent_is_refused_by_name`** pins the
  new gate's name for nine referents in both mutabilities, and pins that class,
  array, and resource stay admitted.
- The full suite plus `lake build` is green, and clippy is at its prior warning
  count.

**What did not change.** `ResKind` stays a sealed enum. `TypeShape` and
`Parser::admits` are untouched — no row moved, and `TyPos::BorrowParam` keeps
its name, its describe text, and its rejection note. The four
`borrow_param_*.sable` subjects and `return_borrow.sable` pass unedited.
Machine semantics are untouched: `Val` and `ValTag` in `lean/Sable/SVM.lean`
have no borrow and no mutability, `svm.rs` reads binding mode only in
validators, and SVM subjects are zero-argument functions — so ADR 0017's
coupling is not triggered and no `corpus/svm-diff/` subject is needed.

## What did not land

`check::option_payload_ty` and `interp::option_value_ty` still return a type,
as ADR 0066 recorded; `option_value_ty` has a reason to, and
`option_payload_ty` is waiting on its callers.

`Ty::Borrow` admits a borrow of a borrow in the representation. `&&[u64]` is a
sample row and is refused at the parameter position by name, but no stage below
that has a rule about nesting borrows, because none needs one yet.
