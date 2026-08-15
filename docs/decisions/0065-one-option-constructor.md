# ADR 0065 — one option constructor: an option owns when its payload owns

**Decided 2026-08-16.** Supersedes the representation half of ADR 0060; its
ownership rules — explicit mutable local, non-consuming `.is_some`, atomic
`.take` (ADR 0061) — are unchanged.

## Context

ADR 0060 gave an owning option its own constructor:

```text
AffineOptionTy := Array(ValueTy)
Ty::AffineOption(AffineOptionTy)
```

The argument for it was precise and, at the time, correct. `Ty::Option`
described a *copyable* value, and every stage relied on that: `.value` is a
non-consuming projection, a declaration copies its initializer, a call
argument copies. Making one payload of `Ty::Option` affine by convention would
have turned every `Ty::Option(_)` pattern in the compiler into an ownership
audit. A separate constructor bought that audit for free — an ordinary
copy-option rule could not *name* an owning option, so it could not reach one.

ADR 0064 made container payloads full types. From that point the protection
was already gone in the representation and only present in the spelling:
`Ty::Option(Box::new(Ty::Array(Box::new(Ty::Bool), Owned)))` was constructible,
printed `option<[bool]>`, and `Ty::is_affine` already answered `true` for it
through `Ty::Option(payload) => payload.is_affine()`. Two constructors named
one shape, and only the parser decided which one a program got. That is the
condition ADR 0064 recorded as remaining work, and it is worse than either
end state: a rule could be written against `Ty::Option` believing it had
excluded owners, while a hand-built or future AST hands it one.

## Decision

**`Ty::Option(Box<Ty>)` is the only option constructor.** `Ty::AffineOption`
and `AffineOptionTy` are deleted. Whether an option owns is *computed*:

```rust
Ty::Option(payload) => payload.is_affine(),
```

`option<[T]>` is parsed by the same production as every other payload —
`lower_option_type` no longer inspects the payload's syntax to pick a family,
and `Ty::Array(_, Mutability::Owned)` under `Ty::Option` is all an owning
option is. `option<raw<R>>` stays `Ty::OptionRaw` because it is one abstract
nullable pointer value rather than an option over a pointer.

What is accepted does not change. `option<[bool]>` remains the only admitted
owning option, and every position that refuses it still refuses it under the
same diagnostic name — but each of those refusals is now an explicit rule
asking an explicit question, rather than a consequence of which constructor
the parser happened to build.

### The question every copy rule asks

```rust
/// The payload of an option whose present case owns storage.
Ty::as_affine_option_payload(&self) -> Option<&Ty>
```

It is one named accessor, on `Ty`, spelled the same way at every site, so
widening the owning family later is one edit rather than a hundred and fifty.
It is a **gate**, not a traversal: one level, no recursion.

**It is deliberately not `payload.is_affine()`,** which is what ADR 0064's
phrasing ("affinity read off the payload") would suggest, and this narrowing
is the load-bearing decision here. `option<class>` has an affine payload too.
It is *not* in the owning family: it is a copyable-family shape that the
copyable payload gate refuses by its own name,
`type.option_payload_unsupported`. Routing the family on `is_affine()` would
move eleven cells of that shape's row in `docs/shape-admission.md` and one
cell of `docs/type-matrix.md` — from the copyable gate's refusal to the
owning gate's — which is a change in which rule a user is told about, for a
shape nothing about this work touches.

So the owning family is read off the payload's **shape**: an owned array. That
is exactly the set `AffineOptionTy::Array(_)` denoted — it carried no
mutability field and had one variant — so every gate answers identically for
every shape, which is the property the two ratchets measure.

The two are not complements, and `no_owning_option_is_admitted_by_the_copyable_option_gate`
pins the invariant that matters instead: **no option that owns is admitted by
`check::option_payload_ty`.** An option is in the owning family, or refused,
never copyable.

### Arm order became load-bearing

With two constructors, a rule could list its option cases in any order. With
one, every dispatch on option shape must put the owning case **first**, or the
copyable arm matches it. This is the single place where the fold is a
behavioural change at each site rather than a rename, and it is why the four
stage type-domain checks (`check::validate_aggregate_ty`,
`vcgen::validate_vc_ty`, `interp::validate_interp_ty`,
`svm::validate_ty_payload`) answer the owning family in a guard *before* their
exhaustive one-level dispatch rather than inside it.

The sharpest instance is not a diagnostic at all. `interp`'s `some(...)`
evaluation chooses the runtime representation from the expression's type:

```rust
Some(option) if option.is_affine_option() => { /* eval_moved -> AffineOptBoolArray */ }
Some(Ty::Option(payload)) => { /* eval -> RtVal::Opt { payload, value } */ }
```

Ordered the other way, `option<[bool]>` builds `RtVal::Opt` holding an
`Rc<RefCell<RtArray>>` from `self.eval` — a *copy* — which `RtVal::clone`
duplicates freely and which `drop_place`, keyed on the value's own
constructor, does not recognise as an owner. That is the double-owner this
whole partition exists to prevent, and it is one arm's position away. It is
reachable today: with the arms swapped, `corpus/tests/test_affine_options.sable`
fails.

Everything below that point is keyed on `RtVal`/`SpecVal` constructors rather
than on `Ty`, so this is the *only* place where a type decision picks a
runtime representation, and fixing it fixes the interpreter and the monitor
snapshot together.

### One Lean type for options

`vcgen::lean_affine_option_ty` is folded into `lean_option_ty`, which is now
an allow-list over the payload: `Bool`, an integer model, and an owned
`[bool]`, which is `Option (Sable.Seq Bool)` — parenthesized, because the
result is one argument. Everything else latches
`internal.vcgen.lean_type_unsupported` as before.

### Newly representable, still unspellable

`AffineOptionTy::Array` carried no `Mutability`, so `Ty::Option(Array(_,
Shared))` and `Ty::Option(Array(_, Mut))` — `option<&[T]>`, `option<&mut [T]>`
— are newly *representable*. They are not newly spellable: `Parser::admits`
does not admit `Borrow` at `TyPos::OptionPayload`. A borrow owns nothing, so
they are not in the owning family; every gate refuses them by name. Both are
added to `docs/shape-admission.md` as samples, which is the point of a battery
that does not go through the parser.

## Consequences

**What replaced the structural protection.** A copy-shaped rule used to be
safe because it could not name an owner. Each one now says so:

| lifecycle stage | what asks |
|---|---|
| declaration | `Stmt::Decl` routes to `check_affine_option_initializer` on the payload, before the arms that build a copyable value |
| assignment | `option.affine_assign` on the destination's payload |
| inferred binding | `option.affine_inferred` on the cached type; a bare read is `option.affine_temporary` |
| every other expression | `check_expr`'s entry fence refuses an owning expected type and an owning cached type, so `infer_expr`'s copy rules never see one |
| argument, return, field, trait, template | `parameter_ty` and `validate_declared_aggregate_payloads` ask before their copyable-option refusals, so the reported rule is the owning one |
| `.value` | refused at the operand, before `option_payload_ty` |
| `.is_some` | classified on the operand's payload, then routed to the owning path |
| ownership engine | unchanged: it already read `Ty::is_affine`, which was already structural |
| interpreter construction | the owning arm is first (above) |
| VC, SVM, LLVM | the same question at each stage's own gates and positions |

**The standing limitation is unchanged.** `Place` has no index path, so an
owner living in an array element cannot be tracked at all.
`check::validate_array_payload` refusing every owning payload by name remains
the load-bearing line (ADR 0064).

**One diagnostic text changed.** `mono`'s escaped-parameter message for
`option<[<T>]>` said "affine-option array element type"; it now says "option
payload type", which is the convention every other nested container already
follows (the outermost position names the message). The diagnostic *name* is
unchanged, so no fence and no ratchet cell moves.

**What verifies the claim.**

- `docs/type-matrix.md` is byte-identical, `Open cells: 33/81`.
- `docs/shape-admission.md` is byte-identical **cell for cell** — the only
  diff is the two added `option<&[bool]>` / `option<&mut [bool]>` rows. Every
  previously probed (shape, gate) pair answers exactly what it answered
  before, across all twenty-six gates.
- The snapshot oracle (`compiler/scripts/type-snapshot.sh`): the Lean half is
  an **empty diff** over 114,517 lines — every `corpus/verifies` subject,
  including every mangled declaration name and every emitted Lean type. The
  diagnostic half, 3,467 lines over every `corpus/must-fail` subject, is
  **additions only**: the eighteen lines of the two subjects added here, with
  no line removed or changed. `Ty::name` is compositional and the fold is
  name-identical, which is what makes that evidence about the whole grammar
  rather than about the shapes some test mentions.
- Three corpus subjects were added for the duplication paths a merged
  constructor makes thinkable: `affine_option_copy_local.sable` (a second
  option bound to the first), `affine_option_copy_inferred.sable` (the same
  copy with no type written — the first subject for `option.affine_temporary`),
  and `corpus/test-fails/affine_option_take_twice.sable`, which traps on the
  second `.take` precisely because the first one moved the only owner out.
  `corpus/tests/test_affine_options.sable` gains a case that mutates the taken
  array and re-asserts the source is empty.
- `ast.rs`'s `affinity_agrees_with_the_ownership_rule` checks `is_affine`
  against the ownership rule written out separately, over the whole sample
  battery.

## What did not land

**The four validate-and-lower conversions survive.** *(Done in ADR 0066.)*
`check::array_payload_ty`, `interp::value_ty`, `svm::array_element_ty`, and
`svm::ordinary_option_payload_ty` still answer "may this sit here" and "what
is the resulting type" in one function, as ADR 0064 recorded. Nothing here
changed them.

**`Ty::Borrow(Mutability, Box<Ty>)` still does not exist.** Mutability is
carried inline by `Ty::Array` and `Ty::ClassRef`, so `&Nat` and `&[u64]`
remain two unrelated shapes in the representation. That fold is what would
make `option<&[bool]>` a borrow under an option rather than a mutability field
under one.
