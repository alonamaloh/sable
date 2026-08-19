# ADR 0064 — one recursive type grammar: container payloads are full types

**Decided 2026-08-15.**

## Context

ADR 0063 gave the parser one recursive type production and one
(shape × position) admissibility table. The checked types it produced were
still three languages, not one:

- `Ty` — the type of everything: parameters, returns, locals, fields;
- `ValueTy` — `Int | Bool | Record | Param`, the *only* thing a container could
  hold, because `Ty::Array` and `Ty::Option` carried a `ValueTy` rather than a
  `Ty`;
- `AffineOptionTy` — `Array(ValueTy)`, the payload of an owning option.

Because a container held `ValueTy`, the shapes `[[u64]]`, `[Box]`,
`[option<u64>]`, and `option<option<u64>>` were not refused by any rule. They
could not be written down at all. Ten cells of `docs/type-matrix.md` were closed
by that arithmetic and by nothing else.

That is the wrong kind of "no". A language should refuse a shape because a
stage has no semantics for it, at a named diagnostic that says which stage and
why — not because the compiler's data structure lacks a variant. The first can
be read in a table and later changed on purpose; the second can only be
discovered by trying to write the code.

The same lossy funnel already exists on the generic path, where
`GenericTy` — a genuinely recursive type with substitution, canonical keys,
structural depth, and nominal visiting — is narrowed to `Ty` through
`GenericTyError::NotV1Integer`. So this is a convergence of two representations
the compiler already has, not a new design.

## Decision

**Container payloads are full types, boxed.** `Ty::Array(Box<Ty>, Mutability)`
and `Ty::Option(Box<Ty>)` hold a `Ty`, as does `AffineOptionTy::Array(Box<Ty>)`.
`ValueTy` is deleted. No position in the compiler narrows a type to a smaller
payload representation on the way into a container, so what a container can hold
stops being a property of the representation and becomes something a rule has to
say.

`Ty` is consequently `Clone` rather than `Copy`. The runtime tags
(`RtArray.payload`, `RtVal::Opt.payload`, `SpecArray.payload`) hold
`Ty::Int(_)` or `Ty::Bool`, which clone without allocating.

This is the representation half of a larger unification. The other half — one
`Borrow` constructor with mutability lifted out of `Array` and `ClassRef`,
`AffineOptionTy` deleted in favour of affinity read off the payload, and the
per-stage validate-and-lower conversions reduced to validators — is **not** in
the tree. It is stated under "What did not land" as remaining work, not as an
accomplished fact.

### The rule this turns on: traversal or gate, never both

A function over `Ty` is either a **traversal** or a **gate**, and confusing the
two is how a migration like this creates a hole.

> A *traversal* answers "visit everything" — `modules::walk_ty`,
> `mono::subst_ty`, `Ty::name`, `Ty::is_concrete`, `Ty::is_affine`,
> `Ty::structural_depth`. It recurses into every `Box<Ty>` child and matches
> exhaustively with no wildcard, so a new constructor is a compile error. A
> missed child is a hole.
>
> A *gate* answers "may this sit here" — `check::array_payload_ty`,
> `check::option_payload_ty`, `vcgen::validate_vc_payload_ty`,
> `interp::validate_interp_array_payload`,
> `interp::validate_interp_option_payload`, `svm::array_element_ty`,
> `svm::ordinary_option_payload_ty`, `Ty::storage_layout`,
> `llvm::require_runtime_type`. It is an allow-list ending in
> `_ => Err(<named diagnostic>)` and **never calls itself**. A gate that
> recurses admits arbitrary nesting.

A third kind sits beside them and is easy to mistake for a gate: a **position
gate** — `check::parameter_ty`, `svm::validate_parameter_ty`,
`vcgen::validate_vc_type_position` — answers "may this type sit *here*", which
is a different question from "may this type exist" and gets a different answer
for the same type. `[bool]` is an admissible local and an inadmissible
parameter in three stages independently. A position gate runs the payload
traversal first and then refuses by position, so deleting either half leaves
the other still answering, which is why both halves are separate columns of
`docs/shape-admission.md`.

The concrete trap: `vcgen::validate_vc_ty` dispatches
`Ty::Array(e, _) => validate_vc_payload_ty(&e, …)`. Making that "recursive" so
it reads `validate_vc_ty(e, …)` would accept `option<option<u64>>` at the VC
preflight, because `Option(Int)` is fine one level down. The one-level dispatch
is the gate; it stays one level.

#### The stage type-domain checks are exhaustive one-level dispatch

Each consuming stage has one entry point that takes a whole `Ty` and hands its
container payload to that stage's gate:
`check::validate_aggregate_ty`, `vcgen::validate_vc_ty`,
`interp::validate_interp_ty`, and `svm::validate_ty_payload`. All four match
**exhaustively with no wildcard**. `check::validate_aggregate_ty` used to end in
`_ => Ok(())`, which is fail-open: a shape nested under a constructor nobody
thought about would be admitted without any gate seeing it. That is the
invariant to test against when a constructor is added — a wildcard in any one of
the four silently exempts that stage.

They are **one-level dispatch, not traversal**. `Ty::Array(p, _)` hands `*p` to
the array gate, `Ty::Option(p)` hands `*p` to the option gate, and every other
constructor is an explicitly listed terminal arm. One level is sufficient
*because the gates they call are atom allow-lists* — they admit only `Int`,
`Bool`, and `Param`, none of which has a child, so there is nothing below for a
deeper pass to inspect. That sufficiency is a property of the gates, not of the
dispatch, and it is the thing that breaks first. Whoever widens a payload gate
to admit a constructor that has a payload of its own must make the four
dispatchers recurse in the same change, or the inner payload gets no gate at
all.

### Not an arena, and not `TyOf<N>`

Interning atoms as `const TyId`s would keep `Ty: Copy` and keep payload sites as
literal patterns. That advantage is measured against constructors this work
converts into payload holes: `Ty::Array`, `Ty::Option`, and
`AffineOptionTy::Array` now match through a `Box`, and the pending `Borrow` step
converts `Ty::ClassRef(c, m)` into `Ty::Borrow(m, t) if matches!(*t,
Ty::Class(_))` as well. What interning leaves behind is a permanent tax — every
payload match goes through a handle resolve, `Debug` is hand-written through
interior mutability, and `Ty == Ty` is correct only if a global invariant
holds — bought against a `Copy` removal that cost twelve hand-written lines.

Parameterizing the grammar by its nominal representation (`TyOf<Name>`, with
`Ty = TyOf<usize>` and `GenericTy = TyOf<String>`) remains the more complete
answer, and its diagnosis is right: the `Ty`/`GenericTy` split is a *phase*
distinction, not a type distinction. The first G3 widening did not require that
refactor because both newly admitted forms are leaves after resolution: an
integer becomes `Ty::Int`, and a direct ordinary class becomes
`Ty::Class(index)`. Reconsider `TyOf<Name>` when recursive/nested type arguments
are admitted or nominal index assignment moves earlier in the pipeline.

### The substitution vector admits only resolved leaves

`mono::subst_ty(&mut Ty, &[ConcreteArg], Span)` recurses through checked
payloads, but each substitution value is either a concrete integer or an
ordinary class name already resolved to its final checked index. A whitelist in
`ClassArgEnv` preserves the independent generic-argument axis: Boolean, record,
array, option, and nested generic-class arguments still fail before a checked
type is built, and integer-only occurrences such as conversion widths reject a
class argument by name.

`Ty::is_affine(Ty::Param(_)) == false` now describes only the retained ADR 0009
integer proof model. It is not a claim about every concrete argument. An owner
instance substitutes `Ty::Class(index)`, receives `ProofReuse::None`, and is
checked independently under the affine arm; the affinity regression pins that
separation.
`mono::concrete_type_args` is the sole producer of both the resolved
substitution vector (`ConcreteArgs::values`) and the source-structural canonical
keys used for instance identity. All-integer requests render from the integer
values for byte-compatible legacy names; owner requests render from the keys,
so program-relative class indices cannot leak into identity or spelling.

### Nominal indices stay program-relative

`Record(usize)`, `Class(usize)`, `RawRecord(usize)`, and
`ResKind::PointsToRecord(usize)` keep indexing `Program`. That is what lets
`Ty::name()` be constructed without a `&Program` in scope, which most of the
compiler's type-printing sites do not have. It is also why `GenericTy` survives
as the pre-resolution spelling of the same grammar: it names nominals by
`String` because indices are not stable until merge and monomorphization finish.

### `Raw(IntTy)` and `RawRecord(usize)` stay split

A `raw<...>` pointee is a width or a nominal record, and nothing else. Merging
them into `Raw(Box<Ty>)` would make the record-field layout rule read
`Ty::Raw(_) => 8/8` and silently admit `raw<u8>` as a record field — a shape
that is not even in the matrix. `record_field_raw_integer.sable` pins the
refusal.

### Internal refusals are named `internal.`

Several converted sites are unreachable from any source program by
construction: they exist so a hand-built AST meets a named error instead of a
panic. A name in the `internal.` namespace is covered by a unit test with a
hand-built AST rather than by a `corpus/must-fail/` subject. Every such name
carries that cover: `internal.vcgen.lean_type_unsupported` and
`internal.vcgen.int_model_unsupported` in
`an_unprovable_payload_latches_a_named_internal_error`,
`internal.vcgen.type_error` in
`a_payload_with_no_proof_semantics_is_refused_by_name`, and
`internal.mono.type_arg_arity` in `mono`'s own tests. The exemption is
conditioned on that cover, so a new `internal.` name without an asserting test
is a gap, not a shortcut.

Its boundary is exact: an `internal.` name must never be reachable from any
`.sable` source. A refusal a program can reach gets a corpus subject like every
other diagnostic. Two names sit just inside that boundary and are named in the
user's vocabulary instead, because a user could see their text if the shape
domain widened; each is covered by a unit test in place of a corpus subject.
`monitor.no_junk_value` is one (see below). `interp.array_payload_mismatch`
(`interp.rs`) is the other: it traps when an element would be stored outside
its array's payload domain, which no checked program can produce, and
`payload_guard_tests::an_array_never_holds_a_value_outside_its_payload` stands
in for the subject.

Unreachability is about the *text a user can see*, not only about the
diagnostic path. The monitor's junk-value refusal is unreachable from source
today, but `sable test` prints its reason verbatim in the skipped list, so it
is named `monitor.no_junk_value` in the user's vocabulary and carries an
actionable message; a unit test still stands in for the corpus subject. No
other `internal.` name can reach that list: `speceval::Unmonitorable` is
constructed only inside `speceval.rs`, and no other reason there is namespaced
`internal.`.

### The LLVM lowering answers with a panic, and stays that way

`llvm::llvm_ty` and `llvm::type_code` end in `unreachable!`. Measured against
the blessed samples they would panic on most of them: they are *lowerings*, not
gates, and they run only on shapes the `require_*` gates already admitted.

They are deliberately not converted into `Result`. The refusal belongs to the
gate, which has the `.sable` span the diagnostic rule requires; a refusal
raised inside the lowering would be a refusal with no span, produced after the
decision was made, at 38 call sites that are string emitters rather than
error-returning passes. Moving the refusal there would make the diagnostic
worse, not better.

What the panic rests on is an implication — *admitted implies lowerable* — and
that is checked instead: `llvm_lowering_is_total_on_admitted_shapes` runs both
lowerings on every sample the backend's gates admit and names the shape if one
has no lowering. Widening a `require_*` gate without teaching the lowering is
then a red test naming the shape, not an aborted compile in front of a user.
The table records the gates' answers, never a panic, because a table that can
bless "panics" as an answer would make the process abort look intended.

### Machine semantics are untouched

This changes no machine semantics. `Val` and `ValTag` in `lean/Sable/SVM.lean`
are unchanged, and `svm::array_element_ty`'s `{concrete Int, Bool}` allow-list
remains the Rust mirror of `Val.tag?`. The coupling ADR 0017 requires — rules,
functional evaluator, agreement proofs, `corpus/svm-diff/` — is not triggered,
and the Lake build plus the SVM differential stay in the gate anyway.

## Consequences

**Representable is not accepted.** The ten cells that were closed by
*representability* are now spellable in `Ty` and closed by a rule with a name
and a span. They are `[u64]`, `[bool]`, `option<u64>`, `option<bool>`,
`option<[bool]>`, and `class` in **array element**, and `option<u64>`,
`option<bool>`, `option<[bool]>`, and `class` in **option payload**. All ten are
refused by **ADR 0063's parser admissibility table** — `Parser::admits` /
`Parser::check_admits` at `TyPos::ArrayElement` and `TyPos::OptionPayload` —
whose rows this work does not change. Its diagnostic name coincides with the checker
gate's name because `TyPos::gate_name()` maps `ArrayElement` to
`type.array_payload_unsupported` and `OptionPayload` to
`type.option_payload_unsupported`, so an `expect-error` fence cannot tell the
two rules apart.

Thirteen `corpus/must-fail` subjects were added, and they split accordingly:

- seven — the five `array_element_*.sable` subjects,
  `option_payload_class.sable`, and `option_payload_option_array.sable` — pin
  the **parser table**, and their comments say so rather than naming a checker
  gate they never reach;
- six — the `record_field_*.sable` subjects — pass the parser table and pin the
  **record layout rule** at `record.field_type`.

So the deliverable holds in the form "blocked by a rule, at a named diagnostic,
in a table someone can read and later decide to change" — but for the container
cells the table is the *parser's*, not a stage gate's. Moving those refusals
down to the stage gates is not required for soundness and is not attempted here:
the stage gates refuse the same shapes when asked directly, which is exactly
what `docs/shape-admission.md` records. Where the parser table deliberately
admits a shape, the stage gate is the only refusal and has its own subjects —
`array_element_record.sable` and `option_payload_record.sable` pin
`check::array_payload_ty` and `check::option_payload_ty`, and
`affine_option_payload.sable` pins `type.affine_option_payload` for
`option<[u64]>`.

`docs/type-matrix.md` reads `Open cells: 33/81` before and after. A cell that
opens as a side effect is a bug, not progress.

**What verifies the claim.** Four gates run at every step:

- the matrix (`cargo test --test type_matrix`) — identical grid, identical
  closing diagnostic per cell;
- the full suite plus `lake build`;
- a snapshot oracle (`compiler/scripts/type-snapshot.sh`) — the generated Lean
  for every `corpus/verifies` subject and the rendered diagnostic for every
  `corpus/must-fail` subject. `Ty::name` is compositional, so every fold in this
  work is name-identical: `Array(ValueTy::Bool, Owned)` and
  `Array(Box(Ty::Bool), Owned)` both print `[bool]`, and
  `AffineOptionTy::Array(ValueTy::Bool)` and
  `AffineOptionTy::Array(Box(Ty::Bool))` both print `option<[bool]>`. The Lean
  half is an empty diff over 114,517 lines, including every mangled declaration
  name, which is what makes the fold a bijection rather than a smoke test. The
  diagnostic half, 3,350 lines over the 280 `corpus/must-fail` subjects that
  predate this change, is not an empty diff: 17 hunks, 34 lines. Every one of
  them is a `= note:` or caret label losing milestone vocabulary, which this
  change also removed. Extracting the subject headers, the `error` lines and
  the `--> file:line:col` spans gives 938 lines that are byte-identical, so no
  diagnostic name, no span, and no subject outcome moved — which is the
  property the oracle is there to establish. The thirteen subjects added here
  have no before-side; their `expect-error` fences are what pins them;
- a shape-admission ratchet — every constructor of `Ty`, plus a nesting battery
  and a binding-mode battery, run through every payload gate, position gate, and
  traversal, with the answer blessed in `docs/shape-admission.md`. This is what
  the matrix cannot do: the matrix probes source programs, so it cannot see a
  gate lost for a shape no source program can spell. Widening the representation
  and silently widening what a stage swallows become the same table diff.

  Three properties make it a ratchet rather than a dump. Every cell is *derived*
  from the stage — a refusal's cell is the name the stage produced, never a
  string the table repeats, so a renamed diagnostic moves a cell. A traversal
  that has no accept/refuse answer (`mono::subst_ty`, `modules::walk_ty`,
  `interp::value_ty`) records what it produced instead of `yes`, so a lost
  recursive arm also moves a cell: substitution is probed with an empty argument
  vector, which turns "did the traversal reach this parameter" into a named
  refusal, and visibility is probed against a program whose class and record
  names are known, which turns "did the traversal reach this nominal" into a
  name in the cell. And the failure report names the first differing
  (shape, gate) pair, because a stale table is only useful if it says which cell
  moved.

  The binding-mode battery is generated rather than listed:
  `every_distinguished_binding_mode_is_probed` asks the stages whether owned,
  shared, and mutable get different answers for each array element type in the
  samples, and requires a sample for every mode that is answered differently.
  A stage that starts distinguishing a mode it used to ignore fails that test
  until the sample exists, rather than silently leaving the new answer
  unwatched.

**What stays non-orthogonal, on purpose.** `ResKind` stays a sealed enum — a
program may not declare a resource (ADR 0024), so authority must never become a
structural shape. `ResRef` does not fold into a borrow constructor:
`resource &K` is spelled with the `resource` keyword and classified as its own
shape, so folding it would make a shape function disagree with `Parser::admits`
about the same spelling. `IntTy::TParam` and `Ty::Param` remain a duality,
normalized on entry: the former is retained only in integer-only syntax
positions, while declaration value types use the latter.

**Depth after substitution.** The parser bounds a spelled type, and `name`,
`is_affine`, `is_concrete`, and the traversals now recurse over a real tree.
`GenericTy::structural_depth` is checked at the mono boundary. On the `Ty` side,
`substitution_never_deepens_a_checked_type` pins that `subst_ty` preserves
`Ty::structural_depth`, because a parameter is a leaf and so are both admitted
replacement forms, a concrete integer and a resolved ordinary class. No second
bound after expansion is needed while arguments remain direct leaves; that test
is what fails if a recursive argument shape is admitted without a new bound.

**What no representation change buys.** `Place` is a root plus a field path with
no index component, and affinity, initialization, brands, and `#[must_consume]`
are all keyed by `Place`. An owning array element therefore cannot be tracked at
all — `xs[i]` on a `[Box]` would duplicate an owner with no diagnostic. Until
`Place` gains an index path, `check::array_payload_ty` refusing every affine
payload by name is the load-bearing line, not the parser table.

## What did not land

Three pieces of the plan this decision was drawn from are **not** in the tree.
They are recorded here as remaining work.

**1. `Ty::Borrow(Mutability, Box<Ty>)` does not exist.** *(Done in ADR 0067,
which also reverses the `ResRef` sentence under "What stays non-orthogonal, on
purpose": nothing computes a `TypeShape` from a `Ty`, so folding the checked
representation cannot make a shape function disagree with `Parser::admits`.)*
Mutability is still
carried inline by the constructor that can be borrowed: `Ty::Array(Box<Ty>,
Mutability)` and `Ty::ClassRef(usize, Mutability)`. So `&Nat` and `&[u64]` are
two unrelated shapes in the representation even though they are one shape in the
grammar, and any future borrowable constructor has to add its own `Mutability`
field rather than inherit one. Lifting it out means reworking roughly 89
`ClassRef` sites plus every `Ty::Array(_, m)` pattern. `Ty::name` already prints
`&[t]` for `Array(t, Shared)`, so the snapshot oracle covers the fold when it
happens.

**2. `AffineOptionTy` is not deleted.** *(Done in ADR 0065, which also
narrows the phrasing below: the owning family is read off the payload's
shape — an owned array — not off `payload.is_affine()`, which would pull
`option<class>` in and move a matrix cell.)* `Ty::AffineOption(AffineOptionTy)`
(ADR 0060) is still a constructor separate from `Ty::Option`, with its own
`name`, `is_concrete`, and substitution arm, and 154 sites across the
compiler ask for it by constructor. The mechanism that would replace it is
already present and correct: `Ty::is_affine` reads
`Ty::Option(payload) => payload.is_affine()`, so an option over an owned array
would classify as affine with no separate family. What remains is turning those
154 sites into questions about the payload,
which is a behavioural change at each one rather than a rename — a site that
today means "the owning family" and a site that today means "not the copyable
family" stop coinciding the moment the families merge.

**3. Four validate-and-lower conversions survive.** *(Done in ADR 0066: all
four are pure validators and their callers use the payload they hold.
`interp::option_value_ty` does not join them — its `option<raw<Record>>` arm
is a real lowering, and it is kept and named.)* The plan's decisive
consequence was deleting the five per-stage `ValueTy → Ty` conversions and
leaving a pure validator in each stage. Only `vcgen::vc_option_payload_ty` is
gone. Four remain, now typed over `Ty` rather than `ValueTy`:

| function | file | signature |
|---|---|---|
| `check::array_payload_ty` | `compiler/src/check.rs` | `(Ty, Span) -> CResult<Ty>` |
| `interp::value_ty` | `compiler/src/interp.rs` | `(&Ty) -> Option<Ty>` |
| `svm::array_element_ty` | `compiler/src/svm.rs` | `(Ty, &str) -> Result<Ty, String>` |
| `svm::ordinary_option_payload_ty` | `compiler/src/svm.rs` | `(Ty) -> Result<Ty, String>` |

Each still answers "may this sit here" and "what is the resulting type" in one
function. Fusing them is defensible where they stand — a separate lowering
beside the validator is a second entry point nothing guards — but it is not the
pure validator the plan described. What this change removed is the *lossy*
arithmetic inside them, not the conversions themselves: they no longer narrow a
type to a smaller representation, they return the payload type unchanged.
Turning them into `(Ty) -> Result<(), _>` means every caller stops asking for a
narrowed type and reuses the one it already holds; `check::option_payload_ty`
and `interp::option_value_ty` join the list once their callers do.
