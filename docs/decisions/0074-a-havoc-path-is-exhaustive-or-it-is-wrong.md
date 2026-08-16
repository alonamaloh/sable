# ADR 0074 — a havoc path is exhaustive or it is wrong

**Decided 2026-08-16.** Closes two false-proof holes, one fail-open panic
family, one wrong-layer error, and one landmine — five audited defects whose
common cause was the same arrangement: the answer to "what is a fresh symbolic
state for a value of this type" existed in several divergent copies, each a
`match` over `Ty` with a wildcard, and every wildcard silently kept a stale
symbolic chain.

## Context

VC generation replaces mutated symbolic state with fresh binders at three
kinds of site: parameter entry (a caller's arbitrary-but-well-typed value),
the call-site havoc for `&mut` arguments (the callee wrote through them,
within its posts), and the loop-head havoc (the body wrote, within its
invariants). All three answer one question — a fresh binder of the type's
Lean shape, plus the facts every checked inhabitant satisfies — but each
answered it with its own dispatch over `Ty`, and the dispatches did not
agree on which types they covered.

Where a havoc dispatch missed a type, the failure mode was not a diagnostic.
The `_ => {}` arm *kept the pre-mutation chain in the environment*, so the
prover reasoned about post-loop or post-call state using pre-loop or pre-call
values. That is a false-proof machine: `sable check` said `fully verified`
about contracts `sable test` refutes. It is the exact defect class ADR 0072
closed for borrow locals, reappearing wherever a havoc dispatch had a hole,
and no gate watched it because a wildcard arm is invisible to the compiler
and to the admission tables alike: the type is admitted everywhere, and the
hole is in what a stage *means*, not in what it admits.

The audit that motivated this change confirmed five defects, all in this
file, all reproducible:

- **D1 (false proof).** A class-valued field reassigned in an init loop was
  never havocked: the init-branch loop havoc versioned `self.<field>` keys
  through a match covering only arrays, integers, template parameters, and
  booleans. `Class`- and `Res`-valued fields fell to `_ => {}`, so the
  pre-loop constructor chain survived the loop and a post pinning the field
  to its pre-loop value proved — the pinned reproducer proves 9/9 — while the program
  refuted it at run time.
- **D2 (false proof).** A `raw<u8>` local mutated in a loop was never
  havocked: the generic loop-havoc arm table covered every shape *except*
  raw pointers. A program that walks a pointer one past the end of a span in
  a loop and then loads through it was proved trap-free and traps.
- **D3 (fail-open panic).** `&mut self.<field>` resource borrows — spellable
  in a destructor, ADR 0029 — reached sealed resource-op arms that
  destructure `ExprKind::Borrow { array, .. }` *ignoring `field`*. The
  arms key their fresh-state write-back by the borrow's root name, so a
  field borrow would overwrite the whole object with a view; `split_off`
  happened to panic at an `unreachable!` first, and the arms that did not
  panic clobbered `self`.
- **D4 (wrong layer).** A destructor whose loop assigns a field: the loop
  havoc's `self` branch handled `Cctx::Method` and `Cctx::Init` but not
  `Cctx::Deinit`, so the `self` binder was stale-renamed with nothing fresh
  rebound, and the user saw a generated-Lean identifier error about a
  construct the language supports.
- **D5 (landmine).** The plain-call arm havocked `&mut [T]` arguments in its
  own private loop — with a comment saying omitting it proves false posts —
  and the method-call arm had no equivalent. Unreachable today only because
  `type.member_param` refuses every member parameter that is not an integer,
  a class, a resource, or (inits) a shared array borrow; that gate had zero
  corpus subjects, so widening it would have opened D5 silently.

## Decision

**Fresh-state-for-a-type exists once.** `Generator::fresh_state_for(ty,
binder, base, len)` is the single answer: it pushes one binder of the type's
Lean shape, pushes the facts every checked inhabitant of the type satisfies
(integer ranges, option payload ranges over `.value`, record `wf`, class
field facts plus the class invariant, resource-view well-formedness, array
element ranges), and returns the environment value that holds the binder.
Parameter entry, `havoc_mut_borrow_args` (now the *only* call-site havoc —
ordinary calls, method calls, and constructor calls all use it, which is what
defuses D5), the loop-head havoc's generic branch, and the init-branch field
havoc all call it. Site policy stays at the site: binder *names* (`_old_p`,
`_selfN_f`, `_arrN`, source-hinted symbols), the array length *relation*
(entry states bound `0 ≤ len ≤ u64.max`; havoc preserves the replaced
state's length, since stores are the only array mutation), and binding-mode
filters (a shared borrow is never a store target, so it is never havocked).

**A havoc path is exhaustive or it is wrong.** `fresh_state_for` matches
`Ty` with no wildcard, so adding a `Ty` constructor is a compile error in
every havoc path at once. A shape with no fresh-state story — `()` and a
borrow of a borrow, today — latches the fail-closed `refuse_vc_type` refusal
(the ADR 0071/0072 shape): generation fails by name instead of publishing a
theorem over a stale chain. The same rule applies to the havoc paths' edges:
a havocked name with an environment entry but no declared type refuses
(`internal.vcgen.havoc_untyped_name`); a composite `self.<field>` key whose
chain depends on a dead body-local refuses (`internal.vcgen.havoc_stale_chain`)
— while one whose chain survives is rewritten to the stale binder names,
because its place was not assigned and the pre-loop value is intact; and a
unique borrow at a loop head without an entry state still refuses (ADR 0072).

Each defect's specific correction, under that rule:

- **D1/D2.** The init-branch field havoc versions *every* tracked field, and
  the generic loop-havoc branch covers every type, both through
  `fresh_state_for`. A class-valued field comes back with its field facts
  and class invariant (class values only arise from init/method exits); a
  raw pointer comes back *unconstrained* — whatever relates it to a span
  after the loop must be a loop invariant, which is the model's honest
  answer. Both audit reproducers flipped from `fully verified` to unproved
  obligations, and their sound rewrites (loop invariants carrying the field
  value / the pointer position) verify and run.
- **D3.** Every sealed raw/resource-op arm reads its write-back root through
  one helper, `sealed_borrow_root`, which refuses `field: Some(_)` instead
  of ignoring it. The user-facing refusal is the checker's, named and
  spanned: `resource.field_borrow_op`, raised for any field borrow reaching
  a sealed raw, resource, or device operation, with the rewrite in the note
  (move the field into a local binding first — a destructor may move fields
  out). The vcgen helper is the fail-closed second layer, `internal.`-latched.
- **D4.** `Cctx::Deinit` joins `Cctx::Method` in the loop havoc's `self`
  branch: a fresh `_self_loop` state with field facts and *no* class
  invariant — the entry invariant is not re-established once the destructor
  body has run (ADR 0029), so loop invariants carry the working facts, the
  same rule the mid-method state already follows.
- **D5.** The array havoc lives in `havoc_mut_borrow_args`, so member calls
  inherited it; and `type.member_param` gained one `corpus/must-fail/`
  subject per refused family (`bool`, `&mut [T]`, method-position `&[T]`,
  option, record, raw pointer), so widening the gate breaks a fence and the
  widener meets the havoc question deliberately.

One fact-side wildcard was closed in the same change because D3's sound
rewrite exposed it: `push_class_state_facts` now states resource-view
well-formedness for resource fields (every view a field can hold carried it
at the binding site the value came from) and lists its remaining no-fact
shapes explicitly.

## Consequences

- `resource.field_borrow_op` is a named, spanned checker refusal;
  `corpus/must-fail/deinit_field_borrow_split_off.sable` pins the audit
  reproducer, and `corpus/verifies/deinit_split_off_local.sable` (with its
  dynamic twin) pins the rewrite the note prescribes.
- The false-proof reproducers are corpus subjects in both directions:
  `must-fail/init_loop_class_field_stale` and `must-fail/raw_loop_stale_pointer`
  pin the refusals; `test-fails/init_loop_class_field_stale` and
  `test-fails/raw_loop_pointer_off_end` pin the run-time refutations of the
  same contracts; `verifies/init_loop_class_field`, `verifies/raw_loop_pointer`,
  and `verifies/deinit_loop_field` (each with a `corpus/tests/` twin) pin the
  sound forms. The proof answer and the run answer agree in both directions —
  the differential pair is the only check that has caught this defect class,
  and every subject here keeps both halves.
- Internal refusals added by the exhaustiveness rule
  (`internal.vcgen.fresh_state_unsupported`, `.sealed_field_borrow`,
  `.sealed_borrow_shape`, `.mut_borrow_arg_shape`, `.mut_borrow_arg_state`,
  `.havoc_untyped_name`, `.havoc_stale_chain`) are each pinned by an
  asserting unit test, since no source program can reach them.
- Fresh states carry slightly *more* than before where the copies had
  drifted: a loop-havocked option regains its payload range fact (parameter
  entry always had it), and class states with resource fields gain view
  well-formedness. Both are facts every checked inhabitant satisfies;
  nothing that verified before stops verifying, and no admission moves:
  neither `docs/type-matrix.md` nor `docs/shape-admission.md` moves an
  existing cell (both grow columns in the same tree for other work).
- The call-*return* position is the fourth place a fresh state is built,
  and it is unified only in substance, not in code. Its binder matches now
  cover every returnable shape (a nullable record pointer binds
  `Option Sable.RawPtr`; the residue latches
  `internal.vcgen.call_return_unsupported` instead of aborting), and an
  integer-payload option return carries the same `.value` range fact
  `fresh_state_for` gives every other fresh option. It cannot simply call
  `fresh_state_for`, because a returned `Bool` is deliberately a `Prop`
  binder — the logic's `result` is a proposition — where every other fresh
  Boolean state is a `Bool` with a coerced reading. Folding the remaining
  duplication means deciding that representation question, not moving code.
- The member-call arms now substitute `_old_p` for *every* unique-borrow
  argument rather than a class/resource allow-list, so `old p` is defined
  for whatever a unique borrow may someday name there, by the same
  one-question rule as ADR 0067's accessors.
