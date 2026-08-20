# Soundness incident ledger

This is the audit ledger for defects at Sable's semantic boundaries. It is a
record of evidence, not a claim that every compiler bug is a soundness bug and
not a substitute for the future source-to-SVM soundness theorem. The snapshot
below covers repository history through `9af008e` on 2026-08-20.

## Method

An incident is one implementation defect or one recurring rule omission. A
single defect may have several witnesses; those witnesses remain in one record
instead of inflating the count. Follow-up holes are folded into an earlier
record only when the history identifies the same rule and sink. Ordinary
diagnostic, performance, parser-recovery, and proof-automation bugs are out of
scope unless they admitted a bad program, changed the proposition being
checked, crashed after an admitted semantic boundary, or invalidated an
evidence channel.

The evidence classes are deliberately unequal:

- **Confirmed verified-false**: Lean accepted the generated obligations for a
  concrete program and the repository records a contradictory interpreter or
  monitor result, or an execution that reaches a state the proved claim rules
  out.
- **Accepted-invalid**: the checker accepted a forbidden alias, use-after-move,
  authority duplication, or unchecked body. The history does not contain a
  concrete verified-false/runtime counterexample, so this is not promoted to
  the first class.
- **Fail-open ICE**: ordinary source passed an admission gate and reached an
  `unreachable!`, panic, or equivalent internal failure instead of a named
  refusal.
- **Runtime/codegen divergence**: the proof claim was not shown false, but two
  operational or monitoring consumers disagreed or one silently skipped the
  behavior it was meant to observe.
- **Pre-merge near miss**: an adversarial probe, snapshot, or feature fixture
  caught the defect while the affected shape was still unadmitted or before a
  broken refactor was committed. It is useful evidence about discovery, but it
  is not counted as exposure.

“Exposed on main” means a vulnerable revision is an ancestor of the current
`main` history. It does **not** mean a tagged release or downstream user was
affected; this repository has no tags in the audited range. Where the first
reachable revision cannot be proved from history, the ledger says so rather
than guessing.

The current certificate boundary matters when reading the final field in each
record. ADRs 0087–0088 certify selected explicit unique-borrow call write-back;
ADR 0093 additionally certifies structural local/direct-field slot take and put
write-back. ADR 0094 separately certifies the alias-safety decision for a
closed checker-recorded receiver-first, left-to-right argument schedule. Its
typed-AST/ownership-record extraction remains trusted Rust provenance. The
checker-authored ownership plan and retained control plan have exact fail-closed
consumers, but are trusted Rust data, not certificates. The local SVM move
frame theorem proves one machine step, not source translation.

## Summary

The count is ten confirmed verified-false root causes, eight accepted-invalid
families, three runtime/monitoring divergences, three fail-open ICE families,
and ten pre-merge or pre-admission near misses.

| ID | Evidence class | Fixed/discovered | Exposed on main | Root-cause family |
|---|---|---|---|---|
| VF-01 | Confirmed verified-false | `ffd0663`, 2026-08-09 | yes | stale call state |
| VF-02 | Confirmed verified-false | `b57f64c`, 2026-08-09 | yes | stale loop state |
| VF-03 | Confirmed verified-false | `9b8841d`, 2026-08-11 | yes | alias splitting |
| VF-04 | Confirmed verified-false | `cea4ce2`, 2026-08-11 | yes | incomplete mutation discovery |
| VF-05 | Confirmed verified-false, with runtime and authority consequences | `faf1ccf`, 2026-08-11; recurrence `9a4575e`, 2026-08-13 | yes | fragmented ownership transfer |
| VF-06 | Confirmed verified-false | `ca634414`, 2026-08-16 | yes | persistent local alias |
| VF-07 | Confirmed verified-false | `b0f6851`, 2026-08-17 | yes | fail-open havoc dispatch |
| VF-08 | Confirmed verified-false | `1dd9b40` / `c63300c`, 2026-08-18 | yes | borrow plus move in one call |
| VF-09 | Confirmed verified-false | `4b4f93d`, 2026-08-20 | yes at `7957ad0`; no tagged release | pending-loan argument timing |
| VF-10 | Confirmed verified-false; source confined, dependency audit open | confirmed on `77bdf49`; status mitigation `a2d0adc`; warning/cache mitigation `9af008e`; source-confinement mitigation `94c5113`, 2026-08-20; compiled declaration/axiom audit open | yes at `77bdf49`; no tagged release | unauthenticated proof ingress |
| AI-01 | Accepted-invalid | `fa92e12`, 2026-08-11 | yes | borrow-after-move |
| AI-02 | Accepted-invalid/model mismatch | `842d1af`, 2026-08-16 | yes | owner visible during exposure |
| AI-03 | Accepted-invalid | `a7969ec` / `c46ba94` / `3251c23`, 2026-08-12 | yes | incomplete per-place ownership state |
| AI-04 | Accepted-invalid | `c46ba94`, 2026-08-12 | yes | generic-template checking parity |
| AI-05 | Accepted-invalid | `f1b6317`, 2026-08-19 | yes | implicit receiver liveness |
| AI-06 | Accepted-invalid | `faf1ccf`, 2026-08-11 | yes | minting authority outside affine state |
| AI-07 | Accepted-invalid | `c46ba94`, 2026-08-12 | yes | extern return blacklist |
| AI-08 | Accepted-invalid | `4b4f93d`, 2026-08-20 | yes at `7957ad0`; no tagged release | sealed-operation pending loan plus nested move |
| RD-01 | Runtime monitoring gap | `b57f64c`, 2026-08-09 | yes | skipped projection semantics |
| RD-02 | Runtime monitoring grammar divergence | `67a77dc`, 2026-08-10 | yes | precedence disagreement |
| RD-03 | Runtime/checker scope divergence | `a7969ec`, 2026-08-12 | yes | duplicated scope semantics |
| ICE-01 | Fail-open ICE plus proof-accounting gap | `595e799`, 2026-08-11 | yes | duplicated member-call argument handling |
| ICE-02 | Fail-open ICE family | `faf1ccf`, 2026-08-11 | yes | missing ownership-sink arms |
| ICE-03 | Fail-open ICE | `4b4f93d`, 2026-08-20 | yes at `7957ad0`; no tagged release | trait proof-domain admission mismatch |
| NM-01 | Pre-merge accepted-invalid near miss | `d8e875c`, 2026-08-11 | no known exposure | repeated resource argument |
| NM-02 | Pre-merge admission near misses | `9f1f1bc`, 2026-08-11 | no known exposure | storage container and projection assumptions |
| NM-03 | Pre-merge wrong-term/ICE near miss | `59f3fd0`, 2026-08-17 | no admitted affected shape | wildcard field-state dispatch |
| NM-04 | Pre-merge dropped-obligation near miss | `b0964eb`, 2026-08-16 | no broken refactor committed | representation-fold omissions |
| NM-05 | Pre-native layout near miss | `992437d`, 2026-08-12 | statically admitted, not executable as bytes | incomplete alignment rule |
| NM-06 | Pre-merge evaluation-order near miss | `fe72c55`, 2026-08-19 | no known exposure | slot-put traversal order |
| NM-07 | Pre-merge symbolic-state near miss | `fe72c55`, 2026-08-19 | no known exposure | initializer field-state identity |
| NM-08 | Pre-merge verified-false near miss | `fe72c55`, 2026-08-19 | no known exposure | stale slot-length fact |
| NM-09 | Pre-merge monitor/evidence near miss | `ddb3c67`, 2026-08-19 | no known exposure | runtime snapshot aliasing |
| NM-10 | Pre-merge assurance near miss | `7d054cc`, 2026-08-19 | no known exposure | circular certificate claim |

No confirmed post-admission interpreter-versus-native `-O0`/`-O2` mismatch is
recorded in this interval. The native differential pins the admitted subset
across the interpreter and Clang `-O0`/`-O2`. The repository's injected
wrong-lowering evidence belongs to the Lean-SVM differential, not the native
harness; neither result is rewritten here as an incident.

## Confirmed verified-false incidents

### VF-01 — mutable-array call state was not havocked

- **Window and exposure:** contracted array calls landed in `0f917bf`; the bug
  was fixed in `ffd0663` nineteen minutes later. Both revisions are in main's
  ancestry.
- **Witness and false claim:** `zero_out(&mut b)` writes zeros, but the caller's
  `post result = 5` verified because the pre-call all-fives state remained in
  scope. The commit records that the caller verified vacuously from
  inconsistent hypotheses.
- **Root cause and structural fix:** one block of the call encoding was lost in
  a failed multi-part patch. Mutable arguments now receive fresh post-call
  state with preserved length, element facts, and instantiated callee posts.
- **Regression and discovery:**
  [`stale_state_after_call.sable`](../corpus/must-fail/stale_state_after_call.sable)
  fails specifically at `caller.post`. A quicksort benchmark agent, not the
  then-existing corpus, found the defect.
- **Certificate coverage now:** partial. The ADR 0087 certificate checks the
  observed fresh write-back for an admitted explicit unique-borrow call, but
  Rust remains trusted to identify the call, place, and fresh term.

### VF-02 — an owned array kept its pre-loop symbolic state

- **Window and exposure:** owned local arrays were present by the M5 class
  slice; `b57f64c` found and fixed the omission while adding generic `Vec<T>`.
- **Witness and false claim:** a loop fills an all-fives local array with zeros,
  yet `post result = 5` verified because the owned local was absent from the
  loop havoc set.
- **Root cause and structural fix:** loop mutation handling covered borrowed
  arrays but not the owned-local spelling. Owned arrays now enter loop havoc,
  retaining only sound length and element-domain facts.
- **Regression and discovery:**
  [`owned_loop_stale.sable`](../corpus/must-fail/owned_loop_stale.sable). The
  `Vec<T>` benchmark forced the missing composition.
- **Certificate coverage now:** none. The checker-authored loop mutation plan
  and per-callable reconciliation make consumer omissions loud, but the
  source-to-plan mutation set remains trusted.

### VF-03 — overlapping mutable and shared call borrows

- **Window and exposure:** the overlap was possible from `0f917bf` until
  `9b8841d`.
- **Witness and false claim:** `shift(&mut x, &x)` verified a caller returning
  `3`; `sable test` returned `9`. VCgen gave the unique loan fresh state while
  retaining the shared loan's pre-call state, treating one array as two.
- **Root cause and structural fix:** the call checker had names and borrow
  forms, not a common storage identity. `Place` now represents root plus field
  path, and a mutable loan may not overlap any other loan in the call; a
  mutable method receiver participates in the same check.
- **Regression and discovery:**
  [`borrow_conflict.sable`](../corpus/must-fail/borrow_conflict.sable) and
  [`borrow_conflict_field.sable`](../corpus/must-fail/borrow_conflict_field.sable).
  The defect was found while scoping the place engine for resource work.
- **Certificate coverage now:** partial after ADR 0094. The closed recorded
  argument schedule rejects overlapping unique/shared loans, but typed-AST and
  ownership-record extraction remain trusted provenance. A call write-back
  certificate separately validates the selected post-state.

### VF-04 — a mutating method call hidden in an initializer escaped loop havoc

- **Window and exposure:** class methods and loops predated the fix; `cea4ce2`
  closed the hole on 2026-08-11.
- **Witness and false claim:** `while (...) { u64 seen = c.bump(); ... }` left
  `c` at its pre-loop symbolic value. `post result = 0` verified although the
  function returned `3`.
- **Root cause and structural fix:** `collect_assigned` scanned declaration
  initializers incompletely and recognized a mutable receiver only when its
  call was a standalone statement. Both declaration forms now use one
  expression walk with resolved receiver mutability.
- **Regression and discovery:**
  [`loop_stale_class.sable`](../corpus/must-fail/loop_stale_class.sable), with
  the positive `count_to_three` path in
  [`bounded_stack.sable`](../corpus/verifies/bounded_stack.sable). The place
  work's adversarial safe-side review found it.
- **Certificate coverage now:** none. C0 moved loop mutation authority into the
  checked plan, but no certificate proves the checker discovered every source
  mutation.

### VF-05 — ownership transfer was six inconsistent operations

- **Window and exposure:** the affected move forms accumulated through the
  class/resource/destructor rungs and were unified by `faf1ccf`. A special
  array-field path still omitted the moved-source guard and was closed by
  `9a4575e`; this is recorded here as a recurrence, not a second incident.
- **Witness and false claim:** moving array `nb` into `self.buf`, then writing
  `nb[0] = 99`, left the provable `post self.buf.get 0 = 7` false. The
  recurrence moved one array into two fields, mutated `left`, and made the
  provable post over `right` false. Other symptoms of the same fragmented rule
  included duplicated resource authority, returning a resource field while
  retaining the owner, wrong replacement destruction, and clone-based runtime
  moves.
- **Root cause and structural fix:** declarations, assignments, field
  assignments, call/member arguments, and returns each implemented a partial
  idea of “move.” The checker now has one `transfer`; the interpreter has one
  `eval_moved` over `take_place`/`drop_place`; fields must be restored outside
  destruction; replacements and temporaries have retained cleanup actions.
- **Regression and discovery:**
  [`array_move_into_field.sable`](../corpus/must-fail/array_move_into_field.sable),
  [`array_double_move_into_fields.sable`](../corpus/must-fail/array_double_move_into_fields.sable),
  the sink guards introduced with `faf1ccf`, and the two-sided exact-once
  evidence in [`test_ownership.sable`](../corpus/tests/test_ownership.sable)
  plus [`deinit_runs.sable`](../corpus/test-fails/deinit_runs.sable). An
  external review of destruction semantics prompted the systematic sweep; a
  later native-lifetime audit found the recurrence.
- **Certificate coverage now:** no general source-transfer certificate.
  `CheckedOwnershipPlan` and retained assignment/drop actions reconcile exact
  consumers, while the local SVM frame theorem proves only its bounded machine
  move step.

### VF-06 — a borrow bound to a local became a persistent alias

- **Window and exposure:** the history says the hole predated `ca634414` and
  reached every payload; it does not identify one exact introducing commit.
- **Witness and false claim:** after `var view = &mut a`, writing
  `view[0] = true` left the proof environment's `a` unchanged, so `post
  ¬result` verified while the run returned true.
- **Root cause and structural fix:** name-keyed proof state could not resolve a
  write through a long-lived loan alias back to its owner. Sable now refuses a
  borrow as a local binding; borrows are written where they are consumed as
  call arguments or exposure bindings.
- **Regression and discovery:** the payload/binding-mode battery beginning at
  [`borrow_local_bool_array.sable`](../corpus/must-fail/borrow_local_bool_array.sable)
  and the dynamic counterexample
  [`borrow_argument_aliases_the_owner.sable`](../corpus/test-fails/borrow_argument_aliases_the_owner.sable).
  An adversarial review found that the corpus's only prior borrow local lived
  in an unrelated refusal.
- **Certificate coverage now:** none. The present rule is a checker fence, not
  a certified alias model.

### VF-07 — wildcard havoc silently retained states for new types

- **Window and exposure:** type growth made the wildcard omissions reachable;
  `b0f6851` found and fixed both witnesses on 2026-08-17.
- **Witness and false claim:** an initializer loop replacing a class-valued
  field proved its pre-loop value; a raw pointer advanced to one-past-end in a
  loop nevertheless retained the pre-loop bounds proof and the proved-trap-free
  program trapped.
- **Root cause and structural fix:** several hand-enumerated havoc tables had
  wildcard arms. One exhaustive `fresh_state_for` now serves parameter entry,
  call havoc, and both loop-havoc paths; unsupported shapes latch a named
  refusal.
- **Regression and discovery:**
  [`init_loop_class_field_stale.sable`](../corpus/must-fail/init_loop_class_field_stale.sable),
  [`raw_loop_stale_pointer.sable`](../corpus/must-fail/raw_loop_stale_pointer.sable),
  their dynamic twins, the full loop-type battery, and the `same-lean` pairs in
  [`corpus/pairs`](../corpus/pairs/). A deliberate audit, not ordinary corpus
  execution, found the defect.
- **Certificate coverage now:** none for fresh-state construction or loop
  mutation discovery. Exhaustive Rust dispatch, the checked plan, and the
  metamorphic pairs are engineering controls.

### VF-08 — one call could both lend and move the same owner

- **Window and exposure:** the class route existed with ADR 0030's by-value
  class move sink. `d26c1d7` added the owned-array route. `1dd9b40` then found
  and fixed only the bare-array spelling, explicitly but incorrectly recording
  the class case as non-exploitable. Sixteen minutes later, `c63300c` found the
  nested-array and class counterexamples and replaced the syntax guard with the
  semantic rule.
- **Witness and false claim:** `both(&mut a, a)` returned `7` under a verified
  `post result = 0`; `both(&mut a, dup(a))` and the class-valued
  `both(&mut b, b)` similarly returned `99` under a verified zero claim.
- **Root cause and structural fix:** borrow conflict checking collected only
  borrow-shaped arguments, while moves were detected by spelling. Arguments
  are transferred first; the final conflict rule asks the checker's semantic
  moved set whether a borrowed `Place` was handed away, covering nested moves,
  receivers, and every affine type.
- **Regression and discovery:** the four files beginning with
  [`borrow_moved_in_call.sable`](../corpus/must-fail/borrow_moved_in_call.sable).
  The base array case was found adjacent to owned-array parameter admission;
  adversarial review found the nested and class counterexamples and invalidated
  an earlier hand argument that the class case was safe.
- **Certificate coverage now:** partial after ADR 0094. The closed recorded
  argument schedule rejects a move overlapping a pending loan, but extraction
  of the move and loan records from the source remains trusted Rust provenance.

### VF-09 — an earlier pending shared loan survived a later nested mutation

- **Window and exposure:** the exact introducing commit is not yet attributed;
  the defect became possible once class loans and nested call effects
  coexisted. The generated witness demonstrates that published main revision
  `7957ad0` is vulnerable. `4b4f93d` fixed it on 2026-08-20. No tag exists in
  the audited history.
- **Witness and false claim:**
  `observe(&item, set_nine(&mut item))` first creates the outer shared loan,
  then the later argument mutates the same object through a nested unique
  call. Execution returns `9`, while Lean accepted `post result = 1`; the
  interpreter's monitor independently rejects that post.
- **Root cause:** call conflict checking compared the outer call's direct
  argument effects but did not compare the state reserved by an earlier loan
  argument with mutations nested inside a later argument. VCgen could
  consequently instantiate the outer shared contract from the pre-mutation
  symbolic state. This is not VF-08's borrow-plus-move defect: no owner moves,
  and argument evaluation order is the missing dimension.
- **Structural fix and regression:** `4b4f93d` defines a left-to-right pending
  callee reservation. Once an argument or receiver creates a loan, the checker
  rejects later overlapping mutations from checker-authored nested call,
  sealed-operation, slot, option, and exposure effects; a completed earlier
  mutation or transient read remains legal. The focused regression is
  `nested_unique_argument_mutation_conflicts_with_pending_outer_state` in
  [`ownership_adversarial.rs`](../compiler/tests/ownership_adversarial.rs),
  with the direct refusal
  [`borrow_conflict_nested_mutation.sable`](../corpus/must-fail/borrow_conflict_nested_mutation.sable)
  and reverse-order positive control
  [`nested_mutation_before_loan.sable`](../corpus/verifies/nested_mutation_before_loan.sable).
- **Discovery mode:** the generated pairwise ownership/call matrix suggested a
  direct false-post timing twin absent from the handwritten corpus. `208a46a`
  turns that sprint into a deterministic integration matrix with proof,
  interpreter, diagnostic, and metamorphic oracles.
- **Certificate coverage now:** partial after ADR 0094. The closed recorded
  schedule checks receiver-first, left-to-right pending-loan stability against
  later nested effects. Effect discovery and schedule extraction remain
  trusted; the call-havoc certificate separately validates selected unique
  write-back.

### VF-10 — unauthenticated proof ingress could certify a false post

- **Window and exposure:** the exact introducing revision is not yet
  attributed. Published main revision `77bdf49` accepted both witnesses and
  reported `status: fully verified`; no tag exists in the affected history.
- **Witness and false claim:** both programs declare `post result = 1` and
  return zero. One discharges the obligation with `sorry`, introducing
  `sorryAx`. The other appends `axiom fabricated : False` as a continuation of
  a user theorem and later eliminates that false axiom. Lean accepted both
  generated documents, while the checked runtime monitor rejected the claimed
  postcondition.
- **Root cause:** user Lean text could change the proof environment without an
  exact declaration-delta check, and successful verification did not audit the
  complete transitive axiom dependency closure. Ignoring the `sorry` warning
  exposed one route; an ordinary injected axiom can be warning-free, so making
  warnings fatal alone would not close the incident.
- **Mitigation and remaining exposure:** `a2d0adc` removes the strongest status
  globally and reports `Lean accepted; proof dependencies unaudited` through
  an explicit assurance boundary. `9af008e` then rejects ordinary `sorry`,
  `admit`, default-warning `sorryAx`, malformed Lean diagnostic transport, and
  every other unrecognized Lean warning before root or imported proof evidence
  can publish. It also binds that warning policy exactly into proof snapshots,
  READY, artifact identities, in-flight builds, and `.ok` stamps. Commit
  `94c5113` adds a separately built trusted parser: every raw
  term consumes end of input, every ghost is exactly one expected `def` or
  `theorem`, and arbitrary comment metadata is delimiter-safe and single-line
  encoded. Continuation `axiom`, `set_option`, `#exit`, clause escapes, and
  comment escapes now fail before Lean sees a candidate. READY also
  SHA-256-binds the exact sorted local `.olean` set and parser executable. This
  still does not close the incident: the declaration-level warning remains
  fatal even when a theorem body locally suppresses `warn.sorry`, but compiled
  declaration bodies and the axiom closure remain unauthenticated, and release
  remains blocked.
- **Regression and discovery:**
  [`proof_ingress.rs`](../compiler/tests/proof_ingress.rs) runs bounded batch
  witnesses for root and imported `sorry`, `admit`, direct `sorryAx`, warning
  suppression, continuation commands, clause escape, and an injected axiom.
  Warning-producing and multi-command forms must fail with named diagnostics
  and leave no final proof artifact. The single-command suppressed-`sorryAx`
  witness also fails at Lean's declaration-level warning; the compiled
  declaration and transitive-axiom audits remain required for dependencies and
  other elaborated output. The supplied source-level
  review identified the routes; repository-local reproduction promoted the
  finding to confirmed verified-false.
- **Certificate coverage now:** none. Existing certificates are declarations
  in the same environment and do not authenticate its axiom closure. Closure
  requires exact permitted declaration deltas, a transitive axiom audit, and
  content-bound trust manifests for roots and imports.

## Accepted-invalid incidents

### AI-01 — borrowing a moved-out place was accepted

- **Window and exposure:** class place moves landed in `bc04e68`; `fa92e12`
  fixed the borrow path later on 2026-08-11.
- **Witness:** `Holder::hold(i); peek(&i)` passed checking even though `i` had
  moved; moving a base also failed to kill a later field borrow.
- **Why it is not VF:** the commit explicitly calls it latent: the interpreter
  still shared `Rc`s, so the repository records no false runtime contract.
- **Fix, regression, discovery:** every borrow is a place use and consults the
  same moved-place set as a read. Guards are
  [`borrow_after_move.sable`](../corpus/must-fail/borrow_after_move.sable) and
  [`borrow_field_after_move.sable`](../corpus/must-fail/borrow_field_after_move.sable).
  The place-engine review found it.
- **Certificate coverage now:** none; liveness remains a checker property.

### AI-02 — exposure left a second owner name usable

- **Window and exposure:** exposure landed in `c46bf45`; the owner was frozen
  in `842d1af` five days later.
- **Witness:** inside `unsafe expose &mut a`, source could still read, write,
  measure, assign, borrow, or re-expose `a`; a raw store beside `a[1] = 7`
  created two writers whose copy-back semantics disagreed.
- **Why it is not VF:** the commit records that the then-current interpreter
  and SVM both modeled exposure by copying, masking the intended real-storage
  alias. It does not record a proof/runtime counterexample on the admitted
  execution engines.
- **Fix, regression, discovery:** the owner is frozen for the lexical loan;
  the exposure binding is its only usable name. The guard family begins with
  [`expose_owner_write_beside_raw.sable`](../corpus/must-fail/expose_owner_write_beside_raw.sable).
  Review of the adjacent borrow-local incident found it.
- **Certificate coverage now:** no exposure certificate. The retained exposure
  plan fixes capture/body-close/copy-back/release order but is trusted.

### AI-03 — ownership metadata did not travel as one per-place state

- **Window and exposure:** the fragmented state accumulated as loan brands and
  mandatory-consumption markers were added. Three review passes fixed the
  family in `a7969ec`, `c46ba94`, and `3251c23`.
- **Witnesses:** an inferred raw declaration lost its loan brand; overwriting a
  place could erase `#[must_consume]`; consuming only one branch read as
  consumed because joins tracked only part of state; loop restoration could
  forget a migrated obligation; root-only lookup let a moved `self.f` revive or
  disappear at exposure close.
- **Root cause and structural fix:** initialization, moves, brands, and
  obligations lived in parallel fields and were joined or cleaned by selected
  subsets. `PlaceState`, `Place::state_key`, path joins, loop-backedge shape,
  and scoped-obligation rejection now operate on the complete place identity
  and state.
- **Regression and discovery:**
  [`expose_inferred_var_escapes.sable`](../corpus/must-fail/expose_inferred_var_escapes.sable),
  [`must_consume_overwritten.sable`](../corpus/must-fail/must_consume_overwritten.sable),
  [`must_consume_one_branch.sable`](../corpus/must-fail/must_consume_one_branch.sable),
  [`must_consume_migrates_across_loop.sable`](../corpus/must-fail/must_consume_migrates_across_loop.sable),
  and the field/exposure guards added by `3251c23`. Repeated adversarial review
  of ADR 0030 found the family.
- **Certificate coverage now:** none. The checker-authored ownership plan
  transports the resulting decisions; it does not certify the checker's
  branch, loop, or obligation logic.

### AI-04 — generic class destructors skipped ordinary member checks

- **Window and exposure:** generic classes landed in `4190ec9`; executable
  destructors landed in `9f1f1bc`; parity was restored in `c46ba94`.
- **Witness:** a template `deinit` consuming the same field twice passed
  because template destructors were not checked at all; template members also
  lacked the marker list and field-hole rule.
- **Root cause and structural fix:** “verify once at the template” used a
  parallel member-checking path that did not cover the destructor. Templates
  now run the same checks as concrete members.
- **Regression and discovery:**
  [`template_deinit_double_consume.sable`](../corpus/must-fail/template_deinit_double_consume.sable).
  The third ownership-transfer review found it.
- **Certificate coverage now:** none; this remains front-end admission logic.

### AI-05 — a moved class local remained callable as a method receiver

- **Window and exposure:** method receivers and by-value class moves had
  coexisted since the class-place/transfer work; `f1b6317` fixed the missing
  liveness check on 2026-08-19.
- **Witness:** `consume(item); item.get()` passed checking even though the
  implicit receiver loan tried to recreate a use of the moved place.
- **Why it is not VF:**
  [`method_receiver_after_move.sable`](../corpus/must-fail/method_receiver_after_move.sable)
  pins the static rejection but contains no false post or recorded runtime
  disagreement.
- **Root cause and structural fix:** receiver resolution bypassed the ordinary
  moved-place use check. Implicit receiver loans now validate place liveness
  before a call transition is recorded.
- **Certificate coverage now:** none for receiver liveness. Method call
  transitions are retained and exactly consumed after admission.

### AI-06 — adopting a descriptor did not spend the world's claim

- **Window and exposure:** POSIX-shaped adoption landed in `af06a18`; the
  missing state transition was fixed in `faf1ccf` about three hours later.
  Both revisions are in main's ancestry.
- **Witness:** calling `open_file(&mut w, fd)` twice could mint two `OpenFile`
  resources for the same descriptor. Affinity governed each token after it
  existed, but did not prevent the world from issuing the second token.
- **Why it is not VF:** the history records duplicated authority, not a
  contract Lean accepted and execution contradicted. The dynamic twin
  independently observes the invalid second adoption, but that is evidence for
  the resource model rather than a false theorem.
- **Root cause and structural fix:** token liveness and authority issuance were
  modeled separately. `PosixWorldView.claimed` now records descriptor claims;
  adoption requires an unclaimed descriptor and marks it claimed.
- **Regression and discovery:**
  [`world_double_adopt.sable`](../corpus/must-fail/world_double_adopt.sable)
  and
  [`world_double_adopt_dynamic.sable`](../corpus/test-fails/world_double_adopt_dynamic.sable).
  The ADR 0030 sink sweep found the missing mint transition.
- **Certificate coverage now:** none; sealed resource transitions and their
  view-state facts remain trusted checker/VCgen logic.

### AI-07 — an extern return blacklist missed storage-holding classes

- **Window and exposure:** the blacklist form was recorded in `209e561`; it
  became materially bypassable when resource-holding classes were admitted in
  `9f1f1bc`, and `c46ba94` replaced it with a whitelist later on 2026-08-12.
- **Witness:** rejecting only raw and resource return types still admitted an
  extern returning either an ordinary class or a class containing resource
  storage. The latter could carry foreign-created authority across a boundary
  whose contract could not establish its provenance.
- **Why it is not VF:** the repository records an invalid ABI admission, not an
  implemented extern whose verified contract was contradicted at runtime.
- **Root cause and structural fix:** a negative list named the storage forms
  that existed when it was written. Externs may now return only the explicit
  ABI whitelist: an integer or nothing.
- **Regression and discovery:**
  [`extern_returns_class.sable`](../corpus/must-fail/extern_returns_class.sable)
  and
  [`extern_returns_storage_class.sable`](../corpus/must-fail/extern_returns_storage_class.sable).
  The third ownership-transfer review found the container bypass.
- **Certificate coverage now:** none; extern signature admission remains a
  front-end trust boundary.

### AI-08 — a sealed operation kept a loan while a later argument moved its owner

- **Window and exposure:** the precise introducing commit is not yet
  attributed; sealed resource operations and nested ownership effects had
  coexisted before the audit. Published main revision `7957ad0` accepted the
  witness, and `4b4f93d` fixed it on 2026-08-20. No tag exists in the audited
  history.
- **Witness:**
  `resource_map_put(&mut cells, sealed_move_map(cells), cell)` creates the
  sealed operation's pending map loan in its first argument, then moves
  `cells` inside the later key expression. The apparently fresh scalar key hid
  that nested move from the operation's conflict check.
- **Why it is not VF:** the repository records forbidden loan/owner overlap but
  no Lean-accepted post contradicted by runtime for this witness. It therefore
  remains accepted-invalid rather than being folded into VF-09.
- **Root cause and structural fix:** sealed operations retained resolved loan
  effects but did not reconcile the moved-place delta accumulated while each
  argument was checked. `4b4f93d` consumes that checker-authored delta and
  applies the same left-to-right pending-reservation rule as ordinary calls.
- **Regression and discovery:**
  [`borrow_moved_in_sealed_nested.sable`](../corpus/must-fail/borrow_moved_in_sealed_nested.sable)
  requires `borrow.moved_in_call`; focused checker tests also cover nested
  mutation, completed-earlier, and disjoint-effect cases. The VF-09 fix audit
  found the sibling family.
- **Certificate coverage now:** partial after ADR 0094. The closed recorded
  schedule rejects the pending-loan/later-move combination, but extraction of
  sealed effects and moved-place deltas remains trusted Rust provenance.

## Runtime and monitoring divergences

### RD-01 — the monitor skipped `(old obj).field` frame projections

- **Window and exposure:** class contracts predated the runtime projection
  support; `b57f64c` fixed it while bringing up `Vec<T>`.
- **Witness:** a mutable method overwrote `buf[0]` while a false frame post over
  `(old self).buf` could be skipped instead of reported.
- **Fix and regression:** the monitor gained old-object projections and chained
  postfix evaluation;
  [`wrong_frame_dynamic.sable`](../corpus/test-fails/wrong_frame_dynamic.sable)
  must observe the violated post.
- **Discovery mode:** benchmark-driven dynamic-test coverage.
- **Certificate coverage:** not applicable. This is an evidence-channel
  defect, not a Lean theorem-validity defect.

### RD-02 — monitor and Lean parsed `↔` at different precedences

- **Window and exposure:** the runtime monitor existed from `ca1eb6a`; the
  option-access surface made the divergence concrete, and `67a77dc` fixed it
  hours after `d1895a7`.
- **Witness:** `1 = 2 ∧ result ↔ 1 = 2` has a different truth value if `↔` is
  parsed at equality precedence rather than Lean's loosest connective level.
- **Fix and regression:** a dedicated Iff token and bottom parse level now
  match Lean; [`test_option_access.sable`](../corpus/tests/test_option_access.sable)
  carries the precedence witness.
- **Discovery mode:** adjacent option-monitor work.
- **Certificate coverage:** not applicable; zero-skip dynamic tests are the
  relevant control.

### RD-03 — checker and interpreter disagreed about marker-block scope

- **Window and exposure:** unsafe/exposure blocks landed in `c46bf45`; the
  first correction was in `a7969ec`, with exposure lifetime refined in
  `c46ba94`.
- **Witness:** the checker kept a class local declared inside `unsafe {}` alive
  in the enclosing function, while the interpreter destroyed it at the closing
  brace; an accepted program therefore panicked the monitor. Treating exposure
  identically then let a loan-derived local outlive the loan.
- **Root cause and fix:** checker and interpreter each inferred scope from
  syntax. `unsafe` is now a non-scoping marker; an exposure is a real loan
  scope. The retained structured control plan now carries those boundaries.
- **Regression and discovery:** ownership lifecycle tests plus
  [`expose_local_outlives_loan.sable`](../corpus/must-fail/expose_local_outlives_loan.sable).
  The second and third transfer reviews found the mismatch.
- **Certificate coverage:** none; retained control is reconciled across
  consumers but not kernel-certified.

## Fail-open ICEs

### ICE-01 — class-borrow member calls bypassed shared argument machinery

- **Window and exposure:** shared class borrowing landed in `f95be36`; the
  common call path was completed in `595e799`.
- **Witness:** a class-borrow argument on a method was accepted by the checker
  and reached `unreachable!` in VCgen. Initializers also assumed a borrowed
  class invariant without emitting the `borrow_inv` obligation.
- **Root cause and fix:** free calls, constructors, and methods duplicated
  argument processing. They now share invariant obligations, borrow facts, and
  mutable write-back machinery.
- **Regression and discovery:** member borrow cases in
  [`class_values.sable`](../corpus/verifies/class_values.sable) and the class
  borrow refusal family introduced by `595e799`. `&mut C` feature work found
  the gap.
- **Certificate coverage:** current unique-borrow method write-back is partly
  certified; shared argument admission and invariant-obligation selection are
  not.

### ICE-02 — ownership sinks had reachable missing match arms

- **Window and exposure:** the affected shapes accumulated through resource,
  member-return, and transfer work; `faf1ccf` records three ordinary-source
  ICEs and closes them.
- **Witnesses:** assigning a resource parameter to a resource field, calling a
  method returning a class or resource, and returning `raw<u8>` each reached a
  missing arm instead of a named refusal or matching semantics.
- **Root cause and fix:** method paths did not mirror the function paths and
  the sink set was enumerated independently. The unified transfer operation,
  explicit ABI gates, and later exhaustive/shape-admission tables replace the
  implicit assumptions.
- **Regression and discovery:** the commit does not name one dedicated source
  file per ICE. Current forged-AST, stage-gate, transfer-sink, and support-matrix
  tests cover the boundaries; this missing one-to-one historical pin is a
  review caveat. The ADR 0030 transfer sweep found them.
- **Certificate coverage:** none for source admission; later plans make a
  missing consumer fail closed after checking succeeds.

### ICE-03 — retained trait calls admitted values outside their proof domain

- **Window and exposure:** the precise introduction is not yet attributed.
  Published main revision `7957ad0` is affected; there is no tag in the audited
  history. `4b4f93d` fixed it on 2026-08-20.
- **Witness:** an otherwise nonconflicting retained trait call can declare and
  receive a class or resource-borrow argument. The checker admits the ordinary
  source, but VCgen's trait-call path requires every evaluated argument to be
  `Val::Int` and reaches `unreachable!("checked: int args")` for the admitted
  class/resource value.
- **Root cause and structural fix:** trait signatures reused the general
  parameter gate while the retained ADR 0009 proof model substitutes integer
  values only. Existing special-case fences were a negative list. `4b4f93d`
  replaces it with the proof domain's positive gate: only `Int` and the
  integer-instantiating `Param` form may appear as trait parameters or results;
  every other shape fails by name before VCgen, with the UART-specific refusal
  retaining priority.
- **Regression and discovery:** the direct guard is
  [`trait_borrow_call_unsupported.sable`](../corpus/must-fail/trait_borrow_call_unsupported.sable),
  with the temporal-priority twin
  [`trait_borrow_nested_mutation.sable`](../corpus/must-fail/trait_borrow_nested_mutation.sable)
  and class/resource/raw/unit signature guards. The VF-09 fix audit followed
  retained `TraitCall` into its supposedly unreachable non-integer arm.
- **Certificate coverage:** none. Trait-call source admission and abstract
  contract substitution remain outside the transition-certificate slice.

## Pre-merge and pre-admission near misses

### NM-01 — `join(a, a)` could duplicate an empty resource

- **Exposure:** no known vulnerable main revision; `d8e875c` introduced the
  sealed operation and fixed the adversarial case in the same commit.
- **Witness:** a zero-length span is adjacent to itself, so the geometry VC did
  not prevent `join(a, a)` from producing duplicated authority.
- **Fix and regression:** each argument moves as it is checked;
  [`resource_join_twice.sable`](../corpus/must-fail/resource_join_twice.sable)
  pins the second use.
- **Discovery mode:** a forcing resource benchmark contradicted a source
  comment that claimed the case was already covered.
- **Certificate coverage:** none; sealed-operation transitions remain trusted.

### NM-02 — resource-holding class admission invalidated two old assumptions

- **Exposure:** no known affected main revision. Resource fields and both
  corrections landed together in `9f1f1bc`.
- **Witnesses:** a class return could launder a loan brand even when its
  signature did not visibly return raw/resource storage; `&mut self.w`
  write-back replaced the whole `self` object with a resource view and reached
  `unreachable!` instead of updating the projection.
- **Root cause and fix:** earlier arguments relied on the language having no
  storage-bearing class, and mutable write-back assumed every loan named a
  root. `class_holds_storage` is transitive, and field write-back rebuilds the
  base object while preserving siblings.
- **Regression and discovery:**
  [`expose_launder_via_class.sable`](../corpus/must-fail/expose_launder_via_class.sable)
  plus the `raii_handle` partial-move and destructor fixtures. Destruction
  feature work invalidated the earlier assumptions before lifting the gate.
- **Certificate coverage:** current explicit unique-borrow field write-back is
  partly covered by ADR 0087; class storage escape remains checker logic.

### NM-03 — wildcard class-field dispatch could emit a silent wrong term

- **Exposure:** `59f3fd0` states that the affected shapes were still refused by
  earlier gates; the explicit fix landed before option-field admission.
- **Witness:** four wildcard paths could emit literal `0`, drop a field from a
  substitution, panic on store, or model a field as a bare integer.
- **Fix and regression:** exhaustive field-state dispatch with
  `internal.vcgen.field_state_unsupported`, class-field stage columns, and a
  byte-identical generated-Lean snapshot over all live paths.
- **Discovery mode:** explicit trusted-dispatch audit ahead of a new field
  shape.
- **Certificate coverage:** none; the defense is exhaustive Rust matching and
  fail-closed admission.

### NM-04 — the borrow representation fold dropped two thirds of array paths

- **Exposure:** no broken refactor was committed. `b0964eb` includes the fold
  and its correction together.
- **Witness:** nine sites formerly meant “array in any binding mode”; after the
  representation changed, they silently matched owned arrays only. Ordinary
  tests stayed green while generated Lean lost borrowed paths.
- **Fix and regression:** ownership and mutability are derived structurally;
  the generated-Lean snapshot and direct stage-gate battery pin the bijection.
- **Discovery mode:** snapshot comparison, not a handwritten source
  regression.
- **Certificate coverage:** none; this is exactly the source/representation
  translation boundary certificates do not yet cover.

### NM-05 — a record's outer alignment did not imply field alignment

- **Exposure:** under-aligned layouts were statically accepted from `afa5133`
  until `992437d`, but record values still had no byte representation and the
  native POD lowering landed only after the fix.
- **Witness:** `#[layout(size := 8, align := 1)]` could contain a `u64` field at
  offset zero even though an align-1 record base need not align that field.
- **Fix and regression:** outer alignment must be a multiple of every field
  alignment in both checker and `Layout.fieldFits`;
  [`record_field_underaligned.sable`](../corpus/must-fail/record_field_underaligned.sable).
- **Discovery mode:** static layout audit before native record transport.
- **Certificate coverage:** the layout proposition is kernel checked where
  used, but source layout validation remains trusted.

### NM-06 — slot put initially visited value staging before its index

- **Exposure:** no known vulnerable main revision. The mismatch was found and
  corrected while `fe72c55` was authoring the first admitted slot operations.
- **Witness:** `slot_put(&mut cells, index_of(&item), item)` must evaluate the
  borrowing index before moving `item` into staging. The preliminary VC path
  staged the value first, disagreeing with source order; the trap twins also
  require index evaluation, then value staging, then bounds/occupancy guards.
- **Root cause and fix:** the new sealed operation had an operation-shaped
  evaluator instead of using expression order as an invariant. VCgen now walks
  the index before the move, and all executable consumers retain the same
  staged-put order.
- **Regression and discovery:** the
  `slot_put_evaluates_a_borrowing_index_before_staging_and_moving_its_value`
  unit in [`vcgen.rs`](../compiler/src/vcgen.rs), plus
  [`slots_bool.sable`](../corpus/svm-diff/slots_bool.sable). An adversarial
  borrowing operand found it before the gate opened.
- **Certificate coverage:** none for evaluation order. The slot certificate
  checks the final structural write-back after staging, while exact retained
  actions and differential traps guard the preceding order.

### NM-07 — initializer slot operations read a different field state

- **Exposure:** no known vulnerable main revision; the initializer mismatch was
  corrected within `fe72c55` before slot operations were admitted.
- **Witness:** an initializer allocates `self.cells`, puts `7`, then takes it
  into another field. An early path read the general enclosing-`self` chain
  instead of the exact symbolic entry installed for the initialized field, so
  the take did not necessarily observe the preceding put.
- **Root cause and fix:** constructor field construction and ordinary method
  field state had parallel lookup paths. The common slot-place helpers now
  preserve their intentional context split: in `Cctx::Init` they read and
  write `env["self.field"]` until the object exists; in methods and deinits
  they project from and update the enclosing `self` state chain.
- **Regression and discovery:**
  `initializer_slot_operations_read_the_exact_initialized_field_state` and
  `direct_self_slot_fields_use_the_enclosing_class_state_chain` in
  [`vcgen.rs`](../compiler/src/vcgen.rs). The first constructor round-trip
  forced the mismatch.
- **Certificate coverage:** partial after `7d054cc`: successful take/put
  write-back is structurally certified, but selection of the initializer's
  pre-state remains trusted Rust provenance.

### NM-08 — whole-owner loop replacement retained a stale slot length

- **Exposure:** no known vulnerable main revision. The verified-false draft was
  found and fixed during `fe72c55`, before the feature commit landed.
- **Witness and false claim:** a loop replaces a length-one local slot owner, or
  initializer field, with `alloc_slots<u64>(2)`. The draft retained the old
  length equality and Lean accepted the false post-loop assertion
  `cells.len = 1` (and its field twin).
- **Root cause and fix:** slot-operation mutation and whole-owner assignment
  shared a havoc family but not a fact-kill rule. A whole-place write now drops
  fresh-to-stale slot length equalities; the final unit invokes Lean and
  requires both false assertions to remain failed obligations.
- **Regression and discovery:**
  `slot_loop_whole_owner_writes_drop_local_and_init_field_length_facts` in
  [`vcgen.rs`](../compiler/src/vcgen.rs). A false-claim probe, rather than the
  positive owner-slot corpus, found it.
- **Certificate coverage:** none. Slot certificates cover direct take/put
  write-back, not whole-owner assignment or loop havoc.

### NM-09 — by-value class snapshots aliased nested runtime slots

- **Exposure:** no known vulnerable main revision. The interpreter and its
  detached snapshot regression landed together in `ddb3c67`.
- **Witness:** `consume_slot_snapshot(b)` moves `b`, drains the moved owner's
  slot, and has entry-value posts that the original `b.cells` still contains
  `7`. A shallow snapshot of the nested slot allocation changed when the live
  owner was drained, so the monitor could reject a true entry-value post.
- **Root cause and fix:** runtime ownership values and immutable specification
  snapshots shared the same nested allocation identity. Snapshot construction
  now creates a detached specification value with no executable authority.
- **Regression and discovery:**
  `test_slot_class_parameter_snapshot_is_detached` in
  [`test_owner_slots.sable`](../corpus/tests/test_owner_slots.sable). Lifecycle
  tests with a by-value class parameter found the evidence-channel alias.
- **Certificate coverage:** not applicable. This is monitor evidence, not a
  claim discharged by Lean.

### NM-10 — the first slot-put certificate claim was circular

- **Exposure:** no unsound certificate was merged. The claim was narrowed while
  `7d054cc` was authoring the certificate slice.
- **Witness:** the proposed put certificate treated the relation between the
  incoming owner and its staged symbolic term as if the kernel had established
  provenance, although both sides were selected by the same Rust generator.
  That would have repackaged the trusted assumption rather than checked it.
- **Root cause and fix:** certificate scope initially followed the desired
  end-to-end story instead of the independent evidence available. The final
  `SlotPutWriteback` checks only
  `observed = before.set i (some staged)`; incoming-to-staged equality, index,
  snapshot, and staged-term provenance are explicitly trusted boundaries.
- **Regression and discovery:** transition/certificate tamper tests in
  [`transition.rs`](../compiler/src/transition.rs) and
  [`vcgen.rs`](../compiler/src/vcgen.rs) independently alter the structural
  fields, while the ADR states what coordinated substitution remains outside
  the claim. Certificate threat-model review found the circularity.
- **Certificate coverage:** this correction defines the coverage: structural
  local/direct-field take/put write-back only, not payload provenance or source
  translation.

## Trend and interpretation

The first cluster, from 2026-08-09 through 2026-08-13, is dominated by one rule
being restated at each syntax form: havoc tables, borrow forms, move sinks,
scope walkers, and partial `PlaceState` joins. Benchmarks and adjacent feature
work found several of these, but the existing corpus usually became a
regression net only after discovery.

The representation work of 2026-08-15 through 2026-08-17 improved the
discovery mode. Direct type/stage matrices and generated-Lean snapshots caught
the borrow-fold and field-dispatch defects before their affected shapes were
admitted. That interval and the immediately following day still produced three
confirmed verified-false root causes: a persistent borrow local, wildcard loop
havoc, and the 2026-08-18 borrow-plus-move call interaction. The evidence
therefore supports “better detectors” but not yet “a declining incident rate.”

G3's owner-slot slice strengthens that mixed conclusion. Five distinct defects
were found before their affected implementation landed: evaluation order,
initializer field identity, a verified-false stale length, aliased monitor
snapshots, and an over-broad certificate claim. Those are near misses, not
exposed incidents, because the probes and corrections landed with the feature.
VF-09 immediately afterward is the warning against a victory narrative:
generated interaction coverage found a verified-false nested-call timing
witness outside the existing corpus on published main. The `4b4f93d` fix audit
then found AI-08's sealed-operation nested move and ICE-03's older trait
negative-list gate. `208a46a` makes the discovery method durable as a bounded
pairwise matrix rather than treating the original sprint as a one-off success.

C0 changes the expected failure mode without completing the soundness proof.
Shared place identity, one checker-authored ownership plan, retained structured
control, exhaustive dispatch, and exact consumer reconciliation make many
former omissions named internal refusals. Call and slot write-back certificates
put the Lean kernel under selected structural transitions; the argument-schedule
certificate checks alias safety for one closed recorded schedule. None proves
that the checker chose every required mutation, rejected every alias, or
translated the source into the right plan. VF-08, AI-05, VF-09, and AI-08 are
the clearest reason to keep testing admission and evaluation-order interactions
independently of plan-consumer correctness.

VF-10 is a different trust-boundary failure from the ownership cluster:
accepted Lean declarations received Sable's strongest status without an
authenticated axiom closure. The global status downgrade contains the claim,
and the warning/cache gate closes one concrete ingress route, but declaration
injection and the axiom closure remain open. This is still an unresolved
release-blocking incident rather than evidence of a completed fix.

This ledger is the baseline for trend claims. A future confirmed incident
should be added with a minimized witness and regression; mitigation and fix
hashes should remain distinct when containment precedes closure. Pre-merge
findings should be recorded too, but never counted as exposed or verified-false
without the corresponding evidence.
