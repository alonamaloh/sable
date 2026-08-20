# ADR 0094 — argument schedules have a closed safety certificate

**Decided 2026-08-20.** Every user call and compiler-sealed
raw/resource/device or owner-slot boundary in every checked non-extern body
receives a bounded, closed Lean certificate for its recorded left-to-right
argument effects. This includes dynamic `test_` bodies and proof-reusing
instances. It checks one alias-safety decision; it is not a source-to-runtime
correctness theorem.

## Context

The checker already enforced the argument-order rules needed by the symbolic
call model: an implicit receiver is reserved first, explicit arguments run
left-to-right, a callee loan remains pending until entry, and nested calls may
complete mutations or moves while evaluating later arguments. Those rules
were spread across direct-loan conflict checks, move tracking, and recursive
mutation collection. A weakened or drifting check could therefore admit a
schedule whose individual expression types remained valid but whose combined
effects were unsound.

Four historical adversarial shapes define the initial acceptance boundary:

- VF-03: overlapping unique/shared loans enter one callee;
- VF-08: one call both lends and directly moves overlapping storage;
- VF-09: a later nested mutation invalidates an earlier pending loan;
- AI-08: a sealed boundary's later nested move invalidates its earlier loan.

The certificate must reject those shapes independently of the admission
helpers whose weakening it is meant to detect.

## Decision

`Sable.ArgumentSchedule.safe` in `lean/Sable/Transition.lean` decides a closed
schedule. A place retains a nonempty root plus its field path, and overlap is
the structural common-prefix relation: `x` overlaps `x.f`, while `x.left` and
`x.right` do not. A schedule contains an optional direct receiver effect and a
one-based ranked list of arguments. Each argument retains its ordered nested
`write`/`move` effects followed by one direct `loan`/`move`/inert effect.

The receiver is processed first. Pending loans reject later overlapping
writes or moves. Previously completed moves reject every later overlapping
write, move, or loan. A unique loan rejects every overlapping pending loan;
two shared loans may coexist. A direct move and callee loan therefore conflict
in either order. Completed mutation before a later loan remains legal, and a
nested shared read is intentionally transient. Receiver moves, invalid places,
nonconsecutive ranks, more than 64 arguments, or more than 64 nested
effects fail the decision.

The generated theorem has no binders, hypotheses, or generator-authored
premises:

```lean
theorem <identity> : Sable.ArgumentSchedule.safe <closed-schedule> = true := by
  decide
```

`compiler/src/argument_schedule.rs` extracts that schedule after successful
checking and symbolic generation. It is a separate typed-AST walk. It neither
calls nor shares `check_pending_loan_argument_mutations` or
`collect_checked_expr_mutations`, and it does not treat `BodyPlan` as an
expression CFG. It consumes exact checker-owned call, sealed-operation,
owner-slot, option-take, and expression-internal value-transfer records.
Every lookup reconciles the table key with the record's embedded identity and
the schedule-relevant typed AST facts: types, spans, places, parameter
positions, and operation flavor, plus the source-carried target for free calls
and constructors. A `MethodCall` AST retains only receiver spelling and method
spelling, not its resolved receiver class; that class target remains selected
from the checker record, then is checked for an exact class referent and
signature. `some(owner)` consumes its exact `OptionPayload` transfer;
`slot_put` consumes the canonical owner/span/`SlotPut(place)` transfer. After
traversal, a global key comparison rejects every unvisited record, including a
record retargeted to a phantom owner. Reusing one record from two AST
occurrences also fails immediately. Every checked non-extern body emits its
closed schedules, including dynamic `test_` functions and concrete instances
whose ordinary functional obligations reuse ADR 0009 integer-model proofs.

User calls, constructors, methods, sealed raw/resource/device operations, and
the three sealed owner-slot operations (`alloc_slots`, `slot_take`, and
`slot_put`) use the same mandatory artifact category. The ordinary obligation
skip set cannot suppress them. The theorem name is a length-framed encoding of
the typed owner, boundary flavor/target, and body-relative source occurrence;
artifact preparation rejects cross-category or imported-name collisions.
Lean rejection maps to `internal.argument_schedule_certificate_rejected`.

## Evidence

A test-only mutation harness compiles entirely out of production. It disables
one historical checker guard at a time, admits the exact VF-03, VF-08, VF-09,
and AI-08 corpus witnesses, and requires Lean to reject their closed schedule
certificates. A static source guard and a non-test build ensure no dormant
false-return helper, flag, or bypass branch is shipped.

Lean truth-table examples pin receiver-first ordering, rank continuity,
structural overlap, mutation-before-loan, pending-loan versus later write/move,
direct and nested duplicate moves, move-before-loan, unique/shared conflict,
and the `OptionPayload` move cases. Rust tests cover schedule tampering,
non-skippability, length-framed names, exact and embedded-key mismatches,
phantom-owner/global-unvisited records, owning-`some` transfer visitation, and
coordinated owner-slot field and transfer-key tampering.
The emission-scope regression requires both a checked dynamic `test_` body and
an ADR 0009 proof-reusing concrete instance to contribute schedule theorems;
the duplicate-consumption regression reuses each expression-internal record
family from a second forged AST occurrence and requires a named refusal.

## Consequences and boundary

For the exact closed schedule emitted, the Lean kernel now decides the ranked
alias rule rather than accepting a Rust-authored proposition as a hypothesis.
The historical conflict shapes remain rejected even when their corresponding
checker guards are weakened in the mutation harness.

The Rust typed-AST/ownership-plan extraction remains trusted. This ADR does
not prove that the checker discovered every source effect, that a forged typed
AST and a coordinated forged record/schedule cannot agree on the same lie, or
that callee contracts describe their implementations. It does not relate the
certificate to interpreter, SVM, LLVM, native ABI, cleanup, traps, or runtime
execution, and it is not a source-to-runtime or source-to-VC translation
theorem. Exact lookup and global completeness catch isolated deletion,
substitution, embedded-key disagreement, phantom-owner retargeting, and
omission. A coordinated method table+record retarget remains within trusted
Rust provenance. These checks do not remove the Rust compiler from the trusted
base. The argument/effect ceilings are denial-of-service
bounds, not claims about unbounded schedules. The 64-argument and
64-total-nested-effect ceilings were validated together by an at-bound
generated-Lean reduction containing 64 disjoint nested moves plus 64 disjoint
direct moves under the artifact's ordinary kernel budget.
