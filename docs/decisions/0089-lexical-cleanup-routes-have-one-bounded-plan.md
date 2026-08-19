# ADR 0089 — lexical cleanup routes have one bounded plan

**Decided 2026-08-19.** The interpreter and LLVM backend share one typed
authority for lexical scope identity, conditional drop identity, and cleanup
order. This is a bounded cleanup/control slice, not the complete normalized
control-flow model required by ADR 0086.

**Follow-ons:** ADR 0091 retains the checker-sealed plan through every checked
program carrier and adds formal-SVM consumption. ADR 0092 adds the pre-check
outline, retained structured edges, VC consumption, exact assignment/trap/class
drop plans, and direct SVM trap consumption. The two-consumer boundary below is
the historical boundary of this first tranche.

## Context

The interpreter and native backend implemented the same lifetime rules with
different stacks: function-body locals, branch-arm locals, and loop-body
locals die in reverse lexical order; an `unsafe` block is a marker rather than
a scope; an early return leaves every active lexical scope; and a trap aborts
without running cleanup. Both implementations were individually tested, but
neither was an authority for the other. A new ownership-bearing shape could
therefore enter one cleanup registry or leave one route without entering the
other.

At that checkpoint, the neighboring consumers did not yet have the same
operational model. VC generation represented loop continuation and exposure
reconstruction through symbolic tails and computed havoc from proof-state
effects. The checker joined affine place state at branches and backedges. The
SVM deliberately erased declaration scopes into a flat environment and had no
general destructor/drop transition. Combining those structures under one CFG
name would have hidden rather than removed the remaining semantic decisions.

## Decision

In that first implementation, `compiler/src/control.rs::BodyPlan` was built
after each callable body had checked. It assigned:

- stable lexical scope keys from the body owner, scope/arm kind, and source
  anchor; duplicate keys are an internal refusal rather than a fallback to
  traversal order;
- `ScopeId` values for the frame, function body, branch arms, loop bodies, and
  exposure bodies, while treating `unsafe` as transparent;
- `DropId` values for typed `Place` cleanup candidates, in declaration order;
  and
- ordered exit routes for lexical fallthrough, loop backedges, and explicit or
  implicit returns.

A candidate is static and conditional. Whether a declaration or later
initialization has made its slot safely droppable on a particular dynamic or
lowered path is consumer state; moving its value may then leave the place
empty. The plan does not pretend to decide either fact. It decides which
candidate is being discussed and the order in which armed candidates are
visited. Existing interpreter and LLVM destruction operations remain
responsible for checking a slot and destroying its value.

Returns have two routes. Lexical locals die before the interpreter checks
postconditions, while owned parameters remain readable by those postconditions
and die on the frame route afterward. LLVM erases contracts and may emit those
routes consecutively while preserving their cleanup order.

At this checkpoint, `BodyPlan` also stated the language's no-unwind policy as
one empty trap route. The interpreter's error propagation and LLVM's terminal
trap blocks retained their existing implementation of that policy; exact source
trap identities were added later by ADR 0092.

## Evidence

Structural tests pin stable-key refusal, `unsafe` transparency, reverse
declaration and scope order, loop-body-only backedge cleanup, two-phase return
cleanup, and the empty trap route. An interpreter regression returns from a
nested branch and requires both inner and outer owners to be removed; existing
and focused trap regressions require owner places to remain untouched after a
trap. LLVM regressions inspect generated IR for inner-before-outer cleanup on a
nested return, reverse loop cleanup, and the absence of cleanup calls in a
terminal trap block.

## Consequences and boundary

At this checkpoint the interpreter and LLVM backend consumed `BodyPlan` routes
for cleanup order instead of independently reversing their local registries.
They retained path-specific arming and value-specific destruction, which remain
dynamic and representation-specific decisions.

This first tranche did **not** close ADR 0086 criterion 3 or C0. Its
checker/VC/SVM, exposure, assignment, and trap-site limitations are superseded
by ADRs 0091–0092. ADR 0092's callable-wide reconciliation and exact local/field
replacement and discarded-temporary actions now close criterion 3 and C0. The
current model is a cross-stage structured typed control/action plan, not a full
expression CFG or a mechanized translation proof.
