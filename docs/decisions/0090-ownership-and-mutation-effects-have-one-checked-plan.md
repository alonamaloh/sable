# ADR 0090 — ownership and mutation effects have one checked plan

**Decided 2026-08-19.** For the admitted checker-to-VC boundary, the checker
is the sole author of ownership transfers and mutation effects. VC generation
requires the exact in-memory plan produced for the same typed AST; it does not
rediscover those effects by walking source syntax.

## Context

ADR 0088 handed explicit unique-borrow call havoc from the checker to VC
generation, but deliberately left the rest of the boundary split. VCgen still
classified by-value call arguments, method receivers, sealed resource/device
operations, affine-option extraction, exposure reconstruction, and loop havoc
through neighboring syntax-dependent decisions. The checker separately knew
whether a transfer copied, moved, carried a mandatory-consumption obligation,
or crossed an exposure brand. Sharing `Place` made both answers use the same
storage identity; it did not make either answer authoritative.

This is the dangerous kind of duplication for a proof-producing frontend. A
missed mutation can leave stale symbolic state in scope, while a differently
decoded move or loan can update the wrong owner. Keeping the two walkers in
agreement by review is not an invariant.

## Decision

`CheckResult` carries one ephemeral `CheckedOwnershipPlan` for the exact
post-monomorphization typed `Program`. Its stable identities use a typed
`CallOwner` plus the full expression or statement span; user calls additionally
include their resolved, flavor-preserving `CallTarget`, and non-call value
transfers include their semantic sink (binding, assignment place, return,
field, sealed-deallocation role, or option payload). The sink is necessary
because parser desugaring may give two distinct boundaries one source anchor;
no identity depends on traversal order. Every table rejects a duplicate key.

The plan contains the complete ownership/mutation facts needed by the current
VC surface:

- every admitted free, constructor, and method call records its receiver and
  every parameter as either a typed `ValueTransfer` or `CallTransition` loan;
- every sealed raw, resource, and device operation records its resolved enum
  target, result type, and every argument's transfer or loan;
- affine-option takes record their source `Place` and payload type;
- exposures record the owner place and type, mutability, and the two checked
  binding identities;
- every loop records the checker-computed mutation set, whose variants retain
  direct writes, unique loans, option extraction, and mutable exposure
  reconstruction; and
- every non-call sink at which the checker performs a value transfer records
  its source place, value type, copy/move/fresh classification, obligation and
  brand state, and span.

Records are inserted only in successful checker arms, after the ordinary type,
borrow-conflict, escape, and affine-shape rules have admitted the boundary.
Loop summaries are constructed in the checker after their condition and body
have been checked; resolved call, sealed-operation, option, and exposure
records are inputs to that construction. This makes loop havoc a projection of
checked facts rather than a second effect analysis in VCgen.

VC generation receives the entire `CheckResult`. Each verified `Generator`
first requires its exact `ControlBody` identity and then performs immutable,
exact lookups in `CheckedOwnershipPlan` at the corresponding semantic
boundaries. A record is checked against the typed AST before use. Missing or
mismatched records latch a named internal refusal. Symbolic path splitting may
visit one source record repeatedly; every visit applies the effect, while an
at-least-once set requires every record owned by that verified callable to be
visited. Deterministically selected unvisited records are also named refusals.
The unique-borrow call subset continues to emit one noncolliding ADR 0087
certificate per symbolic visit.

Nested expression evaluation remains left-to-right. Child expressions are
evaluated, and therefore consume their records, before the enclosing call or
sealed operation looks up and applies its own record. Failed lookup uses only
an inert placeholder after latching the refusal; it cannot reconstruct a
proof-state ownership effect from syntax.

The source-only mutation scan used to reject a `for` desugaring whose hidden
bound/index would be modified now lives in the parser. It is a conservative
parser restriction, not a proof-state effect authority. VCgen retains the
shared `Place` decoder only to validate that a checked record still matches
the typed expression presented to it; it does not use that decoder to select
an effect or mutation place.

## Evidence

Focused tests require missing, mismatched, and unvisited records to fail closed
for option extraction, exposure, sealed operations, loops, and non-call value
transfers. All non-call effect tables and the call table reject duplicate
stable identities. Real-source tests pin affine-option extraction in loop
havoc, resource `split_off`, nested inner-before-outer call evaluation, root
and projected loan places, method receivers, and retained template
destructors. The branch/join call regression still requires a distinct
transition certificate for every symbolic visit.

The full library and source corpus remain the coverage proof that every
checker-produced record for an actually verified callable has a VC consumer:
an omitted consumer is reported by the per-owner unvisited check rather than
being silently ignored.

## Consequences and boundary

ADR 0086 criterion 2 is closed for the admitted checker-to-VC boundary: place
identity and ownership/call-transfer/mutation facts now have one typed
checker-authored representation, and the old VC effect walkers are removed.
ADR 0088 remains the narrower certificate-bearing history of unique-borrow
calls; its statement that the other effects remain future work is superseded
by this decision.

This plan is not serialized into module artifacts and is not a portable IR.
Interpreter, LLVM, and SVM ownership execution remain governed by their checked
program representations. Lexical cleanup ordering, structured route
consumption, assignments, direct trap sites, and concrete runtime class drops
are the separate criterion-3 work completed by ADRs 0089, 0091, and 0092.
`CheckedOwnershipPlan` does not choose runtime storage layouts or certify its
own source translation. ADR 0092's replacement and discarded-temporary actions
instead link back to its exact `ValueTransferKey`s; dynamic liveness and concrete
storage remain execution-consumer state.

Trait-call proof reuse remains outside the handoff because its admitted VC
domain is scalar/integer-only and therefore has no owning value or loan effect
to transfer. Shared loans are recorded at user and sealed call boundaries but
perform no havoc. Static/system allocation statements create authority through
their compiler-defined statement semantics rather than transferring an
existing owner, and scalar/record element stores carry no ownership effect;
their direct mutation places are nevertheless present in enclosing loop
summaries.
