# ADR 0088 — checked call effects are an ephemeral handoff

**Decided 2026-08-19.** The checker, not VC generation, selects the places
havocked for unique-borrow arguments at admitted free, constructor, and method
calls. The handoff is typed, exact, and local to one checked AST.

**Follow-on:** ADR 0090 subsumes this call table into the broader
`CheckedOwnershipPlan` and closes criterion 2 for the admitted checker-to-VC
boundary. This ADR remains the history and exact contract of its call subset.

## Context

ADR 0087 introduced `CallTransition` and a kernel-checked witness that VCgen
wrote a fresh call state back to the recorded place. Its first implementation
still made VCgen independently inspect parameter types and decode argument
syntax to create that transition. Sharing `Place` prevented the two decoders
from disagreeing about roots and fields, but did not make one stage authoritative
about which call effects typechecking had admitted.

The audit also found a checker-side disagreement. Free calls and constructors
used `require_explicit_borrow`, enforcing ADR 0023's rule that unique access is
always visibly reborrowed with `&mut`; method arguments only checked the
resulting type and could accept a bare unique-borrow variable. Producing one
handoff from inconsistent admission rules would preserve the wrong split.

This boundary is particularly sensitive: omitting a mutable argument leaves
callee posts talking about stale state, while choosing the wrong place can
replace an owner instead of one field. The compiler already runs checking and
VC generation consecutively over the same post-monomorphization `Program`, so
no persistent interchange format is needed.

## Decision

`CheckResult` carries `CheckedCallTransitions` as the call component of its
`CheckedOwnershipPlan`. Every successfully checked free, constructor, and
method call contributes one record, including calls with no unique-borrow
effects. A `CallSiteKey` contains:

- the enclosing callable's flavor-preserving semantic identity (`Function`,
  `Constructor`, `Method`, or `Deinitializer`);
- the call expression's full source span; and
- its resolved target and flavor (function, constructor, or method).

Insertion rejects a duplicate key. Source spans are not used alone because
monomorphization preserves them; traversal ordinals are not used because two
independent walkers can drift. If owner, span, and target ever cease to be
unique, checking fails closed until the AST gains a stronger node identity.

That owner type is also the key of the checker's recursion graph. Constructors
and methods with the same member spelling therefore remain distinct nodes;
duplicates within one member flavor are rejected before lookup, and a member
cycle is diagnosed at its own declaration rather than being treated as a free
function.

For every unique-borrow parameter, the checker records its parameter index and
name plus a `CallTransition`: the already-resolved `Place`, referent `Ty`,
`HavocUniqueBorrow` effect, and argument span. This happens only after argument
typing and whole-call borrow-conflict validation succeed. Explicit array,
class, and resource borrows are covered. Free, constructor, and method
arguments use one validator and the same `require_explicit_borrow` authority:
bare shared-borrow forwarding remains admitted but creates no havoc effect,
while every unique class/resource borrow and every array borrow is explicit.

VC generation receives the whole `CheckResult`. At the existing call-havoc
point it requires the exact key and checks parameter position/name, referent,
and argument span on every symbolic visit. The checked record is immutable:
path splitting may legitimately reach one source call once per incoming
symbolic path. VCgen records at-least-once visitation per checked source site
and assigns each visit a deterministic per-generator ordinal, so every visit
performs its own havoc and emits a noncolliding certificate. Missing,
mismatched, and per-verified-callable unvisited records are named internal
refusals. The lookup remains after left-to-right argument evaluation, so a
nested call validates and applies its own transition before the enclosing call
applies its effects.

Retained ADR 0009 class templates include their destructor in that rule. VC
generation synthesizes the destructor's callable shell, runs its body with the
template's abstract type-parameter and trait context under `Cctx::Deinit`, and
visits records owned by `<Template>::deinit`. Concrete proof-reuse instances
may skip their copied destructor bodies only because this retained template
walk now verifies those obligations and effects once.

The handoff remains in memory. Module artifacts contain the resulting VCs and
certificates, never the Rust call-effect table. Imported modules are checked
and generated within their own rooted preparation just as before.

## Evidence

Focused tests cover duplicate identities; missing, mismatched, and unvisited
records; nested calls applying inner then outer effects; whole-array places;
a destructor's projected resource field; constructor and method arguments; and
the named refusal of a bare unique-borrow method argument. A branch/join
regression reaches one checked source call along two symbolic paths and
requires two same-place certificates with distinct visit identities and Lean
theorem names. A retained generic
destructor regression requires both its inline obligation and its projected
resource-field call certificate to be generated; a named must-fail subject
pins an unprovable template-destructor assertion. Existing call-havoc tests
require the checker-authored transition to reach the non-skippable ADR 0087
certificate. A same-spelled initializer/method regression requires distinct
call records, clause helpers, and VC theorem identities, while recursion and
duplicate-member must-fail subjects pin the typed owner assumptions.

## Consequences and boundary

VCgen no longer re-decodes source arguments to decide unique-borrow call
havoc. It still owns symbolic binder creation, fresh-state facts, place
write-back, callee-post substitution, and transition-certificate evidence.

This decision alone is not a general ownership or effect IR. ADR 0090 is the
follow-on authority for value moves, mandatory-consumption state, shared loans,
receivers, sealed operations, exposures, and loop mutation discovery, and
closes ADR 0086 criterion 2 for the admitted boundary. Trait calls remain
scalar-only there and therefore contribute no ownership effect. The broader
coverage must be attributed to ADR 0090, not inferred from this call-only
history.
