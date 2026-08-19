# ADR 0087 — call havoc has a kernel-checked transition certificate

**Decided 2026-08-19.** The first C0 symbolic-transition certificate covers
the dangerous write-back step for explicit unique-borrow call arguments. It is
a bounded check of emitted symbolic state, not general translation validation.

**Follow-ons:** ADR 0088 moves production of the stage-neutral transition to an
ephemeral checker-to-VC handoff; ADR 0090 extends that handoff to the complete
admitted ownership/mutation boundary. The certificate and its assurance
boundary defined here are unchanged.

## Context

At a call through `&mut`, the caller must stop using the argument's pre-call
symbol and continue under a fresh state constrained by the callee's contract.
This path has produced two high-impact failures: mutable-array call havoc was
once omitted, leaving stale state provable, and field havoc once replaced the
owning object rather than its projected field. Ordinary calls, method calls,
and constructors now share `havoc_mut_borrow_args`, and checker/VCgen place
decoding is shared, but the Rust generator was still the only authority saying
that its fresh term reached the environment the continuation reads.

The first certificate needs to check real compiler output, fail closed, and be
small enough that its assurance claim stays honest.

## Decision

`compiler/src/transition.rs` defines a stage-neutral `CallTransition`: the
shared `Place`, referent `Ty`, source span, and `HavocUniqueBorrow` effect. Its
constructor admits the currently meaningful call-havoc referents — arrays,
classes, and resources — and returns a named internal refusal for every other
shape. This first certificate slice did not migrate checker call effects; the
follow-on handoff is decided separately in ADR 0088.

After `havoc_mut_borrow_args` writes a fresh value back, it reads the target
place from the live symbolic environment and attaches an emission witness:

- `fresh`: the binder created for the callee's post-call state;
- `observed`: the value now stored at the whole or projected target place;
- for arrays, `before` and the exact fresh-length = before-length hypothesis;
- the actual binders and hypotheses in scope at that transition.

`lean/Sable/Transition.lean` defines `CallHavocWriteback` and
`ArrayCallHavoc`. `compiler/src/lean.rs` emits one fixed-proof theorem per
symbolic-visit certificate. The write-back field must close by definitional equality; the
array length field must use the exact recorded hypothesis. Certificate
theorems have their own artifact-name set, are hashed and checked with the
ordinary generated document, and cannot be targeted by `defer`, `assume`, or
`discharge`. A rejection maps to
`internal.transition_certificate_rejected` at the call argument.

The Lean theorem identifier is an injective, versioned encoding of separately
length-framed semantic components: typed callable owner, resolved call target,
raw structural place, body-relative call span, parameter index, and deterministic
symbolic-visit ordinal. It never sanitizes the place before encoding. Artifact
preparation also rejects a declaration emitted by the root artifact whose Lean
name is owned by an import (including a cross-category collision) before
category-specific name subtraction runs. Emission ownership is not inferred
from source span alone: an importer-demanded generic instance retains its
dependency template's span but is root-owned when no dependency supplies its
exact same-category declaration.

The producer also refuses before emission when a fresh binder, target
post-state, array pre-state, or exact length hypothesis is absent or
inconsistent. These refusals are a defense in depth; Lean remains the check
that the emitted terms and theorem actually typecheck.

## Evidence

Production generation tests require a real checked mutable-array call to emit
an `ArrayCallHavoc` theorem even when its name is placed in the ordinary skip
set. Focused tests cover whole-array and projected resource targets and the
unsupported-shape/exact-length refusals.

A branch/join regression reaches one source call from two symbolic paths and
requires both havocs to emit distinct visit-keyed certificate theorems. An
artifact regression requires an importer-demanded generic class whose cloned
span points into its dependency to remain root-owned, then rejects an imported
ghost with that concrete structure's exact Lean name.

A two-module regression constructs the former sanitize collision between an
imported `(foo, bar_call_havoc_baz)` certificate and a root
`(foo_call_havoc_bar, baz)` certificate, and requires the distinct root theorem
to remain in the emitted artifact.

The adversarial regression starts from that real checked call, changes only
the certificate's observed post-state back to the actual pre-call sequence,
runs Lean over the generated artifact, and requires the mapped internal
certificate rejection. Real corpus checks cover array, class, resource, and
resource-field write-back.

## Consequences and boundary

This certificate checks that a recorded unique-borrow call transition writes
the selected fresh term to the selected place. For arrays it also checks that
the emitted length fact relates that fresh term to the actual pre-call term.
With ADR 0088, the checker selects that transition for each explicit
unique-borrow argument and VC generation validates its immutable record on
every symbolic visit, while requiring every checked site to be visited at least
once. The certificate rejects the historical stale-state and wrong-root write-back
shapes for a recorded transition.

It does **not** prove that the checker found every relevant effect, that the
source expression was translated completely, that callee posts or all
fresh-state facts are correct, or that moves, loans, receivers, loop havoc,
cleanup, traps, and scope exits share a validated transition system. The Rust
checker and generator remain trusted for those decisions. ADR 0090 closes C0
criterion 2 at that trusted checker-to-VC boundary; the certificate itself does
not establish the closure. ADR 0092 separately closes criterion 3 with a trusted
shared control/action model; that closure likewise does not broaden this
certificate's kernel-checked claim.
