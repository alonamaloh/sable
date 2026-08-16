# ADR 0071 — a backend lowering answers rather than aborts

**Decided 2026-08-16.** Removes the last place where a compiler-internal
disagreement ended a Sable compile with a process abort instead of a
diagnostic.

## Context

`llvm::llvm_ty` and `llvm::type_code` mapped a checked `Ty` to its LLVM
spelling and ended in `unreachable!`. They were not gates: the backend's
refusals are issued earlier, by `require_runtime_type`, `require_local_value`,
and `require_parameter_value`, each of which returns a named, spanned
`backend.*` diagnostic. The lowerings ran only after one of those said yes, so
the panic rested on an implication — *admitted implies lowerable* — rather than
on an argument about the parser.

That implication was checked. `shape_admission::llvm_lowering_is_total_on_
admitted_shapes` handed every sampled shape to a gate and, when the gate
admitted it, to the lowering inside `catch_unwind`, so a widened gate that
forgot to teach the lowering failed a test instead of aborting a user's
compile. But `docs/shape-admission.md` deliberately probes stages *without the
parser in the way*, precisely because "no source program reaches this" is an
argument about the grammar and the grammar is not what the table measures. A
lowering that answers a question with `abort()` is the one stage that could not
be given a column, and the sampled shapes it panicked on outnumbered the ones
it lowered.

The cost of that arrangement is not theoretical: the failure mode it permits is
a compile that ends with no message, no name to match on, and no `.sable` span
— the exact opposite of what every other Sable diagnostic promises.

## Decision

**A lowering answers.** `llvm_ty` and `type_code` return `Option<String>`.
Every `Ty` gets an answer, including the shapes the backend has no
representation for and including `Ty::Int` still carrying an unsubstituted type
parameter.

`None` becomes a diagnostic at the point of use, through `require_llvm_ty` and
the signature mangler, both of which carry a span and a role:

    internal.backend.type_lowering
    no LLVM value type for a shape the backend admitted
    parameter `handle` has type `resource OpenFile`, which a backend gate
    accepted and the value type lowering cannot spell

The name is `internal.`-namespaced, and that is the honest label. It does not
describe a program that is wrong; it describes a gate and a lowering that
disagree, which is a compiler bug. No `corpus/must-fail/` subject can pin it,
because no source program reaches it — a unit test asserts the exact name, the
span, and the role instead, as the corpus convention requires for an
`internal.` name.

**The implication is still the intent.** `llvm_lowering_is_total_on_admitted_
shapes` keeps checking that no shape any gate admits ever needs that
diagnostic; it now reads the lowering's answer instead of catching its panic.
A second test hands every sample to both lowerings and requires only that they
return, which is the totality property itself. The first test is the one that
must keep passing; the second is what makes the first's failure a bad
diagnostic rather than a crash.

**Spans come from the declaration, not from a guess.** A parameter reports at
its own span, a record or class field at the field's, a local at its function's
name span, an argument at the argument's, a return type at the function's name
span. Every site that lowers a type had one of these already; none was
invented.

## What this deliberately does not cover

`IntTy::bits`, `IntTy::min`, `IntTy::max`, and `integer_type_code` still panic
on an unsubstituted integer type parameter. They share one contract —
post-monomorphization only — enforced by `require_concrete_integer` at every
backend ingress and by mono's exhaustive rejection of a parameter left in an
ordinary declaration. `integer_llvm_ty` is the emitter's one-line participant
in that contract and says so; the twenty-odd sites that spell an integer width
call it rather than routing a width through the shape lowering.

Folding those into this change would have meant threading a result through the
trap-metadata packer and the Euclidean-correction helpers to remove a panic
that is guarded by a different, already-stated invariant. That is a separate
decision about `IntTy`, not about shape lowering, and it is not made here.

## Consequences

`ModuleSupport::emit`, `emit_record_type`, `emit_main_bridge`, `mangle`,
`mangle_initializer`, and `mangle_method` return results. Nothing about the
emitted IR changes: this is plumbing, and the differential subjects and the
`llvm_cli` fixtures produce the same bytes they did.

`docs/shape-admission.md` gains no column. The lowerings are not gates and
still have no cell; what changed is that the note explaining why now describes
a total function rather than a panic.
