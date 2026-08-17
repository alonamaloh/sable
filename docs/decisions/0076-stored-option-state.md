# ADR 0076 — stored option state

**Decided 2026-08-18.** A copyable option with a concrete value payload is a
class field: `option<u64>`-family and `option<bool>` fields declare, store,
read, prove, execute, and monitor end-to-end. `docs/type-matrix.md` opens
exactly `option<u64>` × `class field` and `option<bool>` × `class field`
(63 → 65 of 163 intended).

## Context

Nullable state in a class is the most common shape real programs could not
write: a cache slot, a pending entry, a last-seen value. The option family
already crossed every value boundary — locals, returns, plain and member
parameters — and the class-field cell was the flagged next boundary. The
groundwork was ADR 0074's discipline applied to field state: the four
dispatches that produce a class field's symbolic state were made explicit
and fail-closed first (no cell moved, type-snapshot byte-identical), so
this opening replaces named latches rather than wildcards.

## Decisions

1. **The gate is payload-driven, and it is the checker's own fence.**
   `class_field_ty` admits `Ty::Option` with a concrete integer or `bool`
   payload; an abstract payload (`option<T>`) keeps `type.option_field`.
   Monomorphization instantiates template fields *before* the checker runs
   and recurses into option payloads, so no earlier stage re-answers this:
   deleting the arm would fail open. `corpus/must-fail/
   option_field_generic_payload.sable` is the surviving refusal's first
   corpus fence. A template's *concrete* option field is admitted and
   template-verified (`Slotted<T>` in the verifies subject).

2. **The field accessor surface is the option accessor surface.** The
   parser's self-field primary no longer consumes a trailing accessor dot,
   so `self.f.is_some`, `self.f.value`, and `self.f.take` reach the same
   postfix accessors every option expression has. `.take` on a field lands
   in the existing `option.take_not_local` refusal — affine extraction
   mutates its source local, and a field is not one. `.len` stays the
   field-level array accessor, and an unknown accessor keeps
   `parse.unknown_field` with the widened label.

3. **The stored state carries the payload's range fact.**
   `push_class_state_facts` emits `h_field_<name>_range` over
   `(state.f).value` for integer payloads, mirroring what a fresh option
   parameter carries. Sound under ADR 0008's junk model by the same
   induction: every store writes a checked value, the absent case reads
   `getD default = 0`, in range for every integer type, and whole-object
   states arise only from checked init and method exits. Without this fact
   a havocked receiver's field payload would be the one option value in
   the system with no range hypothesis.

4. **External field reads stay closed.** `obj.f` on an option field keeps
   the existing Int/Param-only external-read surface (`not yet`, not a
   decision): borrowed access goes through methods or a field borrow
   passed on, exactly as class-valued fields do today.

5. **The interpreter's field gate splits by container.**
   `validate_interp_class_field_ty` admits what parameters admit; record
   fields keep `interp.option_position_unsupported` — a record is explicit
   byte layout, and a value option has none. The record-side refusal is
   unreachable from source (check refuses record option fields first) and
   is pinned by a unit test rather than a corpus subject: recorded here as
   a knowing waiver of the executable-documentation convention,
   defense-in-depth for raw `Program` callers.

6. **The monitor's match scrutinee admits `old` paths.** `match old
   self.f with …` is monitorable: `match_opt` accepts an `old`-prefixed
   dotted path, evaluated against the entry snapshot. The corpus pins it
   in both directions (a verified `take_hit` contract and a refuted
   `drain` twin).

## Consequences

Init-loop field havoc is conservative — every field is freshened at the
loop head, so a loop invariant must carry even an unassigned field's frame
(`self.limit = m` in the verifies subject's `sweep`). That is existing
havoc design observed at a new field type, not a new rule.

The corpus battery: `corpus/verifies/option_field.sable` (122 obligations
across init/method/deinit state, both loop branches, `option<bool>` and
signed payloads, a template instance, a nested class-valued field, and a
destructor branching on the stored option), an importing module, a
zero-skip tests twin, four must-fail + three test-fails negation twins,
and two `same-lean` pairs (field-vs-local naming; loop havoc erasing the
dead pre-loop field value). The formal SVM has no class-member leg, so no
svm-diff subject can exist; the LLVM backend keeps every such class behind
the fixed-owner fences.
