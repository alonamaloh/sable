# ADR 0078 — option nesting is the recursive family

**Decided 2026-08-18.** `option<option<T>>` is a type, at any depth, for
concrete value leaves: nested copyable options declare, construct, guard,
prove, execute, monitor, and lower through the formal machine wherever
flat options go — locals, returns, and plain function parameters.
`docs/type-matrix.md` opens exactly `option<u64>` × `option payload` and
`option<bool>` × `option payload` (65 → 67 of 163 intended).

## Context

`option<option<T>>` was one of the founding examples of the
representation problem this campaign exists to fix — inexpressible under
the deleted `ValueTy`, and after the representation folds, refused only
by gates. The groundwork was already recursive: the formal machine's
`Val.opt : Option Val` since the SVM value fold, the interpreter's
`RtVal::Opt`, Lean's `Option` itself, and the junk model composes —
`.value` of an absent option of options is `none`, whose own `.value` is
the junk one level down. This is also the first widening through
ADR 0077's classification, and it exercised the design as intended: the
new family variant made every wrapper a compile error until each stage
answered deliberately.

## Decisions

1. **`PayloadFamily::OptionOfValue`, at any depth.** An option payload is
   admitted exactly when its own payload is `Value` or `OptionOfValue`.
   Depth is not a property any stage limits, because everything below the
   classification composes per level (Lean types, value-chain facts,
   runtime and machine values, junk); a depth cap would be one arbitrary
   line, so instead depth three is pinned by corpus and admission
   samples. Everything else stays out with its own family: an abstract
   inner payload keeps `type.option_payload_unsupported` even inside a
   template whose instantiations would all be concrete, and the affine
   family does not nest in either direction.

2. **The family splits by container.** The option wrappers admit
   `OptionOfValue`; the array wrappers refuse it in their own names — an
   element is a place a store can name one of, and no stage has
   per-element option storage. In VC generation the split includes the
   position gate: a parameter transports the recursive family, a class
   field stores flat value payloads only, and the two conditions are
   stated apart so the positions cannot drift together.

3. **Nesting transports; it is not stored or bound by members.** Class
   fields keep `type.option_field`, init/method parameters keep
   `type.member_param`, trait members keep their refusals — each now
   answering in its own name where the payload gate refused first before.
   The interpreter's class-field gate deliberately stays wider than the
   checker's (it answers executability, not language policy), the same
   relationship every interp gate has to check's position rules.

4. **One value chain, one fact.** A checked nested option state carries
   exactly one range fact, at its integer leaf, over the composed
   `.value` chain — emitted by one recursive helper at parameter entry
   and both call-return sites (after the posts, preserving the
   motive-capture discipline). Sound by the junk model's induction level
   by level.

5. **The junk chain reduces by simp.** Core Lean states
   `Option.default_eq_none` without the simp attribute; the prelude marks
   it. That one attribute made the entire junk-composition obligation
   class automatic — no discharge in the corpus reads a junk chain by
   hand — which is this slice's down payment on the tactics-investment
   direction: the right lemma beats a per-subject script.

## Consequences

`corpus/verifies/nested_option.sable` (53 obligations: guarded
double-reads with both someness VCs, the composed range fact
load-bearing, junk-provable pres for `none` and `some(none)` callers,
`option<option<bool>>`, depth three) plus a zero-skip tests twin, four
must-fail + three test-fails negation twins (the inner and outer traps
are distinct, and `some(none)` refutes outer-implies-inner), a same-lean
naming pair, and `corpus/svm-diff/nested_options.sable` — the first
container slice with a formal-machine differential leg, because the
machine was already recursive. The repurposed
`corpus/must-fail/option_payload_option.sable` pins the template
refusal; `option_payload_option_array.sable` keeps the affine nesting
out. Arrays of options remain closed at every gate.
