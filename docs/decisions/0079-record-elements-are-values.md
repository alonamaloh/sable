# ADR 0079 — record elements are values

**Decided 2026-08-18.** `[record]` — an owned array of POD records — is a
type: locals, element reads and stores, `&[record]`/`&mut [record]`
parameters, and init `&[record]` parameters, verified, executed, and
monitored. `docs/type-matrix.md` opens `record` × `array element` and adds
the `[record]` row (67 of 163 → 72 of 180 intended; the denominator grows
with the row, whose `never` set mirrors `[u64]`'s).

## Context

Records existed at every layer — checker type, `Val::Record` with emitted
Lean structures and `wf`, `RtVal::Record` in the payload-generic runtime
array, `SpecVal::Obj` in the monitor, `Val.record` in the formal machine —
and the array machinery was already element-generic after the
representation folds. What refused `[record]` was the payload family
alone. The slice therefore split ADR 0077's classification by container:
`PayloadFamily::Record` is admitted by the array gates and refused by the
option gates, each in its own name, with the groundwork commit answering
every wrapper with its prior diagnostic first (snapshot byte-identical).

## Decisions

1. **A record element is a copyable value, not a place.** Elements are
   read and written whole (`Pt p = a[i];`, `a[i] = Pt(…)`); `a[i].x` has
   no spelling in either direction, consistent with the place engine
   (ADR 0023: a place is a root plus fields, no index component), and
   both spellings are corpus-pinned as parse refusals. Contracts project
   freely: `(a.get k).x` is ordinary Lean.

2. **Elementwise well-formedness is the array's element fact.** Where an
   integer array carries a range quantifier, a record array carries
   `∀ k, 0 ≤ k → k < a.len → R.wf (a.get k)` — every record a program can
   store was built through the checked constructor — emitted by the same
   single dispatch that serves every havoc site, and assumed pointwise at
   each proven-in-bounds read. The emitted record gains
   `@[simp] theorem wf_iff` alongside its `wf` definition: a plain `def`
   is invisible to `simp` (the standing automation lesson), and the
   unfolding lemma is what lets a discharge read field bounds out of a
   `wf` hypothesis.

3. **Class fields wait behind their own name.** `type.record_array_field`
   keeps `[record]` out of class fields until the field-element paths
   (`FieldStore`, `ClassFieldIndex`, `SelfFieldIndex`) generalize — the
   `type.bool_array_field` precedent, and mandatory here because two of
   those paths would otherwise panic or misbrand rather than refuse.

4. **The machine leg is separate.** The formal SVM's arrays are already
   `Val.arr (elem : ValTag) (a : Seq Val)` (ADR 0062) and record values
   exist; what remains is a `ValTag` arm carrying the record's
   declaration tag, its `Val.tag?` admission, and svm-diff subjects — a
   follow-up commit under ADR 0017's discipline. Until then
   `svm.aggregate_payload_unsupported` stands, and `corpus/svm-diff/`
   holds no record arrays.

5. **Off-range junk stays unanswered.** `Sable.Seq`'s `get` is total with
   *unconstrained* junk — there is no Lean-side default record to mirror
   — so the monitor keeps no record answer in `SpecVal::default_of`, and
   an out-of-range record-element clause read is a loud
   `monitor.no_junk_value` skip rather than an invented value that could
   diverge from the proofs.

6. **Position names sharpen as the payload gate steps aside.** Returns
   answer `type.array_return`, trait members
   `type.trait_param_unsupported`, exposure `expose.element_type`, member
   params `type.member_param`/`type.param_unsupported` — each boundary
   now refuses in its own name where the payload gate refused first
   before, and each flip is corpus-pinned.

   > **ADR 0085 supersedes two of those names.** A return no longer
   > refuses an array at all; a class-method result answers
   > `type.member_array_return`, and `type.param_unsupported` has left the
   > member-parameter pair, which `type.member_param` now closes alone.
   > The decision this item states — each boundary refusing in its own
   > name, each flip corpus-pinned — is what that change followed.

## Consequences

`corpus/verifies/record_array.sable` (36 obligations: the elementwise wf
fact load-bearing in an overflow VC, whole-element equality posts through
a `&mut` swap, a quantified fill-loop invariant over element fields, and
a class init taking `&[record]`) with a zero-skip tests twin, seven
must-fail pins, two test-fails twins, and a same-lean loop-havoc pair
whose dead value is a scalar seed — an array's alloc-fill value is *not*
dead (it survives into loop-entry obligations), which the pair harness
itself taught during authoring. Two hand discharges remain (the wf
unfolding into `omega`, and the get/set case split under a quantified
invariant): both are shapes for the planned tactic work.
