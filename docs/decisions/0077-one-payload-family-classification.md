# ADR 0077 — one payload-family classification, eight per-stage answers

**Decided 2026-08-18.** The copyable container-payload gates — what an
array element or a copy-option payload may be, asked by the checker, VC
generation, the interpreter, and the SVM lowering, once per container
kind — share one classification: `Ty::payload_family`, answering `Value`
(concrete integer or `bool`), `Param` (declaration type parameter under
the ADR 0009 abstract-integer model), `Noncanonical` (`IntTy::TParam`),
or `Unsupported`. Each stage keeps its own named gate, its own refusal
name, and its own message; what it no longer keeps is its own copy of the
family split.

## Context

The eight gates were four hand-copies of one three-way classification,
differing only in whether `Param` is admitted (the proof-side stages
verify templates; the executable stages never see one). The blessed
shape-admission table proved the agreement, but agreement by parallel
maintenance is exactly the arrangement that produced the campaign's
false proofs (ADR 0074): the day a container-payload cell opens —
`[record]`, `option<option<T>>`, nested arrays — a widening applied to
three copies and not the fourth would let a shape into stages with no
semantics for it, and the admission table would report the divergence
only after the fact. This is the R2 gate the 2026-08-16 audit ordered
before any container-payload cell opens.

## Decision

`Ty::payload_family` in `ast.rs` is the one place a payload family is
recognized; it is exhaustive over `Ty` with no wildcard, so a new
constructor fails to compile until classified. The eight gates match on
the family: widening a family (or admitting a new one) is a change to the
classification plus a deliberate per-stage decision at each wrapper —
`Value` is admitted everywhere, `Param` only by check and VC generation,
and a stage that cannot serve a family the classification admits must say
so in its own arm, in its own name. The owning payload families
(`option<[T]>`, `option<raw<R>>`) keep their separate gates: affinity is
a different question with different rules, not a wider allow-list.

## Evidence

Behavior-preserving by the type-snapshot oracle: `lean.snap` — which
pins obligation emission order — is byte-identical over the corpus, the
diagnostic multiset is identical, and both blessed admission tables
match their probes without re-blessing. (The diagnostic snapshot's
line *order* for one must-fail subject shifted between binaries:
failing obligations are reported in completion order, which is stable
per binary but not across builds — a snapshot-tool brittleness worth
fixing separately, not a semantic change.)
