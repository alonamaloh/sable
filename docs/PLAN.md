# Sable plan

*Provisional, 2026-08-20. Evidence may reorder this plan.*

The current goal is a coherent, pleasant, trustworthy language—not more
surface area or backend breadth. For the next phase, a feature is primarily
complete when it verifies and runs in the checked interpreter. We will fill a
deliberately chosen part of the type × context matrix, reduce duplicated
semantic authority as we do so, and improve diagnostics and proof authoring
continuously.

LLVM remains in the repository but is parked. The formal SVM remains an
independent semantic oracle, but parity with every source-language feature is
not a completion requirement during stabilization.

This file is intentionally a forward-looking plan rather than an implementation
journal. The former milestone record remains available with:

```sh
git show cbd99999990e04d2530591d169ab278c35002475:docs/PLAN.md
```

Settled reasoning belongs in [ADRs](decisions/), implementation detail in the
[architecture](ARCHITECTURE.md), exact current admission in the generated
[type matrix](type-matrix.md) and [stage matrix](shape-admission.md), and
soundness history in the [incident ledger](SOUNDNESS-INCIDENTS.md).

## Priority zero: seal proof ingress

**Release is blocked.** Before the fail-safe work, Sable accepted both `sorry`
in a user discharge and an extra `axiom` injected as a continuation of a user
theorem. In a minimized witness, Lean accepted the resulting theorem and the
checked runtime monitor rejected the proved postcondition (`result = 1` with an
actual result of zero). Sable reported `status: fully verified` for both
witnesses.

The Lean kernel did what it promises: it checked a term relative to the
constants in its environment. The broken Sable claim is that every trust
dependency in that environment had been accounted for. Until this boundary is
sealed, existing Stage 1 results remain useful compiler/proof evidence but do
not qualify for the `fully verified` label or support a release claim.

The repair is an outcome gate, not a token blacklist. Three fail-safe tranches
are active. Generated-only and Lean-accepted-but-unaudited results carry
distinct assurance states, and every unrecognized Lean warning fails root,
imported-module, and proof-environment verification before an artifact can be
published. A separate trusted parser executable now authenticates every
user-derived Lean term at end of input and every ghost as exactly one permitted
`def` or `theorem` with its expected head; comment metadata is single-line
encoded. This closes continuation commands such as `axiom`, `set_option`, and
`#exit`, as well as clause/comment escape routes, before generated source is
submitted to Lean. Proof-policy identity is exact in published environments,
artifacts, and stamps; proof-environment READY additionally binds the exact
sorted local `.olean` set and parser-auditor executable by SHA-256.

A second READY-bound executable now has a strict, source-side transport for an
observational `Lean.readModuleData` inventory (module/import flags, parallel
constant names and kinds/safety, code-generation names, and raw extension
family counts). It is deliberately dormant in verification: no candidate is
imported or replayed, no manifest is written, and this inventory grants no
cache authority or stronger assurance. It is scaffolding for the compiled
declaration-envelope audit, not that audit itself.

No current path can emit `fully verified`. Lean's declaration-level warning
remains fatal even when a syntactically permitted theorem locally suppresses
`warn.sorry`, but source confinement does not authenticate the compiled
declaration body or its transitive dependencies. The remaining gate is the
compiled declaration and dependency audit below:

1. Audit each generated module's exact compiled declaration envelope. It may
   contain only compiler-authored roots and a narrow, pinned set of structural
   elaborator auxiliaries attributable to those roots—never an extra axiom,
   unsafe declaration, public sibling, or unused private declaration.
2. Audit the complete transitive axiom dependencies of every accepted user
   theorem, obligation, discharge, fact, and certificate. `sorryAx` is
   forbidden everywhere, including approved model modules; source `sorry` and
   `admit` are therefore always fatal. An unavailable or incomplete audit must
   fail verification or produce a clearly lesser status, never `fully
   verified`.
3. Maintain the active source-confinement and fail-closed warning gates. Any
   parser-auditor failure is fatal, and any non-fatal Lean diagnostic must
   remain a structured, compiler-owned exception rather than an arbitrary
   warning substring.
4. Extend the active policy-bound cache identities and stamps with the final
   proof-trust manifest so an old or poisoned entry cannot bypass the complete
   audit.
5. Add root, imported-module, fact, discharge, environment-delta, warning, and
   cache-reuse adversarial regressions for `sorry`, `admit`, direct and
   continuation-line `axiom`, extra declarations, `set_option`, and indirect
   dependency on a poisoned theorem.
6. Record the incident and its exposure window, invalidate affected artifact
   versions, and rerun the corpus, mutation suite, and proof baselines under
   the sealed boundary.

The dependency policy must distinguish two permitted roots from one forbidden
class. Pinned Lean foundational principles are a versioned, explicit
allowlist. Repository-controlled formal models may add an axiom only through a
separate policy: each one is
individually named, confined to an approved content-hashed Lean module or
machine profile, included in the artifact trust manifest, and surfaced in the
assurance report. User-controlled axioms, axioms introduced through imported
dependencies outside those roots, and any occurrence of `sorryAx` are
forbidden. `Fully verified`
is possible only when the completed transitive audit succeeds and its exact
axiom set is a subset of this approved base. Permission for model axioms is not
permission for source proof blocks to introduce them, and it does not imply
that the current SVM needs an axiom.

## Development profiles during stabilization

### Primary language profile

This is the completion target for ordinary language work:

- parsing, modules, monomorphization, and type/ownership checking;
- VC generation and Lean checking;
- the checked interpreter and dynamic contract monitor; and
- diagnostics, LSP support, and proof-authoring workflows needed to use that
  path effectively.

Once priority zero closes, “supported by Sable” means supported coherently in
this profile unless a narrower profile is named.

### Formal semantic profile

Keep the SVM rules, functional evaluator, agreement proofs, and Rust/Lean
differential. Extend them when a stable behavior benefits from an independent
formal account or when the model exposes an ambiguity. Do not require the Rust
SVM bridge to accept every type/context cell, and do not describe its current
strict subset as the semantics of every source feature.

The longer-term target is a stable core semantics against which source
elaboration and VC soundness can eventually be stated. That theorem remains a
future stage; the current source-to-SVM bridge is trusted.

### Parked native profile

Keep LLVM compiling and retain a small canary suite for scalar control,
ownership transfer, cleanup, traps, allocation balance, and Clang `-O0`/`-O2`
agreement. Permit correctness, security, toolchain-compatibility, and
isolation fixes.

During stabilization:

- do not open new LLVM type, storage, call-ABI, or class-shape cells;
- do not make LLVM support part of a language feature's completion gate;
- do not pursue native performance or proof-directed check elimination; and
- keep the existing native timing results as narrow historical evidence, not
  as a performance promise.

The native `unsafe expose` refusal remains load-bearing. It may not be lifted
until native lowering enforces the owner's frozen-name rule and the selected
alias/copy model is represented in the machine rules, evaluator, agreement
proofs, and differential evidence.

## Foundations already worth building on

Sable already verifies substantial algorithms and supports contracts, loops,
modules, generics, traits, classes, arrays, options, records, resources, raw
memory, explicit external-world authority, owner slots, and deterministic
cleanup. `OwnerVec<T>` verifies and runs in the primary profile, including
owner-safe growth and recursive cleanup; its narrower SVM and native coverage
does not make that source-language result incomplete.

The checker already authors shared place identities, an ownership/mutation
plan, and a structured control/action plan that downstream stages consume
fail-closed. Narrow Lean certificates cover selected unique-borrow write-back,
successful local/direct-`self` slot take/put write-back, and the exact recorded
argument schedule. These are strong foundations, but Rust effect discovery,
source elaboration, VC construction, and certificate provenance remain
trusted.

The exact support frontier belongs in [the type × context matrix](type-matrix.md)
and [the shape × stage matrix](shape-admission.md), not in prose here. A closed
type/context cell is either `not yet` or a reasoned `never`; implementation
accidents must not silently become language decisions.

## How work will be chosen

The unit of work is a small vertical slice forced by a real program or API.
Each slice should:

1. name the exact type/context cells it intends to open;
2. settle evaluation order, ownership, mutation, cleanup, and trap behavior
   before admission;
3. add representation and fail-closed gates before the new source form can
   reach a consumer;
4. implement the primary language profile end to end;
5. centralize any semantic fact the slice would otherwise reconstruct in more
   than one stage;
6. add positive, named-negative, runtime, lifecycle, and metamorphic evidence
   as applicable;
7. give adjacent unsupported forms intentional answers and actionable
   diagnostics; and
8. update the generated matrices and user documentation.

SVM or LLVM widening happens only when a slice explicitly selects that
separate profile. A front-end `yes` does not by itself claim successful
verification, interpretation, formal lowering, or native lowering.

## Penciled sequence after priority zero

### 1. Select a stabilization matrix

Review every `not yet` cell, but do not mechanically open all of them. Choose a
compact target organized by type families and common contexts:

- locals, ordinary/member parameters, and returns;
- class fields and copy-container elements;
- option and slot payloads; and
- generic arguments.

Defer raw-storage geometry, resource-map variants, public/native ABI questions,
and exotic recursive containers until a concrete client forces them. Preserve
each current `never` unless its recorded reasoning is deliberately reversed.

The output is a small target table marking cells for this stabilization cycle,
later cells, and reviewed `never` decisions. Every selected group needs a
forcing example.

### 2. Establish one typed semantic core

Use “Sable Core” as a working name for the explicit typed representation that
all semantic consumers should eventually share. Before implementing it, decide
in an ADR whether to complete the retained control/action representation or
introduce a separate core IR.

The core must make these facts explicit rather than asking consumers to infer
them from source syntax:

- places and type-resolved values;
- receiver-first, left-to-right expression effects;
- loans, moves, replacement, mutation, and loop havoc;
- structured branches, loops, calls, returns, and traps; and
- lexical cleanup and destruction order.

This is a split by semantic authority, not a mechanical attempt to turn large
Rust files into smaller files. Source elaboration may remain trusted initially,
but checker, VC generator, interpreter, monitor, formal bridge, and any future
backend should consume one meaning. Exact reconciliation and closed
certificates should retire trust only where Lean receives an independently
meaningful carrier; generator-authored assumptions must not be renamed as
proofs.

Before step 3 or any later language slice begins, land one useful Core tranche
rather than only an ADR or data-structure skeleton. It must carry a real,
nontrivial existing control/effect/cleanup path from the checked program into
at least VC generation and the interpreter, replace their reconstruction of
that path, reconcile exactly with the checker authority, and have fail-closed
mutation and negative tests. Later slices may expand the Core incrementally.

### 3. Make ordinary values unsurprising

First address asymmetries users encounter in routine code: integers, Booleans,
records, copyable options, and copy-element arrays across ordinary calls,
members, returns, fields, and generic clients.

This phase should prefer common type-driven operations for call transport,
field state, loop havoc, monitoring, and diagnostics. It should not introduce
borrow locals; those require a real alias/lifetime model rather than another
special case.

### 4. Complete affine-owner composition

Build on `slots<T>` and `OwnerVec<T>` rather than making ordinary arrays copy
owners. Candidate boundaries include owned and borrowed parameters, returns,
class fields, affine options, slot payloads, generic owner arguments,
replacement, and recursive cleanup. The stabilization matrix—not this list—will
decide the exact slice.

Movement must go through one retained transfer/action authority. Every client
must demonstrate no fabrication, copying, accidental leak, double destruction,
or stale proof state across nested calls, branches, loops, returns, replacement,
and traps. An owner-capable map or another independent owner-bearing container
would be a useful second client after `OwnerVec<T>`.

No ownership-sensitive cell may open until the independent effect-sequence
generator described below is operational for the interactions that slice
selects. It may land alongside the first useful Core tranche, but admission
waits for generated legal and illegal sequences that do not reuse the
compiler's retained-plan oracle.

### 5. Exercise generic composition

Let forcing libraries choose the next language surface. Likely clients include
an owner-capable collection, a small `String`/formatting layer, and
`Result`-shaped error handling. Pattern matching is a temporary omission, not a
principle: introduce a small explicit form when richer sums make partial value
accessors worse than visible case analysis.

Generic proof reuse must be authorized only for the domain it proves. Owner
specializations should be checked independently where required, and clients
should not rely on declaration-specific compiler exceptions.

### 6. Reach a stable-language and release checkpoint

Complete this full checkpoint before any release tag. It is also a prerequisite
for reopening native-backend expansion:

- the selected stabilization matrix is complete;
- several substantial programs verify and run without backend-driven source
  restrictions;
- proof ingress is sealed and every known soundness finding is fixed or
  explicitly bounded;
- common failures have actionable source-level diagnostics;
- proof iteration is tolerable under the supported low-concurrency workflow;
- mutation, effect-sequence, differential, and adversarial evidence remains
  effective;
- an independent review by someone who did not participate in the design or
  implementation is complete, its report is published, and every finding is
  fixed or explicitly bounded; and
- several consecutive slices have not required redesigning evaluation order,
  ownership transfer, cleanup, or generic identity.

This is not a “zero bugs for N days” gate. Findings should be encouraged,
recorded, minimized, and dispositioned. Internal agent or participant review is
valuable but does not satisfy the independent-review release gate.

## Cross-cutting work

### Reduce the trusted base

- Prefer one total semantic operation or retained typed record over policy
  repeated across stages.
- Require exact consumption, one-to-one identities, and completeness checks
  for retained plans.
- Keep proof dependencies, imported artifacts, machine profiles, externs, and
  explicit assumptions visible in one authenticated trust manifest.
- Pursue the eventual Core-to-SVM/VC soundness result only against a stable
  core, not a moving source language.
- Keep the incident ledger and assurance nonclaims current.

### Improve diagnostics and proof ergonomics

- Lead with the rejected source construct, explain the semantic limitation,
  and suggest the nearest supported form.
- Distinguish a language decision from an unfinished interpreter, formal, or
  backend boundary.
- Preserve stable obligation labels and source provenance while reducing
  routine duplicated discharges.
- Improve multi-error recovery, scoped hover resolution, and asynchronous LSP
  verification rather than exposing internal stage vocabulary to users.

### Test effects, not only examples

Develop a small independent effect algebra covering borrow, move, replace,
mutate, nested call, return, trap, loop join, exposure, and drop. Generate legal
and illegal source programs from bounded sequences without reusing the
compiler's retained-plan oracle.

Keep alpha-renaming, insertion of unreachable independent owners, commuting
independent effects, proof/runtime post-state agreement, and reverse-order
controls as metamorphic properties. Continue expanding curated semantic
mutations, but never turn their result into a whole-compiler mutation score or
call a survivor globally equivalent.

### Keep proof work operationally bounded

Default to serial proof work and never exceed two external Lean compiler
processes. Use focused gates during development and the established provenance
protocol for periodic corpus, mutation, native-canary, and proof-timing
baselines.

## When LLVM may resume

Reconsider native expansion only when:

- the selected language surface and typed core are stable;
- lowering can consume explicit evaluation order, effects, traps, and cleanup
  rather than rediscover them;
- ABI choices are deliberate instead of accumulated shape exceptions;
- proof facts used to remove checks have authenticated provenance; and
- the team is prepared to decide whether adapting the textual emitter or
  replacing it is cheaper.

Removing a check merely because trusted Rust currently believes it cannot fire
would recreate the duplicated-authority problem. Optimization should begin
only after the backend can consume facts whose origin and validity are
explicit.

## Later possibilities

These are directions, not commitments or current sequencing:

- broader standard-library work, real module namespaces, packages, partial and
  mutual recursion, and additional sum-type ergonomics;
- concurrency, atomics, and a defined memory model;
- generic MMIO, interrupts, DMA, richer device/ISA profiles, MMU and privilege
  models, and eventually verified runtime or OS experiments;
- floating-point semantics when a forcing application exists;
- wider formal-machine coverage and a mechanized source/Core/VC soundness
  story;
- translation validation or a verified native backend after the language is
  stable; and
- resumed LLVM ABI coverage and proof-directed optimization.

The existing UART profile, raw-memory discipline, explicit world authority,
allocators, bignum library, collections, and formal SVM are foundations for
those experiments, not promises that the corresponding larger systems are
already designed.

## Definition of done

After priority zero, a semantic slice is complete only when:

- intended matrix cells are open and adjacent cells have intentional answers;
- checker, VC/Lean, interpreter, and monitor agree on representative normal
  and trapping behavior;
- affine values move and are destroyed exactly once across every relevant
  exit path;
- no consumer silently reconstructs a semantic fact already carried by the
  typed core or retained plans;
- unsupported forms fail with stable, actionable diagnostics;
- positive, must-fail, dynamic, lifecycle, metamorphic, and mutation evidence
  cover the new interactions as appropriate;
- no proof escape, trust dependency, warning, or monitor skip is hidden; and
- generated matrices and user-facing documentation match the implementation.

## Sources of truth

- [README](../README.md): current capability and assurance summary.
- [Language design](design/sable-language-design.md): normative source
  semantics.
- [Architecture](ARCHITECTURE.md): current implementation and trust boundaries.
- [Type matrix](type-matrix.md): exact source type/context admission.
- [Stage matrix](shape-admission.md): exact per-consumer shape gates.
- [ADRs](decisions/): settled decisions and their reasoning.
- [Soundness incidents](SOUNDNESS-INCIDENTS.md): evidence-qualified failures.
- [Adversarial review guide](ADVERSARIAL-REVIEW.md),
  [mutation protocol](../tools/soundness_mutations/README.md),
  [native protocol](../tools/native_perf/README.md), and
  [proof-timing protocol](../tools/proof_timing/README.md): reproducible
  evidence and its limits.
- [Corpus](../corpus/): executable examples, diagnostics, and differential
  subjects.
- [Original goals and roadmap](design/sable-goals-and-roadmap.md): historical
  research ambitions, not the current sequence.
