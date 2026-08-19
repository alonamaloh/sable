# ADR 0092 — structured control is sealed without claiming an expression CFG

**Decided 2026-08-19.** Structural reachability is planned before body
typechecking, then the exact outline is enriched and sealed after checking.
The checker consumes the outline; proof, formal-machine, interpreter, and native
paths consume its retained typed form. None reconstructs control flow from
statement syntax.
Together with exact replacement and temporary-cleanup actions, this closes C0
criterion 3 and the consolidation gate without claiming a full expression CFG.

## Context

ADRs 0089 and 0091 established stable lexical scopes, cleanup routes, compiler
temporary identities, and an exact `ControlProgram` carrier. Follow-on work made
VC generation and the formal SVM consume that carrier too. Several structural
decisions nevertheless still began in later AST walks: whether a statement was
reachable, whether a branch arm or loop body could fall through, how an
exposure's normal epilogue was ordered, and which proof effect record belonged
to a loop or exposure.

That split was unsafe in both directions. Building the plan only after checking
could let an internal stable-key collision mask the source diagnostic that
checking should have reported first. Recomputing reachability later could let a
mutated checked AST present a different continuation to one consumer. A generic
empty trap route likewise stated the no-unwind policy without proving that each
source operation used the exact retained trap identity.

The remaining structure had to move without pretending that `BodyPlan` is an
expression CFG or that dynamic runtime representation belongs in a shared
static plan.

## Decision

### A total pre-check outline

`ControlOutline` is built for each callable before its flow-sensitive checker
walk. Construction is total over the parser AST and records:

- stable block, scope, branch, loop, and exposure identities and parentage;
- one `StatementPlan` per source statement, including its structural role and
  whether its entry is reachable;
- block and statement `FlowSummary` values for fallthrough, reachable returns,
  and returns anywhere in a nested body; and
- branch-arm, loop-body, `unsafe`-block, and exposure-body structure.

The checker consumes this outline for reachability, branch/loop flow, and the
structural exposure-return rule while it performs ordinary typing and affine
state checks. Because the outline has no failure path, source diagnostics remain
authoritative. Only after checking succeeds does `ControlProgram::seal` reject
ambiguous stable identities or typed-plan inconsistencies.

`BodyPlan` retains the exact outline rather than rerunning its analysis. It adds
typed scopes and bindings, `DropId` candidates, compiler temporaries, return
routes, local/field replacement and discarded-temporary actions, trap sites,
and typed structured edges:

- `BranchPlan` records both arms, each arm's flow, and a normal exit route only
  when that arm reaches the parent continuation;
- `LoopPlan` records header/body identity, body flow, an optional backedge, and
  the exact `EffectSiteKey` of its checker-authored `CheckedLoopEffects`;
- `ExposurePlan` records body flow, the exact `CheckedExposure` key, and—only
  on a normal edge—the ordered capture → body exit → rebuild/copyback → loan
  release → compiler-scratch close sequence; and
- retained block plans distinguish structural blocks from lexical scopes, so an
  `unsafe` block has a block identity while remaining scope-transparent.

The checker uses the corresponding outline flow and structure. VC generation,
SVM lowering, interpretation, and LLVM lowering use their retained typed form.
Syntax-based flow summarization remains only in deliberately unsealed test
helpers.

### Exact replacement and temporary-cleanup actions

The sealed plan carries the remaining cleanup-bearing statement policies:

- `AssignmentAction` fixes a local destination, checked type, previous
  `DropId`, checker-authored `ValueTransferKey`, and direct or compiler-
  temporary staging;
- `FieldAssignmentAction` fixes the `self.field` destination, checked type and
  transfer key, whether an old dynamically present value must be dropped, the
  staging identity, and an optional concrete-class cleanup link; and
- `TemporaryDropAction` fixes the type, checker-authored discard-transfer key,
  source-inexpressible compiler destination, and mandatory class cleanup for a
  discarded fresh class result.

`ClassDropAction` links a statement action to one concrete `ClassDropPlan` and
repeats its canonical empty terminal route. `ControlProgram` centrally resolves
and validates every such link after sealing. The semantic order is retained:
evaluate fully into staging, conditionally destroy the old destination, then
install; or, for a discarded result, evaluate into its compiler temporary and
destroy it before the following statement. A trap during evaluation or any
class-drop phase skips the remaining suffix without unwinding.

### Complete callable reconciliation

Every downstream production consumer first resolves the exact flavor-preserving
`CallOwner` and declaration span. `BodyPlan::validate_callable` first reconciles
the complete retained structural graph: exact block identity, parent, scope,
kind, and anchor; statement kind, entry reachability, and flow; branch arms,
optional `else`, and normal routes; loop condition, body, optional backedge, and
effect key; and exposure owner/use span, type, mutability, bindings, effect key,
and ordered normal actions. It then checks ordered source bindings and types,
drop candidates, every local/field replacement and discarded-temporary action,
their transfer/staging/drop identities, return sites and result slots, compiler
temporaries, and the complete trap ledger. Deleting or moving an unreachable
node is therefore still a mismatch; reachability does not excuse structural
drift.

There is no production fallback that silently builds a new plan from a checked
AST. Test-only unsealed entry points are named and carry no proof provenance.

### Exact consumers

The shared facts have deliberately different operational consumers:

| Planned fact | Production consumers |
|---|---|
| block/statement flow and structured branch/loop/exposure identity | checker from `ControlOutline`; VC, SVM, interpreter, LLVM from sealed `BodyPlan` |
| lexical fallthrough, backedge, exposure-close, and return routes | VC, SVM, interpreter, LLVM |
| checker ownership/mutation effect keys on loops and exposures | VC, paired exactly with `CheckedOwnershipPlan` |
| local `AssignmentAction` | VC; SVM for its admitted direct subset; interpreter and LLVM |
| `FieldAssignmentAction` | VC; interpreter; SVM and LLVM before admitted lowering or named subset refusal |
| discarded-class `TemporaryDropAction` | VC; interpreter; SVM and LLVM before named subset refusal |
| direct expression/statement `TrapSite` | VC, SVM, interpreter, LLVM |
| action-to-`ClassDropPlan` link | centrally at seal; interpreter, SVM, and LLVM at exact use sites |
| concrete `ClassDropPlan` execution | interpreter and LLVM for their admitted runtime subsets |

VC generation uses branch, loop, exposure, and return plans to select symbolic
continuations. Applying a route removes dead names and their type/entry-state
metadata while preserving historical binders and hypotheses. Loop havoc and
exposure ownership reconstruction use the checker-authored effect records named
by the structured plans, rather than a second syntax scan.

VC generation also consumes each retained replacement/temporary action through
its exact `ValueTransferKey`. It authenticates destination, type, staging,
conditional cleanup, compiler temporary, concrete class, and terminal route.
Destruction itself is a proof-state no-op: the normal symbolic state needs only
the installed field value, while a discarded fresh result has no source name to
remove.

The formal SVM consumes exact scope exits, explicit return result slots and
routes, exposure scratch/normal-close actions, admitted direct assignments, and
every direct trap site it lowers. It exact-consumes field replacement and
discarded-class actions—including their concrete terminal cleanup links—before
its existing class-subset refusal. Its `scopeExit`, `moveLocal`, and `retUnit`
semantics remain kernel-related to the executable evaluator.

The interpreter executes local and field replacement plus discarded-class
temporary cleanup from the retained actions. LLVM executes admitted local and
fixed-owner field replacements, including staged class/`u32`-array RHS values
and null-safe old-slot cleanup. LLVM currently refuses a discarded class result
after exact-consuming its temporary and class-drop action. Executing consumers
evaluate the RHS before dropping a dynamically live old destination and
installing the staged value.

Every admitted direct source trap site has an injective semantic key and the
canonical empty `Trap` route. Consumers look up the site immediately before the
corresponding operation; recursive expression evaluation consumes child sites
only if evaluation reaches them. Thus short circuiting does not consume a trap
that did not execute, while whole-callable reconciliation still rejects a
deleted unreachable site. Trap payload construction remains stage-specific;
the shared fact is exact identity and no-unwind control.

`ClassDropPlan` is concrete-class-only. It seals exact class/invariant/field
shape and the order invariant check → optional canonical deinitializer → every
field in reverse declaration order, with one empty terminal trap route for any
failing phase. The interpreter keeps dynamic moved-field presence and removes a
field before recursively dropping it. LLVM keeps its null/neutral slot model,
erases an invariant already authorized by verification, and rejects nonempty
deinitializers or field shapes outside its native subset.

## Evidence

Structural tests mutate retained callables by deleting or moving scopes,
branches, loops, exposures, returns, local/field assignments, discarded
temporaries, compiler temporaries, and trap sites and require named internal
refusals. Separate tests pin branch-arm reachability, optional loop backedges,
exposure normal-action order, effect-key matching, replacement/discard transfer
links, stable staging, terminal no-unwind recipes, and exact concrete class-drop
shape.

VC regressions require dead branch/exposure names to leave later clause scope and
early-return paths not to corrupt sibling symbolic state. SVM tests consume
direct expression and statement trap sites as well as route and action
identities. Interpreter regressions execute field replacement and discarded
temporary cleanup, including RHS/deinitializer traps. LLVM regressions pin
staged class/array field replacement and exact consumption before its refusal
of a discarded class. Other interpreter/LLVM regressions cover nested returns,
loop
backedges, exposure close, moved destinations, exact trap identities, and
recursive class cleanup. The real corpus subject that mentions an
exposure-local name after close must fail in clause elaboration.

## Closure and boundary

ADR 0086 criterion 3 is closed. `BodyPlan` is one retained structured typed
control/action model with zero production syntax-flow reconstruction and exact
coverage of the admitted structural edges, lexical exits, direct traps,
replacement/temporary-cleanup sites, and concrete class destruction policy.
Together with the separately closed checker-to-VC ownership/effect handoff of
ADR 0090, all six C0 criteria are complete.

This closure does not require static data to impersonate runtime state. Dynamic
reachability of an initialized slot, moved-field presence, native null/neutral
storage, and concrete value representation remain consumer state; the shared
plan decides which action and ordering apply. Nor is `BodyPlan` a full
expression CFG. A stage may exact-consume an action and then fail closed because
the value shape is outside its admitted subset.

This decision does not mechanize source-to-VC or source-to-SVM translation
soundness, widen the formal or native admitted subsets, or turn the Rust
compiler into an untrusted certificate producer.
