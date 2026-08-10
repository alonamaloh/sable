# ADR 0018 — Separate verification: content-addressed per-module Lean artifacts

**Decided 2026-08-10 (Alvaro).** Implements the slice ADR 0013 planned
("emit one Lean file per module with `import` lines, so an imported
module's obligations are not re-checked per importer").

## Context

Modules v1 merged the whole import DAG into one generated Lean file, so
every check of an importer re-proved its dependencies' obligations —
every String client re-proved utf8's 205. The source-level linking
design was chosen so fixing this touches only emitter/checker plumbing,
and it did: the language, parser, checker, vcgen, and interpreter are
unchanged.

## Decision

**One generated Lean file per module, compiled to a content-addressed
artifact** at `.sable-out/modules/<stem>_<hash>.{lean,olean,ok}` and
verified once; importers `import` it through Lean's own module system.

- **Content addressing is the whole cache story.** The hash covers the
  module's generated content plus the prelude (Lean sources, toolchain
  pin, lakefile). Import lines name dep artifacts *by hash*, so an
  artifact name transitively pins everything its verification depended
  on, Merkle-style. Validity is mere existence: `.ok` is written only
  after a successful kernel-checked run that produced the importable
  olean; failures leave nothing behind. No mtimes, no invalidation
  logic, no staleness bugs — a changed dep is a different name.
- **Emission is name subtraction.** A module's file declares only what
  no imported artifact declares (classes, ghost defs, clause-wf defs,
  obligation theorems). Generic instances demanded by an importer land
  in the importer's file; everything a dependency proves is proven
  exactly once. This forced byte-stable generation — vcgen's scope
  binders are now name-sorted, since HashMap iteration order had leaked
  into loop-clause wf defs.
- **Roots always verify.** `sable check` runs Lean on the root's own
  file every time (its header is the stable `.sable-out/<stem>.lean`
  path so the daemon's warm-document reuse keeps working); only
  dependencies are consumed from artifacts. A verified root is stamped
  as an artifact too, so checking a dependency first (the corpus does)
  seeds its importers.
- **Diagnostics stay per-file.** Dep failures are carried as
  (file, module-local span) and re-rendered in whichever importer's
  coordinate space asked, so an error in an imported module still
  points at that module's own source, checked from anywhere.
- **The daemon stays warm and honest.** It spawns `lean --server` with
  the artifact directory on `LEAN_PATH`; because dep artifact names are
  content-addressed, the generated header changes exactly when a dep
  changed — which is Lean's own signal to reload imports. A daemon
  started before this slice reports unknown modules; the client detects
  that and falls back to the batch path.

## Flat-namespace guards

Separate verification makes silent cross-module shadowing possible
where the merged file previously produced a (confusing) Lean error, so
three conditions are now compiler diagnostics, each with a must-fail
program:

- `module.foreign_escape` — a `defer`/`assume`/`discharge` naming an
  obligation an imported module proves in its own artifact. Escape
  hatches live with the obligation.
- `module.name_collision`, extended to ghost definitions — a ghost
  redefining an imported name would otherwise be silently replaced by
  the import under name subtraction.
- `module.duplicate_decl` — two sibling modules instantiating the same
  generic, so both artifacts declare it and importing both would
  collide. Fix: instantiate in one shared module. (A shared-instance
  home falls out naturally once visibility lands; until then the
  diagnostic names both modules.)

## Measured

`sable check corpus/verifies/string.sable` (imports utf8): 27.6s →
2.0s once utf8's artifact exists — its 205 obligations are imported,
not re-proven. Cold full corpus: 164s → 130s (importer chains share
artifacts within the run). Root obligations are still re-proven every
run by design.

## Consequences and deferred

- `.sable-out/modules/` accumulates superseded artifacts (dev cache,
  gitignored); an occasional `rm -rf` is the garbage collector.
- Dependency *warnings* (automation-budget) surface on the check that
  freshly verified the dep; cache hits don't re-report them. Every
  corpus dependency is also a corpus root, so warning-cleanliness stays
  enforced there.
- Root-check caching (skip Lean when the root's own artifact is
  stamped) would collapse unchanged-corpus wall time to seconds; not
  taken — `sable check` re-verifying what you point it at is the honest
  default. Revisit if suite time hurts again.
- Still deferred from ADR 0013: `pub` visibility (with `use` lists
  becoming restrictive), module subdirectories, re-exports.
