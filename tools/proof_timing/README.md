# Proof-timing protocol v3

This protocol records reproducible **end-to-end verification wall time** for
Sable's closed positive corpus. It is observational engineering instrumentation,
not a correctness gate, a service-level objective, or an isolated measurement
of Lean kernel time.

> **Priority Zero assurance boundary:** new reports record each subject as
> `Lean accepted; proof dependencies unaudited`. Timing a successful Lean run
> does not authenticate its transitive axiom closure. The committed pre-finding
> baselines remain valid timing evidence for their exact revisions, but neither
> they nor a new timing report establish axiom-clean verification or release
> readiness.

The ignored runner is
`compiler/tests/proof_timing.rs`. A report may say `evidence.tier = baseline`
only when the runner itself confirms all of the conditions below. A developer
experiment requires the explicit `SABLE_PROOF_TIMING_ALLOW_CUSTOM=1` opt-in and
is labeled `smoke_custom`; it is never silently promoted or downgraded.

## Measured set and metric

The runner scans only the direct `*.sable` files in `corpus/verifies`, sorts
them by repository-relative UTF-8 path, and currently requires exactly 126
measured subjects. It explicitly excludes exactly one file:

- `corpus/verifies/defer_assume_demo.sable`, because that boundary
  demonstration intentionally contains one `defer` and one `assume`; its
  required SHA-256 is
  `da2324ce92ed248af6a0531619c12be570f21c9389e2b2b1df0db25da0d0cf9e`.

The exclusion path, reason, pinned SHA-256, actual source byte count, and actual
SHA-256 are present in the same length-framed content manifest as every
measured subject. Changed excluded content, or a new or removed corpus file,
therefore stops the run until the protocol is reviewed and its pins are changed
deliberately. Every measured subject must finish with zero warnings, zero
defers, and zero assumes.

Each subject's `verification_wall_ns` is the monotonic wall time around
`verify_file_batch_structured`: source/import loading, checking, VC generation,
Lean generation, proof-ingress auditor and Lean process execution, and artifact
publication are all inside the interval. It is not a kernel-only proof time.
The summary distinguishes:

- `verification_wall_subject_sum_ns`, the sum of those 126 API intervals; and
- `verification_wall_total_ns`, one interval around the serialized subject
  loop, including the small amount of per-subject bookkeeping between calls.

For each root subject, reports separately count the ordinary obligation
theorems, transition-certificate theorems, argument-schedule-certificate
theorems, and Lean bytes emitted in that root document. They also record that
root subject's successful artifact id and immutable proof-environment id, so
root-certificate growth cannot hide behind the older obligation-only count.
Dependency artifacts built within the timed API call are part of its wall time
but are not itemized by these root-subject metrics.

## Required state

Both modes require the test executable's authenticated Cargo output-profile
identity to be exactly `release`, plus `CARGO_BUILD_JOBS=1`,
`CARGO_INCREMENTAL=0`,
`LEAN_NUM_THREADS=0`, `LEAN_IMPORT_WORKERS=1`, and `SABLE_TEST_JOBS=1`, plus a
stable nonempty machine label containing only ASCII
letters, digits, `.`, `_`, or `-`, a prebuilt and exactly validated immutable
proof environment, no `.sable-out/daemon.sock`, existing local
`.sable-out/roots` and `.sable-out/modules` directories, and a new absolute
report path outside the checkout. A baseline also requires the test-only
`SABLE_GRIND_HEARTBEATS` override and ambient `ELAN_TOOLCHAIN`, `LEAN_PATH`,
`LEAN_SYSROOT`, `LEAN_SRC_PATH`, `LEAN_GITHASH`, `LEAN`, `LAKE`, `LAKE_HOME`,
and `LAKE_OVERRIDE_LEAN` overrides to be unset. Lake cache/config/key/endpoint,
Reservoir/package-map, and `LEAN_CC`/`LEAN_AR`/`CC`/`AR`/`CXX`/`LD` overrides
must likewise be unset. The
timing API bypasses the daemon even if one is started later; the socket checks
make that ambient-state error visible too. Directory-entry, metadata, symlink,
and UTF-8 errors are fatal.

The executable's exact selected-profile directory is captured from Cargo's
`OUT_DIR` at compile time by `compiler/build.rs`, cross-checked against the
running test executable's path, and recorded in the report. A baseline requires
that identity to equal `release` exactly and also requires Rust debug
assertions to be disabled. Cargo's build-script `PROFILE` is recorded only as
the debug/release profile family: Cargo documents that a custom profile
inheriting `release` has the same family, so neither it nor
`cfg!(debug_assertions)` can authenticate the selected profile alone.

The build script also embeds the full Git revision, build-time dirty state and
status fingerprint, and short rustc/Cargo versions. It watches package sources,
Git `HEAD`, the resolved ref, and packed refs so a normal Cargo invocation
refreshes those markers after source or revision changes. Baselines require a
known clean compile-time revision equal to both runtime revisions and matching
build/measurement rustc and Cargo versions. The test additionally embeds its
own source bytes and requires their SHA-256 to equal the on-disk protocol
source, preventing a stale same-revision executable from being mislabeled.
Non-Git source distributions may carry `unknown` markers and build normally,
but cannot produce baseline evidence.

Subject serialization comes from the runner's one lexicographic Rust loop, not
from either `SABLE_*_JOBS` variable. Those two variables are pinned
orchestration conventions for the surrounding test/corpus tooling. A shared
in-process mutex plus repository advisory lock serializes compiler-owned proof
launches, including Lake environment queries, proof-ingress auditors, and
direct Lean checks. A short-lived `lake env` wrapper may coexist with the one
Lean executable it launches; the bound is one Lean compiler/auditor runtime,
not one operating-system process. Every Lean-based child inherits
`LEAN_NUM_THREADS=0`,
disabling Lean's internal task manager, and `LEAN_IMPORT_WORKERS=1`, fixing the
otherwise hardware-dependent import-worker count and stripe order. The claim
is therefore at most one compiler-owned Lean proof runtime at a time for this
process and repository, with task-manager workers disabled and a single import
worker inside it.

Toolchain provenance records version output and the relevant ambient Lean/elan
variables. Command lookup through `PATH` and elan's binary-resolution
implementation remain trusted environment boundaries: reports do not
authenticate resolved tool executable paths or their bytes. Requiring the full
recorded Lean/Lake/native-tool override set to be unset for a baseline, and
removing that same set from provenance and measured proof children, lets the
checked-in `lean/lean-toolchain`, trusted empty Lake system configuration, and
Lake workspace drive ordinary selection without claiming more than the
recorded version strings. Every proof Lake process also forces artifact-cache
and restore off, disables package cache use, and supplies no system-cache
configuration.

`cold-roots` means:

- the immutable proof environment is already built and has a valid `READY`;
- `.sable-out/roots` and `.sable-out/modules` exist and contain no entries at
  the start; and
- the serial run populates both directories.

This is a cold generated-artifact start, not a cold operating-system page
cache and not a Lean-prelude build measurement. Imported artifacts become warm
as the lexicographically ordered series progresses. The runner records and
compares a proof-build identity at both ends: `READY`, the exact sorted local
`.olean` set, the proof-ingress auditor executable, and the READY-bound
observational declaration-inventory executable, with content SHA-256, size,
and mtime for each and device/inode on Unix. `Sable.olean` remains separately
named in the JSON for compatibility but is also a member of that complete set.
The declaration inventory is dormant provenance in v3 and is not part of the
per-document measured workload. A changed identity invalidates the series so a
same-source-id proof-environment rebuild or proof-output mutation cannot be
silently included in measured verification time.

For the prescribed paired procedure, `warm-artifacts` means:

- the operator starts it next, without an intervening build, edit, clean,
  daemon, or cache change;
- `SABLE_PROOF_TIMING_COLD_REPORT` selects a successful v3 cold report whose
  bytes are hashed into the warm report;
- its proof-build identity equals the selected cold report's ending identity;
- its starting cache metadata manifest equals the selected cold report's
  ending metadata manifest; and
- the start and end metadata manifests of both artifact directories are
  identical.

The warm runner hashes the cold report bytes, validates its fields, and
requires the same successful evidence tier, full Git revision, subject
manifest, proof environment, release test executable, Cargo lockfile, protocol
source, machine, toolchains, environment, invocation, proof-build identity,
and cold-end cache metadata manifest. Roots are still source-confined by fresh
proof-ingress auditor processes and re-proved in fresh batch Lean processes.
“Warm” refers to generated artifacts available for reuse, never a daemon or
retained in-process checker.

Generated-cache manifests intentionally hash sorted relative path, entry kind,
and file size without reading artifact contents. Reading every generated
`.sable-out/modules/*.olean` only before the warm series would itself
manufacture a page-cache advantage. The immutable proof-environment `.olean`
set is intentionally content-hashed in both cold and warm preflights as part of
the full proof-build identity. Generated artifact names and the compiler's reuse
validation retain their normal content-addressed checks.
The subject content manifest necessarily reads every measured source before
both series, so neither mode claims cold source-file I/O.

The harness cannot prove that the paired commands were temporally adjacent,
that the warm cache has unique physical lineage from the cold run, or that two
metadata-equivalent cache files have identical contents. The no-intervening-
change rule is part of the human procedure. The report binds the selected cold
report bytes and equivalent sorted path/type/size state; normal
content-addressed artifact validation remains responsible for reuse safety.

## Exact baseline procedure

Use a quiet, thermally stable machine and a disposable clean worktree. Run all
commands below from the repository root in one shell. Replace the machine label
with a stable name that you will reuse for later series.

First confirm the revision, compile the exact release timing executable without
running it, and prebuild the immutable proof environment with a single
sacrificial release verification. There must be no daemon socket. Let the
machine return to its intended idle/thermal state after this preparation.

```sh
git status --short
git rev-parse HEAD
test ! -e .sable-out/daemon.sock && test ! -L .sable-out/daemon.sock
unset SABLE_GRIND_HEARTBEATS ELAN_TOOLCHAIN LEAN_PATH LEAN_SYSROOT
unset LEAN_SRC_PATH LEAN_GITHASH LEAN LAKE LAKE_HOME LAKE_OVERRIDE_LEAN
unset LAKE_ARTIFACT_CACHE LAKE_RESTORE_ARTIFACTS LAKE_NO_CACHE LAKE_CACHE_DIR
unset LAKE_CONFIG LAKE_CACHE_KEY LAKE_CACHE_SERVICE
unset LAKE_CACHE_ARTIFACT_ENDPOINT LAKE_CACHE_REVISION_ENDPOINT
unset LAKE_PKG_URL_MAP RESERVOIR_API_BASE_URL RESERVOIR_API_URL
unset LEAN_CC LEAN_AR CC AR CXX LD

CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 LEAN_NUM_THREADS=0 \
LEAN_IMPORT_WORKERS=1 \
  cargo test --release --locked --manifest-path compiler/Cargo.toml \
  --test proof_timing --no-run

CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 LEAN_NUM_THREADS=0 \
LEAN_IMPORT_WORKERS=1 \
SABLE_TEST_JOBS=1 \
  cargo run --release --locked --manifest-path compiler/Cargo.toml -- \
  check corpus/verifies/count_up.sable
```

`git status --short` must print nothing. Preserve any existing generated
artifacts in a temporary backup, then recreate the two measured caches empty.
The immutable `.sable-out/proof-envs` directory stays in place.

```sh
SABLE_TIMING_CACHE_BACKUP="$(mktemp -d .sable-out/proof-timing-backup.XXXXXX)"
mv .sable-out/roots "$SABLE_TIMING_CACHE_BACKUP/roots"
mv .sable-out/modules "$SABLE_TIMING_CACHE_BACKUP/modules"
mkdir -p .sable-out/roots .sable-out/modules

SABLE_TIMING_REVISION="$(git rev-parse HEAD)"
SABLE_TIMING_MACHINE="$(hostname)-proof-baseline"
SABLE_TIMING_COLD="/tmp/sable-proof-${SABLE_TIMING_REVISION}-cold.json"
SABLE_TIMING_WARM="/tmp/sable-proof-${SABLE_TIMING_REVISION}-warm.json"
test ! -e "$SABLE_TIMING_COLD" && test ! -L "$SABLE_TIMING_COLD"
test ! -e "$SABLE_TIMING_WARM" && test ! -L "$SABLE_TIMING_WARM"
```

Record the cold series:

```sh
CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 LEAN_NUM_THREADS=0 \
LEAN_IMPORT_WORKERS=1 \
SABLE_TEST_JOBS=1 \
SABLE_PROOF_TIMING_CACHE_MODE=cold-roots \
SABLE_PROOF_TIMING_MACHINE="$SABLE_TIMING_MACHINE" \
SABLE_PROOF_TIMING_OUT="$SABLE_TIMING_COLD" \
  cargo test --release --locked --manifest-path compiler/Cargo.toml \
  --test proof_timing record_verifying_corpus_proof_times -- \
  --ignored --exact --nocapture --test-threads=1
```

Without building, editing, cleaning, starting a daemon, or changing the cache,
record the linked warm series:

```sh
CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 LEAN_NUM_THREADS=0 \
LEAN_IMPORT_WORKERS=1 \
SABLE_TEST_JOBS=1 \
SABLE_PROOF_TIMING_CACHE_MODE=warm-artifacts \
SABLE_PROOF_TIMING_MACHINE="$SABLE_TIMING_MACHINE" \
SABLE_PROOF_TIMING_COLD_REPORT="$SABLE_TIMING_COLD" \
SABLE_PROOF_TIMING_OUT="$SABLE_TIMING_WARM" \
  cargo test --release --locked --manifest-path compiler/Cargo.toml \
  --test proof_timing record_verifying_corpus_proof_times -- \
  --ignored --exact --nocapture --test-threads=1

git status --short
```

The build script watches package sources and Git revision files, not the Git
index or generated timing caches, so this unchanged second invocation should
reuse the exact cold executable. If Cargo recompiles anything before the warm
test starts, abort the pair and prepare a new cold run.

The final status command must also print nothing. Both JSON documents must say
`schema = sable-proof-timing-v3`, `status = ok`, and
`evidence.tier = baseline`. The warm report records the cold report's absolute
path and SHA-256. The original generated caches remain recoverable under
`$SABLE_TIMING_CACHE_BACKUP`; do not restore them until the warm run and any
report review are complete.

For a non-release-profile/debug-assertion/dirty experiment, set
`SABLE_PROOF_TIMING_ALLOW_CUSTOM=1` on both cold and warm commands and prepare
the same cache states. Retain `CARGO_BUILD_JOBS=1`, `CARGO_INCREMENTAL=0`,
`LEAN_NUM_THREADS=0`, `LEAN_IMPORT_WORKERS=1`, and `SABLE_TEST_JOBS=1`. Such
reports say `smoke_custom` even if some other
baseline conditions happen to hold. Cache truthfulness, no-daemon operation,
subject count, warm-lineage metadata checks, proof-build stability, and zero
warning/defer/assume remain mandatory. Custom Lean/elan overrides or a custom
grind-heartbeat override are recorded as additional smoke reasons.

## Report and comparability

The v3 document records:

- status and evidence tier;
- start/end nanosecond timestamps;
- exact start/end Git revisions, cleanliness, and porcelain status;
- the sorted subject content manifest and per-file SHA-256;
- immutable proof-environment, full local proof-output/auditor/inventory build,
  root-artifact, test-executable, Cargo lockfile, and protocol-source
  identities;
- machine label, host, kernel, architecture, CPU model, logical CPUs, Rust,
  Cargo, Lake, Lean, authenticated Cargo output-profile identity, recorded
  profile family, debug-assertion state, and relevant build environment;
- the test process arguments and current directory;
- metadata-only start/end cache manifests and cold-parent lineage;
- per-root-subject wall time, root-emitted theorem-category counts and Lean
  bytes, root audit-boundary counts, and the explicit proof-assurance state;
  and
- aggregate median, nearest-rank p95, maximum, sums, and failure totals.

A preflight violation, or a fatal postflight inspection error, aborts and may
produce no report. Verification failures and postflight mismatches that were
successfully observed write a `status = failed`, `evidence.tier = invalid`
report (with the attempted tier retained) and then fail the ignored test,
preserving the diagnostic evidence without mislabeling it a baseline.

Compare absolute times only when machine identity, toolchains, profile,
protocol, subject manifest, cache mode, and relevant environment are alike.
Across revisions, inspect theorem counts and generated bytes alongside time.
Do not interpret the cold/warm delta as pure artifact-reuse cost: filesystem
cache, OS page cache, thermal state, scheduler activity, and import order still
affect it. Use repeated paired series for a distribution rather than promoting
one run into a performance guarantee.

## Recorded baselines

The immutable [baseline index](baselines/index.json) remains the authority for
committed historical pairs and their report hashes. Its current v2 pair
predates the per-document proof-ingress auditor and v3 full proof-build
identity, so it is historical evidence and is not comparable with a v3 series.
The v2 files and index remain untouched. That pair measures revision
`25ebc21e71fb7827bf50bd39432e00fd9754c234` on
`alvaros-m2-air-arm64`: 126/126 subjects verified with zero warnings, defers,
assumptions, or failures. Cold-roots took 313.915 seconds and the linked
warm-artifacts run took 218.627 seconds. A separate 250 ms process-table
monitor observed at most one actual Lean process in either run.

Those two totals are one observational pair, not a performance guarantee or a
claim that artifact reuse alone caused their difference. Consult the raw
reports and compare theorem counts, generated bytes, machine state, and the
protocol's stated cache limitations before comparing a later series.

## Committing a baseline

Do not commit ad-hoc reports. For a reviewed successful pair, use immutable
paths of this form:

```text
tools/proof_timing/baselines/<full-revision>/<machine>/<series-id>-cold-roots.json
tools/proof_timing/baselines/<full-revision>/<machine>/<series-id>-warm-artifacts.json
```

When the first pair is committed, add
`tools/proof_timing/baselines/index.json` with one row per pair containing the
full revision, machine, date/series id, both repository-relative paths and
SHA-256 values, protocol schema, proof-environment id, subject-manifest hash,
and a short context note. Reviewers should verify that both reports are
`baseline`/`ok` and mutually linked before adding the row. Keep custom smoke
reports outside `baselines/`; if one is retained for an investigation, its
path and prose must say `smoke_custom`.
