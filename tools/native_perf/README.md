# Native `-O2` performance gate

This directory measures only workload pairs that the verified LLVM entry path
actually admits. It also keeps machine-readable closure records for the three
canonical showcase programs that do not yet reach native code. A backend
refusal never turns into a timing ratio, and a narrower workload never borrows
the canonical program's name.

## Current scope

| Workload id | Native status | What the result means |
|---|---|---|
| `quicksort` | blocked | Exact verified recursive i32 quicksort; C is reference-only. |
| `merge` | blocked | Exact verified borrowed-i32 merge; C is reference-only. |
| `hashmap` | blocked | Exact verified generic `HashMap<i32,u64>`; C is reference-only. |
| `lomuto_partition_u32` | admitted, non-comparable | Exact non-recursive partition kernel over native u32 arrays, but both `-O2` subjects precompute its fixed-input algorithm; it produces no ratio. |
| `merge_u32` | admitted, comparable | Full merge algorithm over native u32 arrays; not evidence for the i32 ABI. |
| `linear_probe_u32` | admitted, comparable | Fixed-capacity local-u32-array probing; not the generic map or its full abstraction contract. |

The exact rendered blocker fragments, source/runtime hashes, comparison
eligibility, and audited admission expectations are in `closure.json`.
Diagnostic identifiers are deliberately not claimed because the CLI does not
render them. Workload inputs, entries, work-unit counts, and semantic profiles
are in `workloads.json`.

## Run

Run from the repository root, giving the machine an explicit stable label:

```sh
test ! -e .sable-out/daemon.sock && test ! -L .sable-out/daemon.sock
LEAN_NUM_THREADS=0 LEAN_IMPORT_WORKERS=1 \
  python3 tools/native_perf/run.py \
  --machine-label apple-m2-air-local \
  --output /private/tmp/sable-native-perf.json
```

The default protocol uses three warmups and fifteen measured executions. Each
execution is a fresh process, but performs 262,144 internal work units so launch
time is not the dominant operation. `--only ID` is repeatable. A quick local
check can use an explicit development compiler with `--compiler PATH --warmups
1 --samples 3 --allow-dirty`; a dirty or explicit-compiler result is marked as
`smoke_custom` evidence, not a baseline. Custom manifest or closure paths are
also marked `smoke_custom`, as are workload subsets and nondefault warmup/sample
counts. Without `--compiler`, the runner builds the current clean checkout's
locked release compiler before admission checks. Put baseline output outside
the worktree; an in-worktree output path is also marked custom.

The runner enforces one Cargo build job, disables incremental compilation for
that release build, disables Lean's task manager, and uses one Lean import
worker for every child command. It also rejects any daemon socket path entry,
including a dangling symlink, both before and after the run so Sable cannot
route verification through a server with unrelated process settings. The
explicit Lean settings in the example make the supported invocation visible;
inherited values are overwritten fail closed, and the enforced preparation
concurrency is recorded in the report's protocol provenance.

The runner:

1. refuses a dirty worktree by default and builds its release compiler from
   that recorded checkout unless an explicit smoke/custom binary is supplied;
2. records the manifest, closure, runtime, compiler, machine, and toolchain
   provenance, and authenticates the runtime, verified subject, and both
   workload sources against closure SHA-256 values;
3. validates the closure's audited base commit as a local ancestor, records its
   date and optimization, and checks HEAD, dirty state, compiler, and every
   authenticated input again after the run;
4. requires the Sable loop bound to equal the manifest work-unit count and
   injects that count into C as `WORK_UNITS` at compile time;
5. asks `sable build --emit-llvm --entry ...` for every exact closure;
6. requires each blocked closure to return exactly one matching backend error
   and terminal lowering summary, and each admitted artifact to print exactly
   one zero-deferred, zero-assumed, no-unsafe, no-extern, `fully verified`
   summary;
7. compiles temporary optimized LLVM for both admitted sides and applies a
   hardcoded, workload-named anti-trivialization profile before linking;
8. compiles both emitted LLVM and C with the same Clang `-O2` and the same
   separately compiled hosted allocation hooks;
9. requires both executables to return the workload's semantic-oracle exit
   value before any timing; and
10. alternates C-first and Sable-first sample order, recording raw samples,
   median, p95, per-work-unit median, toolchains, machine, revision, and protocol.

If a source, native gate, or expected status changes, the run fails. Review the
semantic pair and closure before updating hashes or admission status.

## Recorded baselines

- Revision `ef8b38f8485806a59814e797547eaa742c463fd3` on
  `alvaros-m2-air-arm64` (macOS 26.5, arm64): clean-checkout release compiler,
  all six closure checks, and admitted native paths at `-O2`; comparable pairs
  use three warmups and fifteen samples. The complete
  [JSON report](baselines/ef8b38f-alvaros-m2-air-arm64.json) has SHA-256
  `cb88d5c247d2cbb74df528b31e30510c86b080dbbf331dc1db76227110cebd82`.
  The eligible median Sable/C ratios are `1.0130848846734675` for `merge_u32`
  and `0.9228923732557233` for `linear_probe_u32`. `quicksort`, `merge`, and
  `hashmap` have `c_reference_only_native_blocked`; `lomuto_partition_u32` has
  `admitted_noncomparable_optimization_trivialized`. Those four workloads have
  no timing samples or ratios.

## Interpretation and nonclaims

- Ratios exist only for `comparison_status = "comparable_admitted_pair"`.
  Canonical blockers report `c_reference_only_native_blocked`; the admitted
  fixed-input partition reports
  `admitted_noncomparable_optimization_trivialized`. Neither status has samples
  or a Sable/C ratio.
- The optimized-LLVM profiles are anti-trivialization gates, not equivalence
  proofs. Merge must retain a dynamic load-to-load unsigned value comparison
  and dynamic result store. Linear probing must retain dynamic loads,
  occupancy/key comparisons for the exercised keys, and stores through
  probe-selected addresses. The partition profile intentionally records the
  absence of its ordering comparisons and dynamic stores; if that changes, the
  closure must be re-audited before it can become comparable.
- Allocation and release are inside every work unit on both sides and cross the
  same separately compiled hosted hooks. Compiler verification and LLVM/C
  compilation are recorded but not included in execution time.
- The Sable side is accepted for comparison only with exactly zero deferred or
  assumed obligations and no unsafe or extern boundary. The C side is an
  audited equivalent fixed workload, source-authenticated and checked by a
  full-output/result oracle; it is not formally verified.
- These are small fixed workloads on one machine, not application benchmarks,
  scaling studies, stable ABI claims, or evidence for the canonical quicksort,
  borrowed-i32 merge, and generic-map closures.
- A few samples are useful for regression detection, not for a publication
  claim. Repeat on controlled machines and compare full sample distributions
  before making broader performance statements.
