# Curated soundness mutations

This pilot answers a narrow question: do focused witnesses notice deliberate
damage to Sable's checker, retained control plan, and VC generator? It is not a
whole-program mutation score and does not claim that surviving mutants are
sound.

The runner uses only the Python standard library. It archives a committed Git
revision into a temporary checkout, gives each worker its own
`CARGO_TARGET_DIR` and `.sable-out`, applies an exact single-occurrence text
patch, compiles, runs the listed oracle, restores the pristine bytes, and
deletes the temporary checkout. The live working tree is never copied or
modified. By default the archived revision is `HEAD`, so uncommitted source
changes are intentionally excluded.

## Quick start

From the repository root:

```sh
python3 tools/soundness_mutations/runner.py --list
python3 tools/soundness_mutations/runner.py --dry-run
python3 tools/soundness_mutations/runner.py \
  --mutant control.assignment_destination_check_omitted \
  --workers 1 --report /tmp/sable-mutations.json
```

Run the entire curated set with:

```sh
python3 tools/soundness_mutations/runner.py --workers 2 \
  --report /tmp/sable-mutations.json
```

Workers are deliberately bounded to 1–4. The defaults are two workers, a
five-minute compile timeout, and a three-minute timeout for each oracle. Use
`--compile-timeout` and `--timeout` to adjust those limits. `--revision`
accepts any commit-ish; `--limit N` is useful for a smoke run. Progress goes to
stderr. The report is JSON on stdout unless `--report` is supplied.

## Result meanings

- `semantic-kill`: a source that the pristine compiler rejects is accepted by
  the mutant. This is the principal soundness signal.
- `conservative-kill`: a source accepted by the pristine compiler is rejected
  by the mutant.
- `structural-kill`: a focused Rust invariant test fails under the mutant.
- `compile-invalid`: the mutation does not compile, including test-only
  compilation failures.
- `crash`: the mutated compiler terminates by signal, panic, or fatal runtime
  error instead of producing a language result.
- `timeout`: compilation or an oracle exceeded its bound.
- `equivalent-or-survivor`: the focused oracle observed no semantic or
  structural change. The mutation may be equivalent, redundantly guarded, or
  simply missing a witness.

A must-fail source that remains rejected is never called a semantic kill merely
because its diagnostic changed. The JSON records this as
`diagnostic_only_change` under the oracle and classifies the mutant as
`equivalent-or-survivor`. Baselines are checked before mutation: a missing
rendered marker, unexpected exit status, crash, or baseline timeout is a
`harness-error`, not a mutation result.

## Manifest and oracles

[`mutations.json`](./mutations.json) contains curated edits and focused
oracles. Every edit has repository-relative `file`, `before`, and `after`
strings. Dry-run validation requires `before` to occur exactly once in the
selected revision and rejects absolute paths, parent traversal, unknown
families, missing sources, duplicate IDs, and malformed oracles.

Two oracle kinds are supported:

- `source` runs the just-built `sable check`. Its `expect` is `failed` or
  `verified`; every expected failure has a stable `baseline_contains`
  substring from the CLI's rendered output. Optional `module_paths` become
  `-M` arguments.
- `cargo-test` runs one fully qualified library test with `--exact` and treats
  an assertion failure as a structural kill. A successful exit is accepted
  only if Cargo reports both `running 1 test` and the exact named test as
  `ok`; a zero-test filter is a harness error.

Prefer a small source whose only expected failure is the removed obligation.
Use a structural unit test when a semantic source cannot directly forge the
retained representation being guarded. Multiple focused oracles are allowed
when they exercise genuinely different paths.

## Cost and limitations

Each worker performs one pristine build and then incremental builds for its
assigned mutants. Workers do not share Cargo or Lean caches with one another
or with the live checkout. Mutants assigned to the same worker deliberately
reuse that worker's incremental Cargo target and proof environment after the
source bytes are restored; this is cache reuse, not per-mutant cache
isolation. `.sable-out/proof-envs` is retained only inside that worker to avoid
needlessly rebuilding proof environments, while all per-source output is
cleared between oracles. Full-corpus verification per mutant is intentionally
out of scope because it multiplies a multi-minute corpus run and gigabytes of
proof output.

Some mutants will be equivalent or stopped by a second guard. That is useful
evidence, not a reason to weaken classification. Review survivors manually,
then either add an independent witness, refine the mutation so it isolates one
authority boundary, or document the redundant defense. Timing varies with the
Rust cache and Lean toolchain, so this harness should not double as a
performance benchmark.

## Recorded baselines

[`baselines/6450253.json`](./baselines/6450253.json) records the first complete
run against the commit that introduced this harness. Its manifest hash binds
the result to the exact 20 mutations: 16 were semantic kills and four were
structural kills, with no survivors, invalid mutants, crashes, timeouts, or
harness errors. This is evidence that the selected witnesses detect those
specific edits; it is not a whole-compiler mutation score or a soundness
percentage. The elapsed time is retained for audit context only and is not a
performance measurement.
