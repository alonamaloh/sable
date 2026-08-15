# ADR 0066 — payload gates answer yes or a named error, and nothing else

**Decided 2026-08-16.**

## Context

ADR 0064 made a container payload a full `Ty`, and ADR 0065 made
`Ty::Option(Box<Ty>)` the only option constructor. Four per-stage functions
still answered two questions at once — "may this payload sit here" and "what
is the resulting type" — and ADR 0064 recorded them as remaining work:

| function | signature |
|---|---|
| `check::array_payload_ty` | `(Ty, Span) -> CResult<Ty>` |
| `interp::value_ty` | `(&Ty) -> Option<Ty>` |
| `svm::array_element_ty` | `(Ty, &str) -> Result<Ty, String>` |
| `svm::ordinary_option_payload_ty` | `(Ty) -> Result<Ty, String>` |

Each was identity on accept: `Ty::Bool` in, `Ty::Bool` out. The rebuild is a
leftover from `ValueTy`, when a container held a *smaller* representation and
the caller genuinely could not name its own element type. A container now
holds the element type, so the caller already has the answer and every one of
these functions handed it back a copy of what it was given.

Fusing the two questions was defensible while the lowering was real: a
separate lowering beside a validator is a second entry point nothing guards.
Once the lowering is the identity, the argument inverts — the fused function
*is* the second entry point, and the file already had the validator beside it.
`svm::validate_array_payload` existed only to call `array_element_ty` and
discard its result, `svm::ordinary_option_payload_ty` was a second copy of
`svm::validate_option_payload`'s allow-list with a hard-coded context string,
and `check::array_elem_ty` already called `array_payload_ty`, threw the result
away, and returned its own clone of the payload.

## Decision

**A payload gate answers yes or a named error.** The four conversions become
pure validators, and every caller uses the payload it already holds.

| function | shape |
|---|---|
| `check::validate_array_payload` | `(&Ty, Span) -> CResult<()>` |
| `svm::validate_array_payload` | `(&Ty, &str) -> Result<(), String>` |
| `svm::validate_option_payload` | `(&Ty, &str) -> Result<(), String>` |
| `interp::validate_interp_array_payload` | `(&Ty, &str) -> Result<(), String>` |
| `interp::validate_interp_option_payload` | `(&Ty, &str) -> Result<(), String>` |

`svm::array_element_ty` and `svm::ordinary_option_payload_ty` are deleted into
the validators that already stood beside them; each stage's array payload and
option payload questions now have exactly one entry point apiece.
`interp::value_ty` is deleted outright: its allow-list was a third copy of
`validate_interp_array_payload`'s and `validate_interp_option_payload`'s, and
its six callers either already treated it as a validator or wanted the payload
they were holding.

The gates keep every property ADR 0064 requires of them. They are allow-lists,
they end in a named refusal, and none of them calls itself. Taking `&Ty`
rather than `Ty` is what makes "the caller keeps the payload" cheap: the gate
borrows, the caller moves.

### The one real transformation, kept and named

`interp::option_value_ty` is **not** identity and does not fold. It answers
what an option's *present case* holds, and for a nullable raw pointer that is
a different constructor:

```rust
Ty::OptionRaw(record) => Some(Ty::RawRecord(record))
```

`option<raw<Record>>` is one abstract nullable pointer value rather than an
option over a pointer (ADR 0063), so its present case has type `raw<Record>`.
That arm is a lowering, it survives explicitly, and the `interp option value`
column of `docs/shape-admission.md` records `` `raw<record>` `` for that shape
so deleting it moves a cell. Its ordinary-option arm now runs
`validate_interp_option_payload` and returns the payload, which is the same
accept set it had through `value_ty`.

`check::option_payload_ty` still validates and lowers. It is identity on
accept like the four, but its callers were not part of this change, and ADR
0064's rule — a conversion goes when its callers stop asking for a rebuilt
type — is what decides when it follows.

### Two entry points became one, and two panics went away

`interp::value_ty`'s callers in `AllocArray` and `ArrayLit` read
`value_ty(elem).expect("validated concrete interpreter array payload")` — a
panic standing for an argument about a validator that ran ten lines earlier.
Using `elem` directly deletes the `.expect` and the argument together.

## Consequences

**Behaviour is preserved everywhere a program can reach.** The four functions
were identity on accept, so no caller could observe the difference between the
value returned and the value it passed in; and every refusal they could raise
is raised by the validator that replaces them, under the same machine-matchable
name.

**Three deliberate changes, none of which moves a diagnostic name.**

1. **`docs/shape-admission.md` loses the `interp payload value` column.**
   It recorded `Answer::Observed(value_ty(shape))`, which has no meaning once
   `value_ty` is gone. Its cells held only `` `u64` ``, `` `bool` ``, and
   `none` — identity on accept — so its accept set already duplicated
   `interp array payload` and `interp option payload` cell for cell. Every
   remaining cell of the table is byte-identical: 45 shapes × 25 gates, with
   no cell moved. This is a column removal, not a gate answering differently.

2. **Three interpreter preflight messages gained the shared wording.** The
   store, index, and semantic-type sites each formatted their own
   `interp.aggregate_payload_unsupported` text ("... has unsupported payload
   `X`") in the `None` branch of `value_ty`; they now pass their subject as
   the context to `validate_interp_array_payload` and get its fuller message,
   which names the payload domain. The diagnostic *name* is unchanged, so no
   `expect-error` fence and no ratchet cell moves. The path is unreachable
   from a checked program in any case — the checker's own array payload gate
   refuses the same shapes first, and monomorphization has already removed the
   type parameters this gate additionally refuses.

3. **Seven dead refusals were deleted rather than rewritten.**
   `svm::array_element_ty` was called at three sites that `svm::resolve_array`
   had already validated, and `svm::ordinary_option_payload_ty` at four sites
   that could only be reached holding a `SvmOptionRepr::Ordinary`, which
   `svm_option_repr` and `validate_option_accessor` construct only after
   `validate_option_payload` accepts. Those refusals were unreachable *before*
   this change; deleting the second copy is what makes that visible.
   `SvmOptionRepr::Ordinary` now carries a doc comment saying holding one is
   the evidence that the payload was admitted.

**What verifies the claim.**

- `docs/type-matrix.md` is untouched and byte-identical: `Open cells: 33/81`.
- `docs/shape-admission.md` changes by exactly one removed column; all 45
  rows agree cell for cell on the 25 gates that remain.
- The snapshot oracle (`compiler/scripts/type-snapshot.sh`), run against a
  binary built before ADR 0065 and this change: the Lean half is an **empty
  diff over 114,517 lines** — every `corpus/verifies` subject, every mangled
  declaration name, every emitted Lean type. The diagnostic half is
  **additions only**, the eighteen lines of the two subjects ADR 0065 added,
  with no line removed or changed. Neither of these two changes contributes a
  byte to either artifact, which is what "identity on accept" predicted.
- No diagnostic name is created, so no `corpus/must-fail` subject is required.
  The existing subjects for `type.array_payload_unsupported`,
  `type.aggregate_payload_noncanonical`, and
  `type.option_payload_unsupported` are live probes of the folded gates and
  none of them changed outcome.

## What did not land

**`Ty::Borrow(Mutability, Box<Ty>)` still does not exist**, and
`check::option_payload_ty` and `interp::option_value_ty` still return a type.
`option_value_ty` has a reason to (above); `option_payload_ty` is waiting on
its callers.
