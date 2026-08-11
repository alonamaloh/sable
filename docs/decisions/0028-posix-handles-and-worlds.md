# ADR 0028 — POSIX handles and the explicit world

**Decided 2026-08-11.** ADR 0027 made a deterministic foreign shim work.
This is the second FFI benchmark, and the plan chose that order on
purpose: a real `read(2)` adds file state, external input, short reads,
errors, and interruption, none of which `c_fill` had to answer.

## Decision

1. **Two non-memory resources.** An `OpenFile` is the authority to use one
   descriptor; a `PosixWorld` is the outside. Both follow ADR 0024's rule —
   authority the checker keeps affine, with a pure view the logic reads.

2. **The position lives in the `OpenFile` view**, not in the world, because
   that is where POSIX puts it: an open file description has its own offset
   and two descriptions of one file advance independently.

3. **A foreign operation that touches global state receives the world
   explicitly.** That is what replaces a `modifies` clause over the
   universe. It also means a caller can tell, from a signature alone,
   whether a function can reach outside at all — which is a stronger
   property than any frame clause gives.

4. **Authority for a descriptor is carved out of the world.**
   `open_file(&mut w, fd)` produces the `OpenFile`, with "is this
   descriptor really open" as a *precondition*, not a checker rule. Same
   division as `split_off`: the checker tracks tokens, the VCs track
   geometry — and the state of the outside world is geometry.

5. **The world's view does not model whether a read is short or fails.**
   No contract can predict those. They live in the machine and the monitor,
   and a caller has to handle every outcome its post admits. This is the
   whole reason for passing the world rather than assuming success.

6. **`posix_world(script)` exists only in `test_` functions.** It is the
   one place authority appears from nothing, and a program that could
   conjure a world could conjure any authority the world hands out. The
   `script` argument is what makes external behaviour something a test
   *author* controls: one script makes the second read short, another fails
   the first outright.

7. **Handles are passed explicitly, not owned by an RAII class.** A `File`
   whose destructor closes the descriptor needs non-empty `deinit` and
   destruction semantics, which is later work. Forgetting to `close` leaks
   a descriptor — exactly what affine-not-linear authority permits, and
   what a `#[must_consume]` marker would later diagnose.

## What this rung found

- **The exposure obligation caught the extern contract being
  under-specified.** A `read` post saying "these bytes came from the
  stream" says nothing about whether they are *bytes*, so the caller's
  `[u8]` could not be reconstructed from them. `PosixWorldView.wf` now says
  the stream is a byte stream. It says so for *every* index, not just
  `[0, len)`: off-the-end junk is our modelling choice as much as the
  stream is, and choosing it to be a byte removes a window premise from
  every read contract — the difference between a wrapper that verifies and
  one that needs more hand proof.

- **ADR 0026's "state effects functionally" lesson extends to foreign
  contracts.** The destination is one equation over `SpanView.fillFrom`,
  and because `n = 0` leaves every byte where it was, a short read and a
  failed read need no case analysis at all. Written as three clauses — the
  transferred prefix, the untouched tail, and "nothing changed on error" —
  the exit obligation needed two nested case splits and did not close.

- **A wrapper that hides the world must say what it preserved.**
  `read_twice` could not prove its second read's precondition until
  `read_into`'s post said the handle and the descriptor count survived.
  Found by writing the second caller, not by reading the first.

## The honest cost

**This is the first rung whose safe wrapper needs a hand proof.**
`read_into` carries a three-line `discharge` on the exposure's exit
obligation. It is not on the wrapper's own contract — `result ≤ dst.len`
and the frame clauses verify automatically — and `copy_prefix` (ADR 0026)
needed nothing at all. The difference is the boundary: a foreign contract
whose effect depends on an unpredictable outcome puts a case analysis in
front of the reconstruction, and automation does not chain "the world's
stream is bytes" into "so the buffer can be handed back".

Recorded rather than smoothed over. The tempting fix — a prelude lemma
shaped to this one signature — would be a prelude that knows about
`posix_read`, which is worse than a visible discharge in the subject that
needs it.

**Resource-view contracts are not monitorable**, and that is structural,
not a gap: a view is ghost, so at runtime there is nothing for the monitor
to look at. The verifier covers those; the monitor covers the value-level
halves — how many bytes arrived and which ones — and the test file carries
`expect-skip` fences saying so.

## Deliberately not decided

- **`open` and `write`.** `open` needs to produce a descriptor *and*
  authority, which is a product type; the two-step carve
  (`open_file` after the world already has the descriptor) is what avoids
  it, and a real `open` should wait for whatever answers products. `write`
  is symmetric to `read` and adds no new question.
- **Interruption and partial writes** beyond the short-read schedule, and
  any real libc binding. The schedule demonstrates that unpredictable
  outcomes are expressible and testable; enumerating POSIX is not this
  rung's job.
- **RAII file classes** (`must_consume`, non-empty `deinit`), which is the
  destruction-semantics rung.
