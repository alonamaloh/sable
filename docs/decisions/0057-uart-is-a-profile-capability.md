# ADR 0057 — UART access is a profile capability with trace semantics

**Decided 2026-08-12.** U9 established that ordinary allocation, raw bytes,
typed cells, and explicitly laid-out POD records can share one coherent heap
model. U10 must not undo that result by pretending a device register is a heap
cell with a `volatile` decoration. A UART access observes or changes an external
state machine, and every access is observable even when the returned value is
discarded.

## Decision

The first profile-specific slice is one deliberately narrow formal profile,
`uart-poll-v1`. It makes no commitment to an ISA, physical address space,
page-table format, interrupt model, DMA engine, or generic device-description
language.

Source programs receive an affine `resource Uart` capability. They cannot
construct one, cast an integer into one, or pass it through an audited extern.
The foreign boundary admits resources through an explicit whitelist of the
ABI-erased kinds its shims understand—`RawSpan`, `OpenFile`, and `PosixWorld`;
`Uart` is deliberately not on it.
Production entry code will eventually receive the capability from platform
provisioning. Tests alone may select one of a few deterministic UART scripts
with the compiler-sealed `test_uart` constructor: script 0 is immediately
ready, script 1 becomes ready on its third status read, and every other script
remains not-ready.

The current profile has one physical UART0 and therefore one root authority.
The signature-level authority budget is one: a function, method, initializer,
or generic template may declare zero or one `Uart` parameter, never two.
Accepting a second would make two pure views appear independent to VCgen while
the interpreter and formal profile both operate on the same singleton device.
For the same reason, an owned or borrowed
`Uart` resource may not be stored in a class field, including a generic class
field. Device-identified capabilities and functional field write-back are
future profile work; this slice keeps authority flow explicit through parameters
and locals.

UART operations form a device-intrinsic category separate from raw-memory
operations, resource transformations, and audited foreign calls:

- `uart_status(&mut uart) -> u8` consumes the next environmental oracle value,
  appends one status-register read to the chronological MMIO trace, and records
  whether transmission is ready;
- `uart_write(byte, &mut uart)` requires the most recently observed status to
  be ready, appends one transmit-register write, and clears readiness so a
  later byte must be preceded by another poll.

Both operations require an `unsafe` block. That block is an audit surface, not
a trust escape: the checker still proves the readiness and resource obligations
and the operations have formal machine semantics.

The scripted profile uses two abstract register identifiers in its trace. Their
current numeric encodings are profile-local observation labels, not general raw
addresses and not authority a program can derive from an integer.

## Machine and proof model

The base SVM remains unchanged as the default machine. A UART profile wrapper
adds selected-profile state, an oracle cursor, readiness state, and an ordered
MMIO trace. Non-device steps delegate to the base SVM; profile statements have
no base-profile meaning and reach `undef` there. The wrapper has its own
relational step relation, executable stepper, two-directional agreement proof,
determinism, progress, and runner. Its bare configuration renders byte-for-byte
like the core machine, so adding profile composition does not perturb the
existing differential oracle.

Keeping the wrapper separate avoids threading device state through every
existing arithmetic, call, array, and raw-heap rule. It also prevents the raw
heap from becoming an accidental bag of unrelated machine effects. A terminal
profile execution retains its trace and oracle cursor, so the differential
oracle compares the observable interaction as well as the return/trap/`undef`
outcome.

The proof-facing `UartView` mirrors the functional profile transitions. Driver
contracts use the transmit projection of its trace rather than exposing or
framing every status read. The first verified driver is bounded: it either
observes readiness and emits exactly one requested byte, or exhausts its poll
budget without changing the transmit projection. It assumes no fairness or
eventual readiness.

## Trust and profile identity

Using `uart-poll-v1` does not turn a fully verified build into “verified
relative to an audited boundary.” Its behavior is part of a kernel-checked
machine model, unlike an extern contract. Generated artifacts nevertheless
record the selected profile identifier, a content hash of its formal semantics,
and the device intrinsics they use. The hash is computed from the immutable
request snapshot over the complete recursive local Lean import closure rooted
at `Sable/MMIO.lean` and `Sable/SVMUart.lean`, plus `lean-toolchain` and
`lakefile.toml`; stable relative labels make this profile identity independent
of the clone path.

The containing proof is pinned more broadly. Before profile generation or
dependency work, the compiler captures `proof-env-v2`: every repository-local
Lean source plus `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.
That exact byte map is published under its id, built once at its final stable
path under a per-id lock and one Lake job, and marked READY last. Batch Lean and
the daemon consume that same build and exact generated text; a daemon switches
servers when the id changes. Artifacts also bind the exact canonical Sable
paths, source bytes, resolved import edges, and order. Generated root/module
files publish immutably and are compared byte-for-byte on reuse. FNV hashes are
therefore compact names only: an exact-byte mismatch fails closed as a
content-address collision.

## Implemented evidence

M44's first formal profile is complete and marks the defensible unsafe-Sable v1
stopping point; broader U10 is deliberately deferred rather than blocking the
usability roadmap.
`corpus/verifies/uart.sable` supplies the bounded polling/transmit driver and
discharges 16/16 obligations without assuming fairness. Dynamic fixtures run
the immediate-ready, delayed-ready, and never-ready scripts plus direct
`test_uart(0)` evaluation as an erased resource argument: 4/4 pass. The Lean
package build is green with one job, and the Rust/Lean differential gate agrees
on 69/69 subjects. The profile subjects compare outcome, trace order, cursor,
readiness clearing, invalid-write behavior, profile reselection before a
trapping replacement expression, and selection through assignment, discard,
and inferred declaration.

Resource erasure removes values, not effects. The interpreter evaluates erased
resource arguments and transformation operands left-to-right before discarding
their proof-only values. The SVM lowerer retains `test_uart` as a profile
statement in every statement context above. It erases an authority-only
resource operation only when each operand is syntactically runtime-inert;
potentially trapping or effectful operands make lowering fail rather than
silently changing the program.

The implementation audit also repaired loop semantics across checker, VCgen,
and monitor. Mutation discovery now exhaustively traverses conditions, bodies,
nested `unsafe`/`expose`, calls, and sealed raw/resource/device operations.
Affine shape and the variant are captured before the condition; a false
condition retains its post-state; and decrease is checked from that head value
to the post-body value on every taken iteration, including the final one. Trait
calls now use the ordinary overlapping-borrow rule, while UART-bearing trait
signatures are rejected until abstract trait contracts can carry resource
state.

The sound rule exposed free-list proofs that had relied on stale state.
`free_list_walk_unchanged` provides `state = old state` and restored-chain
postconditions, and the insert-location and first-fit searches transport their
current facts through that frame. Targeted checks are green for 33/33, 13/13,
and 22/22 obligations across the three pairs; focused Rust library tests pass
9/9; the complete single-worker corpus is green in 297.65s; and the full serial
Rust suite is green, including units, corpus, randomized allocator,
grind-budget, LSP, SVM differential, and doc tests.

## Deliberately deferred

- generic `MmioRegion<Device>` capabilities and device-description schemas;
- production platform provisioning and native fixed-address lowering;
- UART receive, interrupts, errors, FIFO depth, and timing;
- privileged instructions, page tables, and a Sail ISA connection;
- concurrency, atomics, and DMA ownership transfer.

Those require additional evidence and separate decisions. The specialized UART
profile is enough to test the architecture's central claim: devices are
capabilities plus oracle-driven trace semantics, not ordinary memory. With that
unsafe-v1 checkpoint reached, LLVM IR lowering is the active next milestone.
