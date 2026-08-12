# ADR 0042 — FreeHeader is one static role over two runtime typed cells

**Decided 2026-08-12.** ADR 0041 proved the two-word header shape. This
decision implements it without adding a bespoke header instruction to the
formal machine.

## Decision

`FreeHeader` is a mandatory, compiler-terminal resource view over allocator
identity, block key, typed size/link cells, and raw payload. Its unsafe surface
is:

```sable
resource FreeHeader h = raw_into_free_header(base, block);
raw_header_init(base, exact_size, next_key, &mut h);
u64 size = raw_header_size(base, &h);
u64 next = raw_header_next(base, &h);
raw_header_clear(base, &mut h);
resource FreeBlock block = raw_from_free_header(base, h);
```

Conversion in requires an aligned block of at least 16 bytes and creates two
uninitialized typed `u64` cells at `base` and `base + 8`. Initialization writes
both fields atomically at the source level and proves that the stored size is
the exact whole-block length. Reads require the selected field to be
initialized. Clearing requires both fields initialized; conversion out then
requires both cleared and returns one well-formed `FreeBlock`. Cleanup
zero-fills the two returned raw words, matching the existing typed-cell
primitive and executable heap semantics.

The operations are raw rather than erased resource transformations because the
metadata is real runtime state. In the SVM lowering, each composite operation
expands to two already-formalized typed-cell statements. This reuses the
relational rules, executable evaluator, agreement proofs, and failure
classification instead of adding a second memory semantics for headers.
Static resource operations may therefore be erased in SVM *statement*
position when they surround observable raw steps; using one as runtime
expression data remains a lowering error.

## Evidence and boundary

`corpus/verifies/free_headers.sable` performs the complete system-root,
allocator, header init/read/clear, block return, and release path at 13/13
obligations with zero `assume` and zero `defer`. Its dynamic test reads both
stored words and returns 64. Seven must-fail subjects pin undersized and
misaligned blocks, dishonest size metadata, uninitialized reads, conversion
before clearing, mandatory abandonment, and extern smuggling.

The SVM differential corpus contains a valid two-word round trip and an
uninitialized read; both trusted executables agree. The complete one-worker
corpus passes in 353.85 seconds, followed by grind-budget, LSP, SVM, library,
and doc-test regressions.

This is still a header mechanism, not traversal. The next proof must choose
the list sentinel, link ordering, and one-step lookup contract while keeping
the runtime head as ordinary safe state paired with the erased allocator
aggregate.
