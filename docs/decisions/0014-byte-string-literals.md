# ADR 0014 — Byte-string literals; bare literals reserved for `String`

Date: 2026-08-10. Status: accepted, implemented (the byte form). The
`String` class itself is future work; this ADR fixes the literal
syntax so nothing changes meaning when it lands.

## Context

There was no way to write text: the JSON and UTF-8 corpus encoded test
data as `[123, 34, 107, ...]` with a comment holding the actual
string. Two literal users exist and both are real — application code
wants a `String`, while codec/test code wants raw `[u8]` bytes,
including deliberately *invalid* UTF-8 that a `String` literal must
never be able to spell.

## Decision

Rust's split, decided now, delivered in two stages:

- **`b"..."` is a `[u8]` literal** of the UTF-8 bytes between the
  quotes — implemented. It is pure sugar: the lexer produces the byte
  vector, the parser desugars to the ordinary array-literal node, and
  no later stage knows literals exist. Escapes are
  `\n \r \t \0 \\ \" \xNN`; the literal must close on its own line.
  Diagnostics: `lex.bad_escape`, `lex.unterminated_string`.
- **Non-ASCII source characters are permitted** and contribute their
  UTF-8 bytes verbatim (`b"é"` is two bytes) — a deliberate deviation
  from Rust, which forbids non-ASCII in byte strings. Sable source is
  UTF-8, the corpus is full of UTF-8 test data, and `b"Aé€😀"` next to
  `b"A\xc0\x80B"` is exactly the valid/invalid contrast the UTF-8
  tests want to state.
- **Bare `"..."` is reserved** (`lex.string_reserved`) for the future
  `String` type: an owned class value over `[u8]` bytes carrying a
  UTF-8 validity invariant, whose literals will satisfy that invariant
  by construction (the compiler read the bytes from a UTF-8 source
  file, so the obligation is a decidable fact over known bytes).
  Reserving now means no literal ever changes type later.

The desugared literal is an untyped array literal, so its type comes
from the expected type like any bracketed literal (`[i32] a = b"Hi!";`
is legal and means the byte values as i32s). Accepted: the literal is
sugar for exactly the array you would have written by hand.

## Consequences

- The corpus test data is legible: `b"{\"a\": 1}"` replaced 52-entry
  decimal arrays across the JSON, UTF-8, and hex tests;
  `corpus/tests/test_byte_literals.sable` pins every escape
  byte-for-byte.
- Owned arrays currently exist only in test functions, so byte
  literals are exercised by the dynamic corpus and lex guards; the
  verifies corpus picks them up when owned-array allocation lands.
- `String` gets its own ADR when built: ghost model (byte sequence
  with validity invariant vs. codepoint sequence), slicing across
  character boundaries, and iteration are the open questions there.
