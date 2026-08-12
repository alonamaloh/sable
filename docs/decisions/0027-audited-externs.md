# ADR 0027 — Audited externs and the trust manifest

**Decided 2026-08-11.** ADR 0026 got a safe wrapper over raw memory to
verify with no user-visible heap logic. This decides how Sable talks to
code it cannot verify, and — more importantly — how the build says so.

## Context

Every rung so far ended with `status: fully verified`. A foreign function
breaks that: its contract is an axiom nobody proved. The design's own
instruction is blunt — *do not print `fully verified` when unproved extern
contracts remain* — so the interesting part of this rung is not the calling
convention, it is the honesty of the output.

## Decision

1. **An extern's contract is audited, not proved.** `extern "C" fn f(...);`
   has no body, owes no obligations, and its posts are assumed at call
   sites exactly as a verified function's are. Its clauses *do* get
   well-formedness defs: a trusted contract that does not elaborate is not
   a contract.

2. **Audit metadata is mandatory**: `#[audit(id := "...", reason := "...")]`.
   A trusted contract with no recorded reason is an unsourced axiom. The
   `id` names *this version* of the contract; the `reason` is what a reader
   of the manifest gets.

3. **Effects are structural, through the resource parameters.** Only a
   passed `resource &mut R` may change. A `resource &R` frames itself, so
   "undeclared mutation is impossible at the call boundary" is *enforced*
   rather than promised — `checksum_all` in the corpus proves its array
   comes back byte for byte, and there is no `modifies` clause anywhere in
   the language to get wrong.

4. **Resources are erased from the ABI.** The foreign function receives the
   pointer, the length, and the byte. Authority is a static notion
   (ADR 0024), so there is nothing to pass.

5. **An extern's return type is an ABI whitelist** — an integer, or
   nothing (`extern.returns_storage`) — and it may not be generic
   (`extern.generic`). Retained pointers, callbacks, and ownership transfer
   to foreign code are out of scope for v1, and a signature that cannot
   hand storage back is what makes passing borrowed storage to an extern
   *reasonable* at all.

   **Amended (ADR 0030), twice.** As first written this rule blacklisted
   raw and resource returns, which named the storage *types* and missed the
   container: a class may hold resource fields (ADR 0029), so returning one
   returns storage by another route. It is a whitelist now, and everything
   else — classes, options, arrays — waits until its ABI and its
   ownership-transfer meaning are deliberately specified. And the sentence
   this decision originally ended on ("rather than a promise about what the
   foreign code does") claimed too much: see the amendment under
   *Consequences*.

6. **The manifest goes inside the hashed content, not beside it.** ADR
   0018's artifact hash is over the generated Lean bytes, and an artifact's
   validity is mere existence of its `.ok` file. An artifact must therefore
   not survive a change to what it *trusted*: changing an audit id has to
   invalidate it exactly as changing a proof does. A comment header in the
   emitted file costs nothing and reuses the staleness machinery whole.
   Checked: `test.fill.v1` and `test.fill.v2` hash differently.

7. **The build status names the boundary.**

   ```text
   unsafe regions: 8
   extern assumptions: 2
     - test.checksum.v1 (c_checksum): ...
     - test.fill.v1 (c_fill): ...
   status: verified relative to audited boundary
   ```

   `fully verified` is reserved for a module that trusts nothing. Imports
   need no union step: the flat merge already puts a dependency's externs
   in the importer's program, so an importer's status names the boundary it
   inherited.

8. **Test shims are keyed on the audit id, not the name.** The id names the
   contract version the program was verified against, so that is the right
   key for the implementation that is supposed to match it. An unknown id
   **traps**; running the empty body as a no-op would let a contract appear
   to hold because nothing happened, which is the one outcome a monitor
   must never produce.

## Consequences

- **U4's brand rule was too blunt, and this rung found it.** It forbade
  passing branded storage to *any* function, which blocked the extern call
  outright. The right rule follows from a property of the language: with no
  globals and no raw- or resource-typed fields, a callee that cannot
  *return* storage cannot retain it either — its locals die with its frame.
  So only a signature returning raw or resource can launder a brand, which
  is exactly what decision 5 forbids for externs.

  **Amended (ADR 0030): that argument is compiler-checked for a verified
  callee and an audited promise for a foreign one.** Nothing stops C
  stashing a pointer in a foreign global and using it after the call
  returns, so for an `extern` the returnless signature does not *establish*
  nonescape — it states it, as part of what the audit id covers. The rule
  is unchanged and so is the code; what changes is which side of the
  audited boundary the reasoning sits on. (Resource fields also made the
  premise "no storage-typed fields" false outright; see ADR 0029.)

  Read decision 5 with this amendment: for a verified callee, "it cannot
  hand storage back" is a fact about the language; for a foreign one it is
  the audited contract's promise, and the whitelist is what keeps the
  promise small enough to audit.
- **`extern.generic` had to move from the checker to the parser.**
  Monomorphization drops an uninstantiated template before the checker sees
  it, and substitutes the parameters away on an instantiated one — leaving
  no generic extern for a checker rule to reject. A syntactic property
  belongs in the parser.
- **U4's unfalsifiable exposure obligation is now falsifiable.** Every
  operation in U4's surface preserved reconstructibility, so
  `expose.<a>.bytes` always closed. An extern whose post says the bytes
  become `uninit` fails it. Trusting a boundary is different from trusting
  the compiler, and this is where the difference shows.
- `Tok::Hash` joins the program lexer — `#[...]` was previously only clause
  syntax on `///` lines.

## Deliberately not decided

- **The rest of the manifest.** The plan lists machine profile and hash,
  intrinsics used, source `assume`s, defers, unsafe spans, and public
  interfaces exposing raw or resource types. Externs, unsafe-region counts,
  defers and assumes are surfaced today; the machine profile has no
  selection mechanism yet, and per-export slicing via the call graph is the
  refinement the plan already marks as optional for the prototype.
- **A real ABI.** Nothing is compiled or linked; `sable test` supplies
  deterministic shims. What is being established is the *contract* shape and
  the trust bookkeeping, which is what later rungs build on.
- **POSIX-shaped externs.** `open`/`read`/`write`/`close` with an affine
  `OpenFile` and an explicit `PosixWorld` are the second FFI benchmark, on
  purpose: a real `read(2)` adds file state, short reads, errors, and
  interruption, none of which the deterministic shim has to answer.
