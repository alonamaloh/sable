# ADR 0006 — Generics v1: explicit instantiation, monomorphize-then-check

**Decided 2026-08-09.** The Vec benchmark (goals doc, Tier 1) forces the
first cut of the generics design. Monomorphization-before-VC-generation
was committed long ago (design §12); this ADR fixes the v1 surface and
the compiler strategy.

1. **Surface**: type parameters on classes and functions —
   `class Vec<T> { [T] buf; ... }`, `fn swap_elems<T>(&mut [T] a, u64 i, u64 j)`.
   Instantiation is **always explicit**: `Vec<i32>::with_capacity(4)`,
   `swap_elems<u8>(&mut a, i, j)`. No inference in v1 — honest and
   unambiguous; inference is sugar that can come later without semantic
   change.
2. **Parameter domain v1**: the eight integer types. (`bool`, class-typed
   parameters, and nested instantiations come later; class fields still
   cannot be class-typed, so `Vec<Vec<T>>` is out of range anyway.)
3. **Strategy: parse → expand → everything else.** A monomorphization
   pass clones each generic declaration once per distinct instantiation
   reachable from non-generic roots, substituting the parameter
   everywhere it occurs — including **as a token in proof-clause text**
   (so `T.max` in a contract becomes `i32.max`). The checker, VCgen,
   Lean emission, interpreter, and LSP see only ordinary declarations;
   the Lean encoding needs nothing new.
4. **Naming**: instances are mangled `Vec_i32` (Lean structure names,
   theorem prefixes); diagnostics and obligation names display the
   pretty form `Vec<i32>::push`. Spans point into the generic source.
5. **Proof cost**: each instance is verified independently. Accepted for
   v1 (automation is cheap; instances differ in range facts anyway).
   Proving once and instantiating — a per-instance `∀`-quantified
   metatheorem — is future work tied to the metatheory track.
6. **Law-carrying trait bounds are deferred to the hash-map benchmark**
   (`T: Hashable` with hash-respects-equality), exactly as the goals doc
   schedules: Vec needs no bounds, so v1 ships without them rather than
   speculating.

## G0 recursive-type foundation (2026-08-12)

ADR 0006's semantic domain remains the eight integer types, but the compiler no
longer represents that temporary limit as a flat type-argument string. G0 makes
the widening path explicit and fail closed:

- `GenericTy` and opaque `CanonicalTypeKey` values recurse over integers,
  `bool`, type parameters, records, classes with arguments, arrays, and options.
  Calls and constructors retain each complete outer type's source span.
- The use-site parser accepts those shapes and shares one grammar between
  generic-call lookahead and AST construction. A recursive path is capped at 64
  nodes, every outer or nested argument list at 256 entries, and each outer
  argument at 4096 total nodes. Generic declarations separately retain their
  existing 256-parameter ceiling and duplicate-name rejection.
- Visible imported generic classes contribute names and arities through a table
  separate from the checked class-index table. This permits recursive nominal
  parsing without changing the indices seen by the checker and later stages.
- `InstanceKey` is structural: function/class kind, template base, and the
  original recursive canonical arguments. Its emitted spelling remains a
  presentation detail; ambiguous legacy spellings and collisions with source,
  template, or impl-lowered names are deterministic errors.
- The semantic gate is unchanged. Any argument that is not a concrete v1
  integer (after parameter substitution) is rejected as
  `mono.type_arg_unsupported` before checked types are built. Boolean/POD
  checking, verification, execution, and lowering belong to G1.

G0 also closes deterministic pre-monomorphization failure paths: duplicate
traits, duplicate impl spec definitions, and duplicate impl methods diagnose the
second declaration in source order. Thus "G0 complete" means the recursive
representation/parser/identity/rejection foundation is complete; it does not
claim that the wider parsed types are language values yet.

The closure gate was the complete low-concurrency suite, not only focused parser
tests: 82/82 library tests; all 368 verifier, rejection, dynamic, and
dynamic-failure corpus subjects in 424.42s; LLVM CLI 6/6; the retained verified
program matching the interpreter and Clang at `-O0`/`-O2`; and SVM 69/69.
