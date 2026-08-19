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
2. **Parameter domain**: the eight integer types and, since the first G3
   owner tranche, direct ordinary (non-generic) classes. `bool`, records,
   arrays, options, and nested generic-class instances remain closed.
3. **Strategy: parse → expand → everything else.** A monomorphization
   pass clones each generic declaration once per distinct instantiation
   reachable from non-generic roots, substituting the parameter
   everywhere it occurs — including **as a token in proof-clause text**
   (so `T.max` in a contract becomes `i32.max`). The checker, VCgen,
   Lean emission, interpreter, and LSP see only ordinary declarations;
   the Lean encoding needs nothing new.
4. **Naming**: all-integer instances retain the legacy `Vec_i32` spelling.
   Any instance containing a class owner uses an injective, length-framed
   structural spelling which contains no program-relative class index.
   Diagnostics retain source spans in the generic declaration.
5. **Proof cost and provenance**: ADR 0009 permits proof reuse only when every
   argument is an integer covered by `Sable.IntModel`. Any instance containing
   a class owner receives `ProofReuse::None` and is checked and verified
   independently after substitution.
6. **Law-carrying trait bounds are deferred to the hash-map benchmark**
   (`T: Hashable` with hash-respects-equality), exactly as the goals doc
   schedules: Vec needs no bounds, so v1 ships without them rather than
   speculating.

## G0 recursive-type foundation (2026-08-12)

At the G0 checkpoint, ADR 0006's semantic domain remained the eight integer
types, but the compiler no longer represented that temporary limit as a flat
type-argument string. G0 made the widening path explicit and fail closed:

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
- At that checkpoint the semantic gate was unchanged: every argument that was
  not a concrete integer failed before checked types were built. The G3
  amendment below opens exactly direct ordinary classes.

G0 also closes deterministic pre-monomorphization failure paths: duplicate
traits, duplicate impl spec definitions, and duplicate impl methods diagnose the
second declaration in source order. Thus "G0 complete" means the recursive
representation/parser/identity/rejection foundation is complete; it does not
claim that the wider parsed types are language values yet.

The closure gate was the complete low-concurrency suite, not only focused parser
tests: 82/82 library tests; all 368 verifier, rejection, dynamic, and
dynamic-failure corpus subjects in 424.42s; LLVM CLI 6/6; the retained verified
program matching the interpreter and Clang at `-O0`/`-O2`; and SVM 69/69.

## G3 amendment: concrete class-owner arguments (2026-08-19)

Monomorphization now resolves a direct ordinary class name against the final
ordinary-class order and substitutes `Ty::Class(index)` into the generated
instance. A generated generic class is not itself an admissible argument:
nested generic-class owners remain a named, pre-mutation refusal until
fixed-point instance discovery can assign their class identities
deterministically.

This widens code specialization, not ADR 0009's abstract proof model. The
retained template is still checked over integer `Ty::Param` values. An
all-integer request keeps its legacy emitted name and integer-model proof reuse
byte for byte; a request containing any class owner uses the structural name,
receives `ProofReuse::None`, and is independently checked and verified with the
concrete affine class type. Boolean, record, array, option, and nested
generic-class arguments remain closed. Retained templates also continue to
reject generic-to-generic calls by name; this tranche does not add abstract
contract transport between templates.
