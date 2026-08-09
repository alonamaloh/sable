# Sable — Language Design

*Working draft 0.4 — subject to revision as real code generates friction.*

Sable is an imperative, C-flavored language in which every function carries a machine-checked proof of its contract. One source file interleaves two languages:

- The **program language**: C-like, no undefined behavior, fixed-width integers, classes with constructors/destructors (RAII), ownership-based memory model.
- The **proof language**: a Lean 4 dialect. *All* specification content — contracts, invariants, ghost definitions, lemmas, tactic scripts — lives on lines beginning with `///`.

## Design pillars

1. **No undefined behavior.** Every syntactically valid program has a meaning defined by a formal machine model. Anything that would be UB in C is either statically excluded by a proof obligation, has defined trap semantics, or — for the one case a runtime check would be unaffordable, reading uninitialized memory in *unchecked* code — lands in an explicit `undef` terminal outcome that verified programs provably never reach (ADR 0005).
2. **A formal machine model is the axiom base.** The default model is the Sable Virtual Machine (SVM, §10), formalized once in Lean. Proof obligations are theorems about machine traces. The SVM is a *semantic definition*, not a runtime: native compilation is (eventually verified) machine-behavior-preserving translation, and other machine models can sit below the same language (§11). The trusted base shrinks in **stages** (§10.1): initially the VC generator is trusted engineering, cross-checked by differential testing against the SVM formalization; a mechanized soundness proof of the VC generator — reducing trust to the machine formalization and the Lean kernel alone — is a scheduled long-running pillar, not a day-one claim.
3. **Ownership before logic.** The type system enforces unique ownership with borrowing (§5). Because mutable aliasing is impossible in safe code, the verifier reasons about values rather than heaps, and framing is a type-system fact, not a per-call proof obligation.
4. **Total verification, visible exceptions.** There are no build modes. An undischarged obligation is a compile error. The only ways past an obligation are written in the source, audited, and greppable: `defer` (sound runtime trap) and `assume` (unsound axiom) — §9.

---

## 1. One file, two languages

Any line whose first non-whitespace characters are `///` is a **proof line**; consecutive proof lines form a **proof block**. Everything else is program text. Ordinary comments use `//`.

Proof blocks bind **positionally**, in the style of documentation comments:

| A proof block that... | ...attaches to | May contain |
|---|---|---|
| immediately precedes a function | that function's signature | `pre`, `post` |
| immediately precedes a loop | that loop | `invariant`, `variant` |
| appears inside a class body | the class | `invariant` |
| immediately precedes a statement | that program point | `assert`, `defer`, `assume` |
| is free-floating (blank line separates it) | the enclosing module | `ghost def`, `theorem`, `discharge` |

A blank line between a proof block and the next item detaches it (making it free-floating). This whitespace sensitivity is identical to doc-comment behavior in Rust/D/Swift; it is normative.

**Rendering is normative tooling policy, not syntax.** The distinction that matters to readers is *obligation vs. evidence*:

- **Interface blocks** — those containing `pre`, `post`, or class `invariant` clauses — are promises to callers. Reference tooling MUST render them undimmed, surface them on hover at call sites, and include them in generated documentation.
- **Evidence blocks** — loop annotations, lemmas, tactic scripts, `discharge` directives — exist for the checker and the proof maintainer. Reference tooling SHOULD render them dimmed and support folding.

The classification is recoverable from block content alone, so one marker serves both without author ceremony. The design goal: *a reader may ignore proofs; no reader may be shown a function without its contract.*

Because contract expressions are unambiguously proof-language, they use real Lean-dialect syntax — `∀`, `match`, unicode operators — with ASCII equivalents (`forall`, `->`, `/\`) accepted.

## 2. The program language

### 2.1 Types

| Kind | Types |
|---|---|
| Integers | `i8 i16 i32 i64 u8 u16 u32 u64` — fixed width; no silent wraparound (§2.2) |
| Boolean | `bool` |
| Floating | `f32 f64` (IEEE-754; verification limited to range/NaN facts in v0.4) |
| Aggregates | `struct`; fixed arrays `T[N]`; owned dynamic arrays `[T]` (length-carrying) |
| Classes | `class` — structs with invariants, constructors, destructors (§7) |
| References | `&T` shared/immutable borrow; `&mut T` unique/mutable borrow |
| Options | `option<T>` with `.is_some`/`.value` accessors (`.value` carries a someness obligation — ADR 0008; **no pattern matching in the program language**, as a standing principle); there is no null |

Proof-side (ghost) types — usable only on `///` lines: `int` (unbounded ℤ), `nat`, `seq<T>`, `set<T>`, `map<K,V>`, `Prop`. Program values lift implicitly into proof terms: an `i32` lifts to an `int` with the fact that it lies in `[-2³¹, 2³¹)`; arrays lift to `seq<T>` with their length fact. There is no reverse lifting.

### 2.2 Arithmetic: obligations, not UB, not silent wrapping

Every partial operation emits a verification condition (VC):

| Expression | Obligation |
|---|---|
| `a + b`, `a - b`, `a * b` | result representable in the operand type |
| `a / b`, `a % b` | `b ≠ 0`; for signed `/`, additionally not `MIN / -1` |
| `a[i]` | `0 ≤ i < a.len` |
| `narrow<u8>(x)` | value fits in the target type |

Division is **Euclidean**, not C-truncating: `a = b*(a/b) + a%b` with `0 ≤ a%b < |b|` — the remainder is never negative, and `/`/`%` coincide exactly with the proof language's (Lean core's) integer division (ADR 0004).

Total operators exist for when modular or saturating behavior is *intended*; they emit no VC. They are operator **modifiers**, not functions: every arithmetic operator lexically inside the form is modular/checked/saturating in its operand type's width (not crossing into called functions or index computations); signed `wrap` is two's-complement (ADR 0005):

```sable
u32 h = wrap(seed * 2654435761);   // modular arithmetic, defined
u8  c = sat(x + y);                // clamps to [0, 255]
option<i32> s = checked(a + b);    // none on overflow
i64 w = widen<i64>(x32);           // widening is always total
```

Contracted total intrinsics expose double-width arithmetic for library code (these are the axioms limb-level code builds on, and where the machine model meets real ISAs):

```sable
/// post (result.1 : nat) * 2^64 + result.0 = (a : nat) + b + (if cin then 1 else 0)
fn carrying_add(u64 a, u64 b, bool cin) -> (u64, bool);

/// post (result.1 : nat) * 2^64 + result.0 = (a : nat) * b
fn mul_wide(u64 a, u64 b) -> (u64, u64);   // (lo, hi)
```

**Evaluation order is left-to-right and `&&`/`||` short-circuit — normatively** (ADR 0005). Trap identity depends on the former (for `a[i] = e`: index, then value, then the bounds check); the guarded-VC idiom `i < a.len && a[i] > 0` depends on the latter.

### 2.3 Definite initialization

Reading a location requires a proof that it was initialized on every path — discharged by flow-sensitive typing in the common case, by the general verifier when control flow depends on proved facts. There is no default zero. The machine model represents uninitialized memory as `⊥`; a ⊥-read sends the machine to the explicit `undef` terminal outcome (so even unchecked programs have a defined meaning), and the soundness theorem (§10) states that verified programs never reach it.

```sable
fn pick(bool b) -> i32 {
    i32 x;
    if (b) { x = 1; } else { x = 2; }
    return x;                       // ok: initialized on all paths
}
```

## 3. Contracts

Contracts are proof-language declarations in the block preceding a function. `pre` clauses are assumptions inside the body and obligations at every call site; `post` clauses are obligations at every exit and assumptions after every call. `post` may mention `result` and `old e` (value of `e` at entry).

```sable
/// pre  b > 0
/// pre  a + b ≤ u32.max            -- in ℤ; makes the body's `a + b` provable
/// post result = (a + b - 1) / b   -- division in ℤ agrees with u32 here (provable)
fn div_round_up(u32 a, u32 b) -> u32 {
    return (a + b - 1) / b;
}
```

Functions without a return type are procedures: falling off the end returns, and posts are proven at that implicit exit (ADR 0005). A call site that cannot prove a `pre` fails to compile, and the error quotes the clause. Contracts are part of a function's *signature* for all purposes: documentation, semantic versioning (weakening a `pre` or strengthening a `post` is backward compatible; the reverse is breaking). Overload resolution never depends on them.

Contract clauses may freely reference ghost definitions (§6). This keeps interface blocks short: a rich property gets a *name* in the contract and a *definition* in an evidence block.

## 4. Loops: invariants and variants

Loop annotations are evidence, not interface — they live in a proof block immediately before the loop, dimmed and foldable. Every loop requires an `invariant` (inductive property) and a `variant` (a ghost `nat` that strictly decreases, proving termination — see §8 for `partial`).

```sable
/// pre  a.len ≤ 2^32
/// post result = spec_sum a 0 a.len
fn sum(&[i32] a) -> i64 {
    i64 acc = 0;
    u64 i = 0;
    /// invariant i ≤ a.len
    /// invariant acc = spec_sum a 0 i
    /// invariant acc.abs ≤ i * i32.max      -- why the addition below can't overflow
    /// variant   a.len - i
    while (i < a.len) {
        acc = acc + widen<i64>(a[i]);
        i = i + 1;
    }
    return acc;
}

/// def spec_sum (a : seq i32) (lo hi : nat) : int :=
///   if lo ≥ hi then 0 else (a.get lo : int) + spec_sum a (lo+1) hi
```

Collapse the `///` lines and the function reads as plain C with a two-line contract. The third invariant is representative of verified programming in practice: the compiler forces you to state *why* nothing overflows, and the bound lives with the proof, not the interface. Invariants change constantly during proof development; because those edits are `///`-only, the executable program has zero diff noise.

**Counted loops are sugar.** `for (u64 i : range(n))` and `for (T i : range(lo, hi))` desugar to the `while` above with the bounds invariant (`lo ≤ i ∧ i ≤ hi`), the variant (`hi - i`), and the increment synthesized — the simplest loops carry zero annotation. Extra `invariant` clauses attach above the `for` as usual; the body may not assign the index or any variable the bounds mention (bounds must be loop-invariant), and `range(lo, hi)` obliges `lo ≤ hi` at entry.

## 5. Memory model: ownership + borrows

Affine ownership with lexically scoped borrowing — the Rust discipline, simplified (no surface lifetime annotations in v0.4).

1. Every value has one owner. Assignment and by-value passing **move** ownership unless the type is `copy` (scalars are). A moved-from variable is statically dead.
2. `&x` creates shared borrows: any number may coexist; no mutation through them; the owner is frozen while they live.
3. `&mut x` creates a unique borrow: exactly one; mutation allowed; the owner is inaccessible meanwhile.
4. When the owner of a `class` value dies, its destructor runs (§7), in reverse declaration order — defined, like everything else.
5. Shared mutable state goes through the library type `cell<T>` carrying a declared invariant; every access is a method call whose contract preserves it.

Why ownership rather than a flat heap with separation logic: with a flat heap, every function needs footprint annotations and the proof layer stops being optional reading. Under ownership, framing, definite initialization, absence of use-after-free, and single-destruction are theorems of the *metatheory*, proved once — the per-program verifier sees an essentially functional program with mutation localized to uniquely-owned values. Empirically this is why ownership-based verifiers (Verus, Creusot) discharge obligations orders of magnitude faster than heap-logic tools. The machine-model heap is a partial map `Addr ⇀ Val ∪ {⊥}`; the metatheory's target theorem is that the ownership discipline implies the separation-logic frame rule for all safe code. Mechanizing that theorem is part of the staged metatheory pillar (§10.1) — the nearest precedent, RustBelt, was a multi-year team effort for a fragment of Rust, and Sable's deliberately smaller surface (lexical borrows, no closures, no lifetimes) is what keeps it tractable.

```sable
/// post *a = old *b ∧ *b = old *a
fn swap(&mut i32 a, &mut i32 b) {
    i32 t = *a;  *a = *b;  *b = t;
}
// swap(&mut x, &mut x) is not a verification failure — it is a type error.
```

An `unsafe` sublanguage (raw regions, manufacturing ownership from bytes) is deliberately unspecified in v0.4; its design is a scheduled deliverable of the allocator benchmark (see the goals document), with full separation-logic obligations expected at the safe/unsafe boundary. FFI rides on the same design. This deferral is correct for the benchmark-driven phase, but it should be named for what it is: **the gate between research artifact and usable language**. A systems language that cannot call anything is a proof pipeline with syntax; no adoption claim can be made before the unsafe/FFI boundary lands.

## 6. Ghost code

`ghost def` introduces specification-only functions and predicates; `ghost` variables may appear in program bodies for proof bookkeeping. The compiler erases all ghost content; the metatheory proves erasure sound (ghost code cannot influence real control flow or data).

```sable
/// def sorted (a : seq i32) : Prop :=
///   ∀ i j, 0 ≤ i → i < j → j < a.len → a.get i ≤ a.get j

/// pre  sorted a
/// post match result with
///      | some i => 0 ≤ i ∧ i < a.len ∧ a.get i = key
///      | none   => ∀ k, 0 ≤ k → k < a.len → a.get k ≠ key
fn binary_search(&[i32] a, i32 key) -> option<u64> {
    u64 lo = 0;
    u64 hi = a.len;
    /// invariant hi ≤ a.len
    /// invariant ∀ k, 0 ≤ k → k < lo → a.get k < key
    /// invariant ∀ k, hi ≤ k → k < a.len → key < a.get k
    /// variant   hi - lo
    while (lo < hi) {
        u64 m = lo + (hi - lo) / 2;
        if      (a[m] < key) { lo = m + 1; }
        else if (a[m] > key) { hi = m; }
        else                 { return some(m); }
    }
    return none;
}

/// -- Evidence: shrinking the interval preserves the "outside is ≠ key"
/// -- invariants only because the array is sorted; instantiating the
/// -- sortedness quantifier is beyond automation, so the obligation is
/// -- discharged by name with a tactic script.
/// discharge binary_search.inv_preserved.«∀k<lo» by
///   intro k hk0 hk
///   by_cases hklo : k < lo
///   · exact h_inv_2 k hk0 hklo
///   · by_cases hkm : k = lo + ((hi - lo) / 2)
///     · rw [hkm]; exact h_path
///     · calc a.get k ≤ a.get (lo + ((hi - lo) / 2)) :=
///             h_sorted k _ hk0 (by omega) (by omega)
///         _ < key := h_path

(Sequence indices are ℤ, like every lifted program value; quantifiers over
indices carry explicit `0 ≤ k` guards, and `a.get` is total with junk off
range. A `nat`-indexed `seq` was tried first and does not elaborate against
ℤ-lifted bounds — the checker commits `k : ℤ` at the comparison before ever
seeing `get`.)
```

Every obligation has a stable, **content-anchored** name: the enclosing declaration, the clause kind, and a source anchor derived from the clause's own structure (here, the `none` match arm) or an explicit `#[label(...)]` on the clause. Names are never positional indices — inserting a statement must not renumber obligations and silently orphan `discharge` blocks. `discharge NAME by TACTIC` targets one obligation; if an edit changes a clause enough that its anchor no longer resolves, the orphaned `discharge` is itself a compile error, never silently dropped. Undischarged obligations are compile errors printing the name, the goal, the context, and the automation portfolio's diagnosis.

*(Implementation status, v0.4: there is no SMT solver anywhere — routine obligations are closed by an automation portfolio inside Lean (`omega`, `grind`, `simp`) and every proof, automated or hand-written, is checked by the Lean kernel; see ADR 0002. The seam that was expected to be the highest-risk engineering — presenting failed goals with stable, nameable hypotheses — is implemented: hypothesis names are content-anchored (`h_pre_sorted_a`, `h_inv_<slug>`, `h_path_<slug>`), so `discharge` scripts survive unrelated edits. Obligation-name anchors are currently expression slugs; the `#[label(...)]` form described above is not yet implemented.)*

## 7. Classes, invariants, RAII

A `class` is a struct with invariants, constructors (`init`), and a destructor (`deinit`). The class invariant is declared in a proof block inside the class body and is an **interface block** — undimmed, in docs — because it is shorthand for a conjunct in the `pre` and `post` of every public method.

The desugaring is normative and slightly asymmetric:

- **Obligation** at the exit of every `init` and every public method taking `&mut self`.
- **Assumption** at the entry of every public method and of `deinit`.
- **Not in force** mid-method, or for private methods (which state explicitly which invariant conjuncts they require/preserve). This permits a method to break the invariant temporarily between statements.

```sable
class BoundedStack {
    [i32] buf;
    u64  len;

    /// invariant len ≤ buf.len
    /// invariant buf.len > 0

    /// pre cap > 0
    init with_capacity(u64 cap) {
        self.buf = alloc_array<i32>(cap, 0);
        self.len = 0;
    }                                  // invariant proved here

    /// post result  → self.len = old self.len + 1 ∧ self.buf.get (old self.len) = x
    /// post ¬result → self = old self
    fn push(&mut self, i32 x) -> bool {
        if (self.len == self.buf.len) { return false; }
        self.buf[self.len] = x;        // bounds VC: branch condition + invariant
        self.len = self.len + 1;       // overflow VC: len < buf.len ≤ u64.max
        return true;
    }                                  // invariant re-proved here

    /// post old self.len = 0 → result = none
    /// post old self.len > 0 → result = some (self.buf.get (old self.len - 1))
    fn pop(&mut self) -> option<i32> {
        if (self.len == 0) { return none; }
        self.len = self.len - 1;
        return some(self.buf[self.len]);
    }

    deinit {
        // buf is owned; its own deinit frees it after this body.
    }
}

fn demo() {
    var s = BoundedStack::with_capacity(4);
    let _ = s.push(7);
}   // s.deinit() runs here — provably exactly once, by ownership
```

Double-free and use-after-free are unrepresentable rather than unproven.

## 8. Termination and partiality

Functions are total by default: loops need a `variant`, recursion needs a decreasing measure, and the call graph is checked for well-founded descent.

```sable
/// post result = spec_gcd a b
fn gcd(u64 a, u64 b) -> u64
/// variant b
{
    if (b == 0) { return a; }
    return gcd(b, a % b);              // a % b < b : the descent VC, automatic
}
```

`partial fn` opts out: only partial-correctness obligations ("*if* it returns, `post` holds"); partiality is transitive to callers unless a caller proves a variant at the call site. Servers and event loops live here, honestly labeled. `partial` is part of the signature and appears in documentation.

Totality-by-default has a systems payoff: any interface whose functions are ordinary (non-`partial`) is *finite* in the sense exploited by push-button kernel verification (Hyperkernel/Serval) — bounded, terminating, amenable to full SMT exploration. In Sable that discipline is the default semantics rather than a convention.

## 9. Escape hatches: `defer` and `assume`

There are **no build modes**. One source file has one meaning; an undischarged obligation does not compile. The only ways past an obligation are declarations written in the source, local, visible in diffs, and tallied in every build report:

```sable
    /// defer overflow(acc + widen<i64>(a[i]))
    // sound: compiles this one VC to a defined runtime trap (panic with the
    // obligation name). Everything proved downstream remains true — the
    // deferred predicate is "true or halt", never assumed.

    /// assume #[audit(reason := "vendor guarantees DMA buffer alignment")]
    ///        aligned(buf, 64)
    // unsound: an axiom. If false, downstream theorems are vacuous. Legal only
    // with an #[audit] payload; intended for facts about the world outside the
    // machine model (FFI, hardware), not for skipping hard proofs.
```

- `defer P` may target any *runtime-monitorable* obligation — quantifier-free, or quantifiers over statically bounded ranges (compiled to checking loops). Classically-quantified or ghost-typed obligations cannot be deferred; they must be proved or assumed.
- Build output reports per package: `assumes: N (listed), defers: M (listed)`. Zero of both is **fully verified** — a property of code, not of build configuration, expected to be badged by package registries. This yields an in-source assurance ladder in the SPARK Bronze/Silver/Gold tradition.
- Ecosystem norm: `defer` is scaffolding ratcheted toward zero (CI can forbid increases); `assume` is a permanent, reviewed trust statement about the environment.

Rationale for keeping a sound trap-fallback at all: without `defer`, schedule pressure funnels into `assume` — and an unproved-but-monitored predicate ("true or halt") is strictly safer than an unproved-and-assumed one.

*(Implementation status, v0.4: `defer` and `assume` are implemented as module-level clauses naming an obligation — `/// defer NAME`, `/// assume #[audit(reason := "...")] NAME` — mirroring `discharge`'s workflow; the statement-attached `kind(expr)` form shown above is not yet implemented. Tallies and the fully-verified status line work as specified.)*

**Testing before proving.** Specifications are code and have bugs; the cheapest way to find a wrong `post` is to run it. The `sable test` tool executes test functions with all monitorable contracts checked dynamically and all proof obligations skipped. It is a development tool in the sanitizer category: its artifacts cannot be released or depended upon, so it is not a language mode and creates no dialect. Workflow: write contracts → test them dynamically → prove them.

## 10. The SVM in one page

The default machine model is deliberately boring: a **structured (AST-level) small-step semantics** (ADR 0005 — the earlier "typed stack machine" framing is retired; a lower-level machine may appear later as a compilation target with a refinement proof, not as the language's meaning).

- **Configuration**: `⟨continuation, locals, ghost⟩` with three terminal outcomes: `done v`, `trapped t`, and `undef` (⊥-reads in unchecked code). Locals hold `Val ∪ ⊥`; ownership absorbs the heap (arrays and class values are owned values); `ghost` holds specification state erased from real execution (its transitions are scheduled work, tied to the erasure metatheorem).
- **Semantics**: small-step for statements, big-step for the pure expression layer (calls are A-normalized to statement level, so expressions cannot diverge); deterministic given the allocation-capacity parameter `cap` (OOM is the defined trap above it; soundness quantifies over `cap`); left-to-right, short-circuiting. Formalized in Lean as inductive relations — the first draft (`lean/Sable/SVM.lean`) has 73 rules for the core subset, roughly half of them explicit trap propagation. This artifact is the language's meaning — there is no prose abstract machine to disagree with it.
- **Soundness theorem** (the metatheory's target statement): *if every VC of program P is a theorem, then no execution of ⟦P⟧ reaches `undef`, executes a partial operation outside its domain, violates a contract, or — absent `partial` — diverges; and every `defer`red predicate either holds or the execution ends in a named trap.* When mechanized (§10.1, stage 2), the compiler is untrusted; the theorem, the machine formalization, and the Lean kernel are the trusted base.
- Allocation failure is defined behavior: `alloc_array` halts in a named OOM trap. Top-level correctness claims therefore read "every execution either satisfies the contract or halts in the OOM trap." (A `try_alloc` returning `option` exists for callers that must handle exhaustion.)

*(Formalization status: a first 73-rule draft of these semantics exists at `lean/Sable/SVM.lean` — core subset: expressions with trap outcomes, statements, loops; classes and calls scoped out. Writing it surfaced eleven ambiguities in this section's prose; all eleven are now resolved in ADR 0005 and folded into this document (the `undef` outcome, modifier scope, the AST-level machine, A-normalized calls, normative evaluation order and short-circuiting, the capacity parameter, procedures, and the minor batch), with ghost transitions and trap-payload observability explicitly deferred. The formalization still needs the `undef` outcome added; audit trail in `docs/notes/svm-draft.md`.)*

### 10.1 The trusted base, in stages

The soundness story is deliberately staged, because a mechanized VCgen soundness proof is RustBelt-scale work that sits on the critical path of nothing in the near-term goals:

- **Stage 1 (from day one)**: the SVM step relation is formalized in Lean and is the language's normative meaning. The VC generator is *trusted engineering* — the same trust posture as Verus and Creusot today — but it is cross-checked continuously: the SVM formalization is executably testable via the reference interpreter (and later the self-hosted SVM interpreter, which doubles as a differential-testing oracle for every compiler question).
- **Stage 2 (its own long-running pillar)**: mechanize the soundness theorem — VCgen correctness against the step relation, ghost-erasure soundness, and the ownership-implies-frame-rule metatheorem of §5. This retires the VCgen from the trusted base. It is scheduled as an explicit tier in the goals document, not implied by the design.

Claims made about verified Sable programs must name the stage they rest on.

## 11. Profiles and alternative machine models

The SVM is one machine model, not a commitment. Two mechanisms keep the language portable downward toward bare metal:

- **`#[freestanding]` profile**: no implicit allocator — `alloc_array` and growable `[T]` are unavailable; only stack values, `T[N]`, and statically declared regions; `panic` becomes a user-supplied handler. This *shrinks* the trusted base (the OOM story vanishes) and serves embedded targets on its own.
- **Alternative machine layers**: the same language can be proven against a formalized hardware model (e.g., the Sail RISC-V or ARM machine-readable specs) instead of the SVM, with privileged operations (page-table writes, interrupt control) exposed as contracted `unsafe` intrinsics specified against that model — the seL4 architecture, with Sable in place of C. Native compilation is validated per-build (translation validation) before any verified-compiler pillar exists.

## 12. Deliberately missing from v0.4

Concurrency (rely-guarantee with ghost resources), the `unsafe` sublanguage and FFI (design deliverable of the allocator benchmark, and the gate to any adoption claim — §5), closures capturing borrows, floating-point verification beyond range facts, surface lifetime annotations for non-lexical borrows, and richer generics (non-integer type arguments, multiple/inherited trait bounds — v1 of generics and law-carrying bounds exists per ADR 0006/0007). Each has known literature; none blocks the core.

One generics decision is committed upfront rather than left to the benchmark, because it constrains everything downstream: **monomorphization before VC generation** (Verus's route). *(v0.4+ implementation: generics v1 exists per ADR 0006 — type parameters on classes and functions over the integer types, always-explicit instantiation (`Vec<i32>::with_capacity(4)`), expansion between parse and typecheck so no downstream stage sees a type variable, `T` substituted even inside proof-clause text so `T.max` works, instances verified independently. Law-carrying trait bounds landed with the hash-map benchmark (ADR 0007): a trait pairs a spec-level function (`/// spec hash : int → int`, referenced `Self::hash`/`K::hash`) with a program method contracted against it — the equation is the law that restores determinism and spec-level application; impls provide the spec function as a ghost def plus bodies verified against the trait contract, and monomorphization consumes the whole mechanism. v1 limits: bounds over the integer types, one bound per parameter, no inheritance or default bodies.)* Generic code is specialized before verification conditions are produced, so the VCgen, the Lean encoding, and the eventual metatheory (§10.1) never see type variables. The hash-map benchmark drives the surface design — trait syntax, law-carrying bounds, contract inheritance — not the compilation strategy. Retrofitting generics into a VCgen and a soundness proof is famously painful; fixing this early is deliberate risk reduction, at the known cost of code-size blowup and no polymorphic compilation, both acceptable for a verification-first systems language.

## Appendix A — the reader's contract, restated

- `//` — comment. For humans only.
- `///` — proof language. For the checker; classified by content:
  - `pre` / `post` / class `invariant` → **interface**: undimmed, in docs, on hover.
  - everything else (loop annotations, `ghost def`, `theorem`, `discharge`, `defer`, `assume`) → **evidence**: dimmed, foldable.
- A blank line detaches a proof block from the item below it (doc-comment rule).
- No build modes. `defer` = sound trap, counted. `assume` = audited axiom, counted. Zero of both = fully verified, and the registry says so.
