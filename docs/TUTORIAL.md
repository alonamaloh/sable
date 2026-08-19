# A tour of Sable

Every code block below is checked by `cargo test --test docs`, so if the
language moves and this page goes stale, CI says so.

Sable is one file holding two languages. Ordinary lines are a C-flavored
program language. Lines beginning with `///` are Lean 4, and they say what the
program *means*. `sable check` compiles the program and proves the claims; a
program that does not verify does not build.

```sh
compiler/target/debug/sable check hello.sable
```

## 1. A function and its contract

`pre` is what a caller must establish; `post` is what the function promises.
`result` names the returned value.

```sable
/// pre  b > 0
/// pre  a + b ≤ u32.max
/// post result = (a + b - 1) / b
fn div_round_up(u32 a, u32 b) -> u32 {
    return (a + b - 1) / b;
}
```

```
verified: div_round_up.sable — 4 obligation(s) across 1 function(s): 4 proved, 0 deferred, 0 assumed
status: fully verified
```

A `pre` is an assumption inside the body and an obligation at every call site.
A `post` is the reverse: an obligation at every exit, an assumption after every
call. Contracts are part of the signature — weakening a `pre` or strengthening
a `post` is backward compatible, and the reverse breaks callers.

That second precondition is not decoration. The design document's own version
of this example asked only for `a + b - 1 ≤ u32.max`, which permits
`a + b = 2³²` and overflows the intermediate sum; the compiler rejected it, and
`corpus/must-fail/overflow_design_doc.sable` now pins the mistake.

## 2. Arithmetic is exact

Integers are fixed-width, and there is no wraparound and no undefined
behavior. Every partial operation emits an obligation instead: `+ - *` must not
overflow, `/ %` need a nonzero divisor (and, when signed, not `MIN / -1`),
`a[i]` needs `i` in range. Unsigned subtraction is a partial operation too —
`a - b` needs `a ≥ b`.

```sable
// expect-error: overflow
/// post result = a + 1
fn inc(u64 a) -> u64 {
    return a + 1;
}
```

```
error: unproved obligation `inc.overflow.a_1`
   = goal: 0 ≤ (a + 1) ∧ (a + 1) ≤ u64.max
```

The fix is to say what you meant — `/// pre a < u64.max`. Clauses reason in
unbounded ℤ, so `u64.max` is a real number there, not a wrapped one.

Division is Euclidean, not C-truncating: the remainder is never negative, and
`/` and `%` agree exactly with Lean's integers.

```sable
/// post result = 3
fn euclidean() -> i32 {
    return -7 % 5;
}
```

Conversions between widths are explicit. `widen` is always safe; `narrow`
carries an obligation that the value fits.

```sable
/// post result = x
fn to_u64(u32 x) -> u64 {
    return widen<u64>(x);
}

/// pre  x ≤ 255
/// post result = x
fn to_u8(u64 x) -> u8 {
    return narrow<u8>(x);
}
```

(The design doc also describes `wrap`/`sat`/`checked` modifiers for when
modular or saturating arithmetic is *intended*. Those are not implemented yet —
`type.unknown_function` — so today every arithmetic operation is checked.)

## 3. Locals and control flow

Bindings are immutable unless declared `mut`. `var` infers the type. There is
no default zero — reading a local requires it to be initialized on every path.

```sable
fn pick(bool b) -> i32 {
    mut i32 x;
    if (b) { x = 1; } else { x = 2; }
    return x;
}
```

A function with no return type is a procedure: falling off the end returns, and
its posts are proven there. `&&` and `||` short-circuit, normatively — the
idiom `i < a.len && a[i] > 0` depends on it.

## 4. Loops need an invariant and a variant

The `invariant` is what stays true across iterations; the `variant` is a
quantity that strictly decreases, which is why the loop terminates.

```sable
/// post result = n
fn count_up(u64 n) -> u64 {
    mut u64 i = 0;
    /// invariant i ≤ n
    /// variant   n - i
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

After the loop the verifier knows the invariant *and* the negated condition —
`i ≤ n ∧ ¬(i < n)` is what proves `result = n`. A `for` loop over a range
carries its own bound, so it needs only an invariant.

```sable
/// post result ≤ a.len
fn count_nonzero(&[u64] a) -> u64 {
    mut u64 c = 0;
    /// invariant c ≤ i
    for (u64 i : range(0, a.len)) {
        if (a[i] != 0) { c = c + 1; }
    }
    return c;
}
```

## 5. Arrays: owned, lent, moved

`[T]` is an owned array — it owns its storage and there is exactly one owner.
`&[T]` lends it for reading and `&mut [T]` for writing; a borrow names the
caller's storage for the length of the call.

```sable
/// pre  m.len ≥ 1
/// post m.get 0 = 1
/// post m.len = (old m).len
fn set_first(&mut [u64] m) {
    m[0] = 1;
}
```

`old e` is the value of `e` at entry. In a contract an array lifts to a
sequence: `.len`, `.get k`, and quantifiers over indices.

An owned array can also be *moved* — returned out of a function, or passed by
value. Both hand the storage over: the source name dies, and the receiver owns
it.

```sable
/// post result.len = n
/// post ∀ k, 0 ≤ k → k < result.len → result.get k = 0
fn zeros(u64 n) -> [u64] {
    mut [u64] xs = alloc_array<u64>(n, 0);
    return xs;
}

/// pre  xs.len ≥ 1
/// post result = xs.get 0
fn head([u64] xs) -> u64 {
    return xs[0];
}

/// post result = 0
fn demo() -> u64 {
    [u64] xs = zeros(3);
    return head(xs);
}
```

What a caller learns about a returned array is its element domain and whatever
the posts say — *not* a length, unless a post states one. That is deliberate: a
`&mut` argument comes back as the same storage, so its length is preserved,
while a returned array is storage the caller never held. Using a moved array is
a compile error (`array.use_after_move`), and so is lending and moving the same
array in one call (`borrow.moved_in_call`).

See `corpus/verifies/array_passing.sable`, `array_return.sable`, and
`array_param.sable` for worked versions.

## 6. Options

`option<T>` replaces null. `.is_some` tests it; `.value` extracts it and
carries an obligation that the value is present. There is no pattern matching
in the program language — the accessors work identically in code and contracts.

```sable
/// post result.is_some ↔ a.len > 0
fn first(&[u64] a) -> option<u64> {
    if (a.len == 0) { return none; }
    return some(a[0]);
}
```

A contract *may* use `match`, since clauses are Lean:

```sable
/// post match result with
///      | some v => v = 1
///      | none   => true
fn one_or_nothing(bool b) -> option<u64> {
    if (b) { return some(1); }
    return none;
}
```

## 7. Naming a property

A `def` on a `///` line introduces a specification-only definition. It keeps
contracts short and gives the property one place to live.

```sable
/// def all_zero (a : Sable.Seq Int) : Prop :=
///   ∀ k, 0 ≤ k → k < a.len → a.get k = 0

/// post all_zero result
/// post result.len = n
fn make_zeros(u64 n) -> [u64] {
    mut [u64] xs = alloc_array<u64>(n, 0);
    return xs;
}
```

A recursive `def` also needs `termination_by` and `decreasing_by` — see
`corpus/verifies/bignum.sable`, which builds a whole lemma library this way.

## 8. When automation needs help

Routine obligations are closed by an in-Lean automation portfolio; there is no
SMT solver. When it cannot, name the obligation and prove it. `assert` states a
stepping stone at a program point, and `#[label(...)]` gives a clause a stable
name so the proof survives edits.

```sable
/// pre  x ≥ 3
/// pre  x ≤ 100
/// post result ≥ 9
fn square_lower(u64 x) -> u64 {
    /// assert #[label(sq_mono)]  x * x ≥ 3 * x
    /// assert #[label(sq_bound)] x * x ≤ 10000
    return x * x;
}

/// discharge square_lower.assert.sq_mono by
///   have h := Int.mul_le_mul_of_nonneg_right h_pre_x_3 (by omega : (0:Int) ≤ x)
///   omega

/// discharge square_lower.assert.sq_bound by
///   have h := Int.mul_le_mul_of_nonneg_right h_pre_x_100 (by omega : (0:Int) ≤ x)
///   omega
```

Nonlinear arithmetic is the usual reason: `omega` reasons about linear integer
arithmetic and will not multiply two variables for you. The error message gives
you the obligation's name, its goal, and the hypotheses in scope — hypothesis
names are content-derived (`h_pre_x_3`), so they do not shift when you edit
something unrelated.

An obligation's name is `<function>.<kind>.<slug>`, where the kind is what the
verifier was proving — `pre`, `post`, `inv_init`, `inv_preserved`,
`variant_decreases`, `assert`, `overflow`, `bounds`, `div_zero` — and the slug
comes from the clause's own text. That is what `#[label(...)]` pins: reword a
clause without a label and its slug changes, which orphans the `discharge` that
targeted it. An orphaned `discharge` is a compile error, never a silent no-op.

## 9. Classes

A `class` is a record with an invariant, constructors (`init`), a destructor
(`deinit`), and methods. The invariant is an obligation at the end of every
`init` and every `&mut self` method, and an assumption at every entry.

```sable
pub class Counter {
    u64 n;

    /// invariant n ≤ 100

    /// post self.n = 0
    init new() {
        self.n = 0;
    }

    /// post result → self.n = old self.n + 1
    /// post ¬result → self.n = old self.n
    fn bump(&mut self) -> bool {
        if (self.n == 100) { return false; }
        self.n = self.n + 1;
        return true;
    }

    /// post result = self.n
    fn get(&self) -> u64 {
        return self.n;
    }

    deinit {
    }
}

/// post result ≤ 100
fn use_it() -> u64 {
    mut var c = Counter::new();
    bool ok = c.bump();
    return c.get();
}
```

Class values are owned, like arrays: they move, and a moved-from place is not
destroyed again. On a non-trapping path, each live owner is destroyed exactly
once when its lifetime ends — on ordinary scope fallthrough, loop cleanup,
return unwinding, or replacement of an initialized destination. A trap
terminates immediately: Sable does not unwind the stack or run destructors or
array cleanup on that path. `corpus/verifies/bounded_stack.sable` is the
canonical example; `corpus/verifies/ownership.sable` walks the transfer rules.

## 10. Modules

One file is one module, named by its stem. `use` imports it, `pub` exports.

```sable
// geometry.sable
/// pre  w + h ≤ 1000
/// post result = 2 * (w + h)
pub fn perimeter(u64 w, u64 h) -> u64 {
    return 2 * (w + h);
}
```

```sable
// main.sable — checked with: sable check -M . main.sable
use geometry;

/// post result = 14
fn demo() -> u64 {
    return perimeter(3, 4);
}
```

`-M <dir>` adds a directory to the module search path. Imports are verified
separately: a caller reuses the callee's contract, not its body.

## 11. Running the program

`sable test` is a separate, Lean-free path: it interprets the program and
checks contracts dynamically. It is dev tooling, not a second checker of
record — but it is how you find a *wrong contract* fast, since a false post is
reported at the call that violates it.

```sable
// test_geometry.sable — run with: sable test -M . test_geometry.sable
use geometry;

/// pre x = y
fn expect_eq(u64 x, u64 y) {
}

fn test_perimeter() {
    expect_eq(perimeter(3, 4), 14);
}
```

```
test test_perimeter ... ok
test result: 1 passed, 0 failed
```

`test_*` functions are the entry points and are never verified. Clauses outside
the monitorable fragment are reported as skipped, never guessed.

`sable build --emit-llvm` lowers a verified program to LLVM IR. The native
backend covers less of the language than the verifier does, and says so by
name (`backend.unsupported`).

## 12. Escape hatches

Two, both counted in the build report and both greppable.

```sable
/// post result = a + b
fn add_unchecked(u32 a, u32 b) -> u32 {
    return a + b;
}

/// defer add_unchecked.overflow.a_b
```

`defer` compiles one obligation into a runtime trap — sound, and the program
still cannot go wrong silently. `assume` takes one as an audited axiom, which
is *not* sound, so its justification is mandatory:

```sable
/// post result = a / b
fn div_trusted(u32 a, u32 b) -> u32 {
    return a / b;
}

/// assume #[audit(reason := "the network layer validates b > 0 before dispatch")]
///        div_trusted.div_zero.a_b
```

Neither file reports `fully verified`; the status line says what was deferred
or assumed.

## Where to go next

- `corpus/verifies/` — 120+ programs that must verify, from `binary_search` to
  an arbitrary-precision bignum library. This is the real documentation: it is
  executable, and CI keeps it green.
- `corpus/must-fail/` — one program per diagnostic, each showing exactly what
  the compiler refuses and why.
- `docs/design/sable-language-design.md` — the normative design. It describes
  v0.4 in full, including parts not yet implemented; `docs/type-matrix.md` says
  which types actually work in which positions today.
- `docs/ARCHITECTURE.md` — how the compiler is put together, and
  `docs/decisions/` for the reasoning behind each settled question.
