# ADR 0035 — Mandatory consumption is a resource-type property

**Decided 2026-08-12.** Field-level `#[must_consume]` established exact
ownership transfer inside one class, but passing the marked token to an
ordinary by-value parameter ended the obligation at the call boundary. That
means a do-nothing function was a valid sink. Release authority cannot depend
on that weaker rule.

## Decision

Compiler-defined resource kinds may be mandatory. `OpenFile` is the first
instance and the proving surface for the rule; `RawSpan`, `PointsTo<u64>`, and
`PosixWorld` remain affine and leakable.

Every owned place of a mandatory type carries an obligation. This includes:

- parameters on entry to a verified function, init, or method;
- results of compiler-sealed resource producers and function calls;
- locals and fields receiving a move; and
- class fields, without a separate field annotation.

Moves relocate the obligation. Returning authority removes it from the callee
and the mandatory return type establishes it again at the caller's receiving
place. Passing it to a verified function removes it from the caller only
because the callee's owned parameter independently inherits the same
obligation and every path through that body is checked. A direct return and a
unit fallthrough are both frame exits; neither may leave a mandatory parameter
or local behind. Discarding a fresh mandatory result as an expression statement
is the same abandonment and is rejected.

A class field of mandatory type makes `deinit` compulsory. Ordinary methods
may retain the obligation in `self`, because the object outlives the method;
the destructor must carry it to a terminal sink. The existing field-level
`#[must_consume]` remains available for a class that wants a stricter policy
over an otherwise affine resource such as `RawSpan`. That older policy still
means “must leave this owning destructor”; it does not change the resource
kind globally.

## Terminal operations

The first terminal operation is explicit in the audited boundary:

```sable
extern "C" #[audit(id := "posix.close.v2", reason := "...")]
fn posix_close(i32 fd, #[consumes] resource OpenFile fh,
               resource &mut PosixWorld w) -> i32;
```

`#[consumes]` is accepted only on an owned mandatory-resource parameter of an
extern. A verified Sable function may not assert it; its body must demonstrate
the chain to a terminal operation. An extern with an unmarked mandatory
parameter is rejected because it has no body to inspect, and marking an affine
resource is rejected because there is no mandatory obligation to discharge.

The attribute is an audited promise about foreign behaviour, so adding it
changes the contract. The POSIX shim's audit id is therefore versioned from
`posix.close.v1` to `posix.close.v2`. Future compiler-sealed operations such as
system deallocation may be terminal consumers by their sealed signatures; user
code cannot declare a sealed operation.

## Evidence and consequence

`mandatory_resources.sable` sends an `OpenFile` through a verified function
return and another verified wrapper before reaching `posix_close`. The RAII
handles no longer carry a field annotation: their destructors verify from the
resource type alone. Negative subjects pin a do-nothing sink, a returning path,
a discarded temporary, a mandatory field without `deinit`, a foreign parameter
missing `#[consumes]`, an attribute on verified code, and an attribute on a
non-mandatory resource.

This closes U8's consumption entry gate. It does not itself introduce
`SystemDealloc`, allocation leases, free, or coalescing; those operations may
now be designed on top of a rule strong enough to protect release authority.
