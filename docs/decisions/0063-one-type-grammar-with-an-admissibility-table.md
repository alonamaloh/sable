# ADR 0063 — one type grammar, with admissibility as an explicit table

**Decided 2026-08-15.**

## Context

The parser had eleven hand-written type parsers — `param_ty`, `ret_ty`,
`record_field_ty`, `option_ty`, `option_value_ty`, `array_payload_ty`,
`for_index_ty`, `raw_ty`, `resource_ty`, `scalar_ty`, and `int_ty` — one per
position, each spelling its own subset of the grammar. A twelfth, better
grammar already existed beside them: the bounded recursive parser that reads
generic type arguments (ADR 0006), which spells the whole language and shares
one syntax routine between lookahead and AST construction.

Three things followed from that arrangement.

**Where a type may be written was implicit.** A position admitted exactly what
the parser its caller happened to reach could parse. Nothing stated the policy,
so answering "may a record be a class field" meant reading a parser, and two
parsers for near-identical positions could disagree without anything noticing.

**A refused shape produced a parse error.** Writing `[u64]` as a record field
reached `parse.expected`, and a record as an array element reached
`parse.unknown_type`: diagnostics that point at a token and report that no type
was found, when a type was in fact written and the real answer is that this
type is not admitted here. `docs/type-matrix.md` recorded those two names as
the closing diagnostic for twenty-seven of its fifty closed cells — which is
not a language rule, it is a report of which parser ran out of alternatives.

**Every widening touched several parsers.** Admitting a shape in one more
position meant editing that position's parser and its error text, and there was
no place where the result could be read as a whole.

## Decision

**One parse, one lowering, three projections.** `parse_type_syntax_at` reads
the prefix forms — `&T`, `&mut T`, and `resource K` — over
`parse_type_core_at`, the prefix-free recursive core that reads nominal records
and classes, integer widths, `bool`, type parameters, `[T]`, `option<T>`,
`raw<T>`, and resource kinds. `Parser::lower_type(syntax, pos)` is the single
recursive lowering. The three entries — `Parser::ty`, `Parser::value_ty`,
`Parser::int_ty` — differ only in the result type they narrow to (`Ty`,
`ValueTy`, `IntTy`); they parse and lower identically. The generic-argument
bounds become the bounds on every declared type: at most 64 nodes deep, at most
256 entries in an argument list, at most 4096 nodes in one type.

> **ADR 0064 supersedes the `Parser::value_ty` entry in that list.** `ValueTy`
> is deleted; the surviving entries are `Parser::ty` and `Parser::int_ty`.

**Admissibility is an explicit table.** `Parser::admits(shape, pos) -> bool` is
one match, keyed by the shape of the type and the position it was written in,
and it is the language's whole shape policy for types. It is a table rather
than an implicit consequence of which parser a caller reached for four reasons:

* it can be read. The whole policy is one screen, so a question about one cell
  is answered without reading a parser, and two positions that should agree
  can be seen agreeing;
* it is complete by construction. A new position must be given a gate name, a
  noun phrase, and a rejection note, all of which are exhaustive matches on
  `TyPos`, and a place in the position chain the audits walk; a new shape must
  be given a place in `TypeShape::after`, and every row then refuses it until
  it is listed, so the failure direction of an unfinished edit is closed;
* the diagnostic is generated from it. `admitted_spellings` reads the same
  table to build the "expected …" line, so the sentence a user is shown cannot
  drift from the rule that produced the rejection;
* it is pinned against the representations. `admitted_shapes_match_their_lowering`
  checks every admitted (shape, position) pair against what that position's
  lowering can actually hold, so a spelling the table admits can never reach an
  unhandled case, and a future table edit that overreaches fails there rather
  than in a program.

Each position carries a stable gate name (`TyPos::gate_name`), a noun phrase
for the position, and a rejection note keyed by the (shape, position) pair, so
a rejection explains the type that was written rather than the position's most
common refusal. The fifteen gate names are `type.param_unsupported`,
`type.borrow_param_unsupported`, `type.return_unsupported`,
`type.local_unsupported`, `type.record_field_unsupported`,
`type.class_field_unsupported`, `type.array_payload_unsupported`,
`type.option_payload_unsupported`, `type.for_index_unsupported`,
`type.const_unsupported`, `type.cast_target_unsupported`,
`type.impl_target_unsupported`, `type.raw_element_unsupported`,
`type.resource_extent_unsupported`, and `type.resource_map_key_unsupported`.
Two arity names join them, `parse.raw_type_arity` and `resource.type_arity`,
and five names lose a `generic` they no longer earn now that one production
reads every type rather than only a generic argument list:
`parse.expected_type`, `parse.array_type_close`, `parse.type_arg_separator`,
`parse.type_too_deep`, and `parse.type_too_large`.

Array elements and option payloads share their gate name with the checker rules
that refine them, deliberately: the parser refuses the shapes the payload
representation cannot hold, the checker refuses the ones it can hold but has no
semantics for, and a reader asking what may go there gets one answer either
way. The name answers a question about the language, not about which stage
answered it.

## What the table does not own

The table decides shapes, and only shapes. Three other kinds of rule stand
between a spelling and an accepted program, and none of them belongs in it.

**Which spellings of an admitted shape exist.** `lower_raw_type` decides that
`raw<u8>` and `raw<Record>` are the raw pointers that exist; `lower_res_kind`
decides which resource kinds the compiler defines, since a program may not
declare one; `lower_option_type` sorts an admitted payload into the three
option families the representation distinguishes. These look past the shape at
the type, which is exactly what a shape table cannot do.

**Which option family a payload names.** `option<[T]>` and `option<raw<R>>`
are gated by the `OptionPayload` row like any other payload — the row admits
`S::Array` and `S::Raw`, and `lower_option_type` consults it for both before
doing anything else. What the table does not decide is *which of the three
families results*: an array payload becomes `Ty::AffineOption`, a raw-record
payload becomes `Ty::OptionRaw`, and everything else becomes a copyable
`Ty::Option`. That choice is made from the payload's syntax, after the row has
already admitted it.

**What a position demands beyond a spelling.** `local_needs_initializer` is a
rule about locals that no shape implies. The checker's payload, ownership, and
layout gates — `record.field_type`, `type.bool_array_param`,
`type.field_array_move`, the affine-option boundary — own the rejections they
can say more about than a grammar could, and several positions admit a shape
precisely so that those gates are reached. Admitting a shape is never a promise
that the program checks.

What stays in the table is the complement: the rejections with no downstream
equivalent, either because the position's representation cannot hold the shape
at all or because letting it through would commit the compiler to semantics it
does not have. The complete list is the match itself; this document
deliberately does not copy it, because a copy drifts.

## Consequences

**A shape now reaches a named semantic gate instead of a parse error.** Writing
a type the position refuses produces the position's own diagnostic — its name,
its noun phrase, the spellings it admits read off the table, and a note keyed
to the pair — pointing at the type's span. `docs/type-matrix.md` records that
directly: the cells that `parse.expected` and `parse.unknown_type` used to
close are now closed by the position gates, so the matrix reports language
rules rather than which parser ran out of alternatives.

**The grammar remains the rule in exactly one place.** Borrow and resource
prefixes are read by the outer production, not the recursive core, so a position
nested inside a type — array element, option payload, a class or record type
argument — cannot spell them, and `[&T]` is a parse error rather than a gate
rejection. That is deliberate: no nested representation for either shape exists,
so there is nothing for a gate to explain.

Two argument lists are outer positions despite their angle brackets:
`alloc_array<T>` and `widen`/`narrow<T>` name a type the surrounding expression
is about, not a component of one, so they read the outer production and answer
`alloc_array<&u64>` with the array-element gate rather than with
`parse.expected_type`. The gate is the better answer — it names the shape and
the position — and the cost is that the same shape is a parse error in `[&u64]`
and a gate rejection here. Both refuse; only the diagnostic differs.

**A type parameter shadows a nominal type of the same name.** `lower_named_type`
resolves type parameters before visible classes and records, so inside
`fn first<Pair>(Pair p)` the name `Pair` is the binder even when a record `Pair`
is in scope. This is a change: the previous position-specific parsers disagreed
with each other — parameter and return positions resolved nominals first while
use-site type arguments resolved binders first — which made a declaration
incoherent with its own body. Binder-first is the rule because the alternative
is worse across modules: with nominal-first, a module that adds a public class
`T` silently changes what every importer's `fn f<T>(T x)` means, rather than
saying anything. Shadowing is legal rather than rejected, because rejecting it
would make adding a public class a breaking change for importers.

The cost is a program that used to name the nominal and now names the binder;
it surfaces as a rejection at the first use of the shadowed type's structure,
never as a program that keeps compiling with a different meaning.
`corpus/verifies/type_param_shadows_nominal.sable` pins the rule and
`corpus/must-fail/type_param_shadows_record_field.sable` pins the failure
direction.

**Widening is one edit.** Admitting a shape in one more position is a change to
one row; adding a position is a row plus its gate name, noun phrase, and
rejection note; adding a shape is one arm of `TypeShape::after`, and every row
refuses it until it is listed. Each of those fails closed and is pinned by the
audits above.

**One fence covers two rules for two positions.** Because array elements and
option payloads share a gate name with their checker rules, an `expect-error`
fence alone cannot tell the halves apart, so the corpus could let a regression
in one hide behind the other. `admitted_shapes_match_their_lowering` pins the
parser's half shape by shape, and each half has corpus subjects of its own:
`array_element_class.sable` and `option_payload_option.sable` for the table,
`array_element_record.sable` and `option_payload_record.sable` for the checker.
