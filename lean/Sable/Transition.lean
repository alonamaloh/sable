/-
Copyright (c) 2026 Sable contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sable contributors
-/

import Sable.Seq

/-!
# Selected symbolic-transition certificates

These predicates are deliberately small.  Generated theorems use them to
check that a call-site unique-borrow havoc wrote its fresh state back to the
symbolic place the caller continues to name.  Arrays additionally certify the
length relation installed for the callee's post-state.  Owner-slot take and
put certificates check only the exact state observed after write-back against
the pre-state, index, and staged put term retained by the symbolic certificate.

This validates those emitted transition facts.  It does not validate mutation
discovery or the complete source-to-symbolic translation.  Owner-slot
allocation and cleanup remain outside this certificate slice.

The argument-schedule predicate at the end is a separate closed certificate.
It checks a bounded, ranked trace recorded after typechecking: an optional
receiver reservation, then each argument's completed nested writes/moves and
its direct callee effect.  Place overlap is structural (root plus field-path
prefix), not a comparison of rendered names.
-/

namespace Sable

/-- The symbolic state observed after call havoc is the fresh state chosen for
the unique-borrow argument. -/
structure CallHavocWriteback {α : Type} (fresh observed : α) : Prop where
  writeback : observed = fresh

/-- Array call havoc writes back the fresh sequence and preserves the length
of the actual pre-call sequence. -/
structure ArrayCallHavoc {α : Type}
    (before fresh observed : Seq α) : Prop where
  writeback : observed = fresh
  length : fresh.len = before.len

/-- The symbolic place observed after a successful owner-slot take is the
pre-state with that cell empty. The occupied-cell guard remains an ordinary
obligation; taken-payload provenance is a trusted generator-authored symbolic
fact in ordinary VC contexts outside this structural certificate. -/
structure SlotTakeWriteback {α : Type}
    (before observed : Seq (Option α)) (i : Int) : Prop where
  writeback : observed = before.set i none

/-- The symbolic place observed after a successful owner-slot put contains the
staged term. The empty-cell guard remains an ordinary obligation;
incoming-to-staged provenance is a trusted generator-authored symbolic fact in
ordinary VC contexts outside this structural certificate. -/
structure SlotPutWriteback {α : Type}
    (before observed : Seq (Option α)) (i : Int) (staged : α) : Prop where
  writeback : observed = before.set i (some staged)

namespace ArgumentSchedule

/-- A source storage identity.  Field paths are retained as components so
`x`, `x.left`, and `x.left.leaf` overlap by prefix while `x.left` and
`x.right` remain disjoint. -/
structure Place where
  root : String
  fields : List String
deriving DecidableEq, Repr

private def fieldsPrefix : List String → List String → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x == y && fieldsPrefix xs ys

def Place.valid (place : Place) : Bool :=
  !place.root.isEmpty && place.fields.all (fun field => !field.isEmpty)

def Place.overlaps (left right : Place) : Bool :=
  left.root == right.root &&
    (fieldsPrefix left.fields right.fields || fieldsPrefix right.fields left.fields)

/-- The effect retained at a callee boundary for one receiver or argument.
An inert value may have performed nested effects while being evaluated; those
live in the argument step rather than being smuggled into this direct effect. -/
inductive DirectEffect where
  | inert
  | loan (place : Place) (unique : Bool)
  | move (place : Place)
deriving DecidableEq, Repr

/-- A completed effect observed while evaluating an argument.  A nested
unique loan is a write once its callee returns; a nested shared read is
transient and therefore deliberately absent. -/
inductive NestedEffect where
  | write (place : Place)
  | move (place : Place)
deriving DecidableEq, Repr

/-- Argument ranks are one-based.  Rank zero is reserved structurally for the
receiver field of `Schedule`, so the order cannot be changed by list
rearrangement without invalidating this record. -/
structure Argument where
  rank : Nat
  nested : List NestedEffect
  direct : DirectEffect
deriving DecidableEq, Repr

structure Schedule where
  receiver : DirectEffect
  arguments : List Argument
deriving DecidableEq, Repr

def maxArguments : Nat := 64
def maxNestedEffects : Nat := 64

private def nestedCount : List Argument → Nat
  | [] => 0
  | argument :: rest => argument.nested.length + nestedCount rest

private def overlapsAny (place : Place) (places : List Place) : Bool :=
  places.any (fun other => place.overlaps other)

private def conflictsWithLoan
    (place : Place) (unique : Bool) (loans : List (Place × Bool)) : Bool :=
  loans.any (fun prior =>
    place.overlaps prior.1 && (unique || prior.2))

private def applyNested
    (pending : List (Place × Bool)) (moved : List Place) :
    List NestedEffect → Option (List Place)
  | [] => some moved
  | .write place :: rest =>
      if !place.valid || overlapsAny place moved ||
          pending.any (fun loan => place.overlaps loan.1) then
        none
      else
        applyNested pending moved rest
  | .move place :: rest =>
      if !place.valid || overlapsAny place moved ||
          pending.any (fun loan => place.overlaps loan.1) then
        none
      else
        applyNested pending (place :: moved) rest

private def applyDirect
    (pending : List (Place × Bool)) (moved : List Place) :
    DirectEffect → Option (List (Place × Bool) × List Place)
  | .inert => some (pending, moved)
  | .loan place unique =>
      if !place.valid || overlapsAny place moved ||
          conflictsWithLoan place unique pending then
        none
      else
        some ((place, unique) :: pending, moved)
  | .move place =>
      if !place.valid || overlapsAny place moved ||
          pending.any (fun loan => place.overlaps loan.1) then
        none
      else
        some (pending, place :: moved)

private def checkArguments
    (expectedRank : Nat) (pending : List (Place × Bool)) (moved : List Place) :
    List Argument → Bool
  | [] => true
  | argument :: rest =>
      if argument.rank != expectedRank then
        false
      else
        match applyNested pending moved argument.nested with
        | none => false
        | some moved' =>
            match applyDirect pending moved' argument.direct with
            | none => false
            | some (pending', moved'') =>
                checkArguments (expectedRank + 1) pending' moved'' rest

/-- The bounded argument-schedule rule.

The receiver is processed first.  A pending loan rejects every later
overlapping write or move.  A completed move rejects a later loan.  Direct
moves and callee loans therefore cannot overlap in either order, and a unique
loan cannot overlap any other callee loan.  A completed earlier write is not
retained, so mutation-before-loan remains legal. -/
def safe (schedule : Schedule) : Bool :=
  decide (schedule.arguments.length ≤ maxArguments) &&
    decide (nestedCount schedule.arguments ≤ maxNestedEffects) &&
    match schedule.receiver with
    | .move _ => false
    | receiver =>
        match applyDirect [] [] receiver with
        | none => false
        | some (pending, moved) => checkArguments 1 pending moved schedule.arguments

/-! The closed truth table below pins the temporal asymmetry and the moved
state independently of Rust extraction. These examples are deliberately
small enough to reduce with the kernel evaluator. -/

private def truthPlace : Place := ⟨"item", []⟩
private def truthField : Place := ⟨"item", ["field"]⟩
private def otherPlace : Place := ⟨"other", []⟩

private def truthSchedule
    (receiver : DirectEffect) (arguments : List Argument) : Schedule :=
  ⟨receiver, arguments⟩

example : safe (truthSchedule .inert [
    ⟨1, [.write truthPlace], .inert⟩,
    ⟨2, [], .loan truthPlace false⟩]) = true := by decide

example : safe (truthSchedule .inert [
    ⟨2, [], .inert⟩]) = false := by decide

example : safe (truthSchedule .inert [
    ⟨1, [], .loan truthPlace false⟩,
    ⟨2, [.write truthField], .inert⟩]) = false := by decide

example : safe (truthSchedule .inert [
    ⟨1, [], .loan truthPlace false⟩,
    ⟨2, [.move truthField], .inert⟩]) = false := by decide

/-- Rust extraction maps a named owner consumed by `some(owner)` to this
`OptionPayload` nested move.  It cannot follow an earlier callee loan. -/
example : safe (truthSchedule .inert [
    ⟨1, [], .loan truthPlace false⟩,
    ⟨2, [.move truthField], .inert⟩]) = false := by decide

/-- The same `OptionPayload` move remains moved state for a later loan. -/
example : safe (truthSchedule .inert [
    ⟨1, [.move truthField], .inert⟩,
    ⟨2, [], .loan truthPlace false⟩]) = false := by decide

example : safe (truthSchedule .inert [
    ⟨1, [], .move truthPlace⟩,
    ⟨2, [], .move truthField⟩]) = false := by decide

example : safe (truthSchedule .inert [
    ⟨1, [.move truthPlace], .move truthField⟩]) = false := by decide

example : safe (truthSchedule .inert [
    ⟨1, [.move truthPlace], .loan truthField false⟩]) = false := by decide

example : safe (truthSchedule .inert [
    ⟨1, [], .move truthPlace⟩,
    ⟨2, [.write truthField], .inert⟩]) = false := by decide

example : safe (truthSchedule .inert [
    ⟨1, [], .move truthPlace⟩,
    ⟨2, [.move truthField], .inert⟩]) = false := by decide

example : safe (truthSchedule (.loan truthPlace true) [
    ⟨1, [], .loan truthField false⟩]) = false := by decide

example : safe (truthSchedule (.loan truthPlace false) [
    ⟨1, [], .loan truthField false⟩,
    ⟨2, [.write otherPlace], .inert⟩]) = true := by decide

end ArgumentSchedule

end Sable
