/-
U9a probe — a reusable aggregate resource and the intrusive-list proof shape.

Run from `lean/`:

  lake env lean ../docs/notes/resource-map-probe.lean

The surface goal is `ResourceMap<K, R>`: one affine token whose duplicable
view is a partial map from keys to `View<R>`.  This file tests the hidden
interpretation rather than adding a user-visible separation logic.  It proves
generic take/put, derives an in-place entry update from those rules, then uses
`ResourceMap<Int, PointsToView IntrusiveNode>` to state a doubly linked list
only as runtime links plus an abstract sequence.
-/

import Sable
open Sable

set_option linter.unusedVariables false

namespace ResourceMapProbe

universe uK uV uC uW

/-! ## Pure map view -/

structure ResourceMapView (K : Type uK) (V : Type uV) where
  entries : K → Option V

namespace ResourceMapView

variable {K : Type uK} {V : Type uV} [DecidableEq K]

def empty : ResourceMapView K V :=
  ⟨fun _ => none⟩

def erase (m : ResourceMapView K V) (key : K) : ResourceMapView K V :=
  ⟨fun k => if k = key then none else m.entries k⟩

def insert (m : ResourceMapView K V) (key : K) (value : V) :
    ResourceMapView K V :=
  ⟨fun k => if k = key then some value else m.entries k⟩

omit [DecidableEq K] in
@[simp] theorem empty_entries (key : K) :
    (empty : ResourceMapView K V).entries key = none := rfl

@[simp] theorem erase_eq (m : ResourceMapView K V) (key : K) :
    (m.erase key).entries key = none := by
  simp [erase]

@[simp] theorem erase_ne (m : ResourceMapView K V) {key other : K}
    (hne : other ≠ key) :
    (m.erase key).entries other = m.entries other := by
  simp [erase, hne]

@[simp] theorem insert_eq (m : ResourceMapView K V) (key : K) (value : V) :
    (m.insert key value).entries key = some value := by
  simp [insert]

@[simp] theorem insert_ne (m : ResourceMapView K V) {key other : K}
    (value : V) (hne : other ≠ key) :
    (m.insert key value).entries other = m.entries other := by
  simp [insert, hne]

/-- Exact view restoration, not merely extensional membership equivalence. -/
theorem erase_insert_roundTrip
    {m : ResourceMapView K V} {key : K} {value : V}
    (hentry : m.entries key = some value) :
    (m.erase key).insert key value = m := by
  cases m with
  | mk entries =>
      simp only [erase, insert]
      congr 1
      funext other
      by_cases h : other = key
      · subst other
        simpa using hentry.symm
      · simp [h]

theorem insert_erase_roundTrip
    {m : ResourceMapView K V} {key : K} {value : V}
    (hempty : m.entries key = none) :
    (m.insert key value).erase key = m := by
  cases m with
  | mk entries =>
      simp only [erase, insert]
      congr 1
      funext other
      by_cases h : other = key
      · subst other
        simpa using hempty.symm
      · simp [h]

end ResourceMapView

/-! ## Hidden valid-composition interpretation

`ownsValue` and `agreesValue` stand for the resource-specific part of the
eventual resource-soundness metatheorem.  Users see neither them nor the
context predicates below.  The important question is whether one generic map
rule preserves them for every resource kind. -/

def ValueDisjoint
    {V : Type uV} {Cap : Type uC}
    (ownsValue : V → Cap → Prop) (left right : V) : Prop :=
  ∀ cap, ¬ (ownsValue left cap ∧ ownsValue right cap)

def ResourceMapView.Valid
    {K : Type uK} {V : Type uV} {Cap : Type uC} {World : Type uW}
    (agreesValue : World → V → Prop) (ownsValue : V → Cap → Prop)
    (world : World) (m : ResourceMapView K V) : Prop :=
  (∀ key value, m.entries key = some value → agreesValue world value) ∧
  ∀ leftKey rightKey left right,
    m.entries leftKey = some left →
    m.entries rightKey = some right →
    leftKey ≠ rightKey →
    ValueDisjoint ownsValue left right

inductive Bundle (K : Type uK) (V : Type uV) where
  | one : V → Bundle K V
  | many : ResourceMapView K V → Bundle K V

def Bundle.owns
    {K : Type uK} {V : Type uV} {Cap : Type uC}
    (ownsValue : V → Cap → Prop) : Bundle K V → Cap → Prop
  | .one value => ownsValue value
  | .many m => fun cap =>
      ∃ key value, m.entries key = some value ∧ ownsValue value cap

def Bundle.agrees
    {K : Type uK} {V : Type uV} {Cap : Type uC} {World : Type uW}
    (agreesValue : World → V → Prop) (ownsValue : V → Cap → Prop)
    (world : World) : Bundle K V → Prop
  | .one value => agreesValue world value
  | .many m => m.Valid agreesValue ownsValue world

def Bundle.Disjoint
    {K : Type uK} {V : Type uV} {Cap : Type uC}
    (ownsValue : V → Cap → Prop) (left right : Bundle K V) : Prop :=
  ∀ cap, ¬ (left.owns ownsValue cap ∧ right.owns ownsValue cap)

def PairwiseDisjoint
    {K : Type uK} {V : Type uV} {Cap : Type uC}
    (ownsValue : V → Cap → Prop) : List (Bundle K V) → Prop
  | [] => True
  | resource :: rest =>
      (∀ other ∈ rest, resource.Disjoint ownsValue other) ∧
      PairwiseDisjoint ownsValue rest

def ContextValid
    {K : Type uK} {V : Type uV} {Cap : Type uC} {World : Type uW}
    (agreesValue : World → V → Prop) (ownsValue : V → Cap → Prop)
    (world : World) (resources : List (Bundle K V)) : Prop :=
  (∀ resource ∈ resources, resource.agrees agreesValue ownsValue world) ∧
  PairwiseDisjoint ownsValue resources

theorem Bundle.Disjoint.mono_left
    {K : Type uK} {V : Type uV} {Cap : Type uC}
    {ownsValue : V → Cap → Prop} {before after other : Bundle K V}
    (subset : ∀ cap, after.owns ownsValue cap → before.owns ownsValue cap)
    (hdisjoint : before.Disjoint ownsValue other) :
    after.Disjoint ownsValue other := by
  intro cap overlap
  exact hdisjoint cap ⟨subset cap overlap.1, overlap.2⟩

theorem Bundle.Disjoint.symm
    {K : Type uK} {V : Type uV} {Cap : Type uC}
    {ownsValue : V → Cap → Prop} {left right : Bundle K V}
    (h : left.Disjoint ownsValue right) :
    right.Disjoint ownsValue left := by
  intro cap overlap
  exact h cap ⟨overlap.2, overlap.1⟩

theorem one_owns_sub_many
    {K : Type uK} {V : Type uV} {Cap : Type uC}
    {ownsValue : V → Cap → Prop} {m : ResourceMapView K V}
    {key : K} {value : V} (hentry : m.entries key = some value) :
    ∀ cap,
      (Bundle.one value : Bundle K V).owns ownsValue cap →
      (Bundle.many m).owns ownsValue cap := by
  intro cap howns
  exact ⟨key, value, hentry, howns⟩

theorem erase_owns_sub_many
    {K : Type uK} {V : Type uV} {Cap : Type uC} [DecidableEq K]
    {ownsValue : V → Cap → Prop} {m : ResourceMapView K V} {key : K} :
    ∀ cap,
      (Bundle.many (m.erase key)).owns ownsValue cap →
      (Bundle.many m).owns ownsValue cap := by
  rintro cap ⟨other, value, hentry, howns⟩
  have hne : other ≠ key := by
    intro heq
    subst other
    simp at hentry
  exact ⟨other, value, by simpa [ResourceMapView.erase, hne] using hentry, howns⟩

theorem ResourceMapView.valid_erase
    {K : Type uK} {V : Type uV} {Cap : Type uC} {World : Type uW}
    [DecidableEq K]
    {agreesValue : World → V → Prop} {ownsValue : V → Cap → Prop}
    {world : World} {m : ResourceMapView K V} {key : K}
    (hvalid : m.Valid agreesValue ownsValue world) :
    (m.erase key).Valid agreesValue ownsValue world := by
  constructor
  · intro other value hentry
    have hne : other ≠ key := by
      intro heq
      subst other
      simp at hentry
    exact hvalid.1 other value (by
      simpa [ResourceMapView.erase, hne] using hentry)
  · intro leftKey rightKey left right hleft hright hne
    have hlk : leftKey ≠ key := by
      intro heq
      subst leftKey
      simp at hleft
    have hrk : rightKey ≠ key := by
      intro heq
      subst rightKey
      simp at hright
    apply hvalid.2 leftKey rightKey left right
    · simpa [ResourceMapView.erase, hlk] using hleft
    · simpa [ResourceMapView.erase, hrk] using hright
    · exact hne

/-- The generic sealed `take`: one entry becomes one affine resource and the
residual aggregate, while every unrelated resource in the context is framed. -/
theorem context_take
    {K : Type uK} {V : Type uV} {Cap : Type uC} {World : Type uW}
    [DecidableEq K]
    {agreesValue : World → V → Prop} {ownsValue : V → Cap → Prop}
    {world : World} {rest : List (Bundle K V)}
    {m : ResourceMapView K V} {key : K} {value : V}
    (hentry : m.entries key = some value)
    (hcontext : ContextValid agreesValue ownsValue world (.many m :: rest)) :
    ContextValid agreesValue ownsValue world
      (.one value :: .many (m.erase key) :: rest) := by
  obtain ⟨hagrees, hmapRest, hrest⟩ := hcontext
  have hvalid : m.Valid agreesValue ownsValue world :=
    hagrees (.many m) (by simp)
  refine ⟨?_, ?_, ?_, hrest⟩
  · intro resource hresource
    simp only [List.mem_cons] at hresource
    rcases hresource with rfl | rfl | hresource
    · exact hvalid.1 key value hentry
    · exact ResourceMapView.valid_erase hvalid
    · exact hagrees resource (by simp [hresource])
  · intro resource hresource
    simp only [List.mem_cons] at hresource
    rcases hresource with rfl | hresource
    · intro cap overlap
      obtain ⟨other, otherValue, hother, hotherOwns⟩ := overlap.2
      have hne : other ≠ key := by
        intro heq
        subst other
        simp at hother
      have horiginal : m.entries other = some otherValue := by
        simpa [ResourceMapView.erase, hne] using hother
      exact hvalid.2 key other value otherValue hentry horiginal
        (Ne.symm hne) cap ⟨overlap.1, hotherOwns⟩
    · apply Bundle.Disjoint.mono_left
        (one_owns_sub_many hentry)
        (hmapRest resource (by simp [hresource]))
  · intro resource hresource
    apply Bundle.Disjoint.mono_left erase_owns_sub_many
    exact hmapRest resource hresource

/-- Replacing the head resource by another view of the same footprint is the
hidden meaning of a tracked mutable entry borrow. -/
theorem context_replace_head
    {K : Type uK} {V : Type uV} {Cap : Type uC} {World : Type uW}
    {agreesValue : World → V → Prop} {ownsValue : V → Cap → Prop}
    {world : World} {rest : List (Bundle K V)} {before after : V}
    (hagreesAfter : agreesValue world after)
    (sameFootprint : ∀ cap, ownsValue after cap ↔ ownsValue before cap)
    (hcontext : ContextValid agreesValue ownsValue world (.one before :: rest)) :
    ContextValid agreesValue ownsValue world (.one after :: rest) := by
  obtain ⟨hagrees, hheadRest, hrest⟩ := hcontext
  refine ⟨?_, ?_, hrest⟩
  · intro resource hresource
    simp only [List.mem_cons] at hresource
    rcases hresource with rfl | hresource
    · exact hagreesAfter
    · exact hagrees resource (by simp [hresource])
  · intro resource hresource
    apply Bundle.Disjoint.mono_left (before := .one before)
    · intro cap howns
      exact (sameFootprint cap).mp howns
    · exact hheadRest resource hresource

theorem ResourceMapView.valid_insert
    {K : Type uK} {V : Type uV} {Cap : Type uC} {World : Type uW}
    [DecidableEq K]
    {agreesValue : World → V → Prop} {ownsValue : V → Cap → Prop}
    {world : World} {m : ResourceMapView K V} {key : K} {value : V}
    (hempty : m.entries key = none)
    (hvalid : m.Valid agreesValue ownsValue world)
    (hagrees : agreesValue world value)
    (hseparate : (Bundle.one value : Bundle K V).Disjoint ownsValue (.many m)) :
    (m.insert key value).Valid agreesValue ownsValue world := by
  constructor
  · intro other otherValue hentry
    by_cases heq : other = key
    · subst other
      simp only [ResourceMapView.insert_eq] at hentry
      cases hentry
      exact hagrees
    · apply hvalid.1 other otherValue
      simpa [ResourceMapView.insert, heq] using hentry
  · intro leftKey rightKey left right hleft hright hne
    by_cases hleftKey : leftKey = key
    · subst leftKey
      simp only [ResourceMapView.insert_eq] at hleft
      cases hleft
      have hrightKey : rightKey ≠ key := Ne.symm hne
      have hrightOriginal : m.entries rightKey = some right := by
        simpa [ResourceMapView.insert, hrightKey] using hright
      intro cap overlap
      exact hseparate cap
        ⟨overlap.1, ⟨rightKey, right, hrightOriginal, overlap.2⟩⟩
    · have hleftOriginal : m.entries leftKey = some left := by
        simpa [ResourceMapView.insert, hleftKey] using hleft
      by_cases hrightKey : rightKey = key
      · subst rightKey
        simp only [ResourceMapView.insert_eq] at hright
        cases hright
        intro cap overlap
        exact hseparate cap
          ⟨overlap.2, ⟨leftKey, left, hleftOriginal, overlap.1⟩⟩
      · have hrightOriginal : m.entries rightKey = some right := by
          simpa [ResourceMapView.insert, hrightKey] using hright
        exact hvalid.2 leftKey rightKey left right
          hleftOriginal hrightOriginal hne

/-- The generic sealed `put`: an absent key plus context separation is enough;
the caller never proves a global nonoverlap formula. -/
theorem context_put
    {K : Type uK} {V : Type uV} {Cap : Type uC} {World : Type uW}
    [DecidableEq K]
    {agreesValue : World → V → Prop} {ownsValue : V → Cap → Prop}
    {world : World} {rest : List (Bundle K V)}
    {m : ResourceMapView K V} {key : K} {value : V}
    (hempty : m.entries key = none)
    (hcontext : ContextValid agreesValue ownsValue world
      (.one value :: .many m :: rest)) :
    ContextValid agreesValue ownsValue world (.many (m.insert key value) :: rest) := by
  obtain ⟨hagrees, hvalueTail, hmapRest, hrest⟩ := hcontext
  have hagreesValue : agreesValue world value :=
    hagrees (.one value) (by simp)
  have hvalid : m.Valid agreesValue ownsValue world :=
    hagrees (.many m) (by simp)
  have hvalueMap : (Bundle.one value : Bundle K V).Disjoint ownsValue (.many m) :=
    hvalueTail (.many m) (by simp)
  refine ⟨?_, ?_, hrest⟩
  · intro resource hresource
    simp only [List.mem_cons] at hresource
    rcases hresource with rfl | hresource
    · exact ResourceMapView.valid_insert hempty hvalid hagreesValue hvalueMap
    · exact hagrees resource (by simp [hresource])
  · intro resource hresource cap overlap
    obtain ⟨entryKey, entryValue, hentry, hentryOwns⟩ := overlap.1
    by_cases heq : entryKey = key
    · subst entryKey
      simp only [ResourceMapView.insert_eq] at hentry
      cases hentry
      exact hvalueTail resource (by simp [hresource]) cap
        ⟨hentryOwns, overlap.2⟩
    · have horiginal : m.entries entryKey = some entryValue := by
        simpa [ResourceMapView.insert, heq] using hentry
      exact hmapRest resource hresource cap
        ⟨⟨entryKey, entryValue, horiginal, hentryOwns⟩, overlap.2⟩

/-- A mutable entry update is derivable from take → footprint-preserving
resource mutation → put.  A future concise borrow surface need not add a new
authority axiom. -/
theorem context_update_entry
    {K : Type uK} {V : Type uV} {Cap : Type uC} {World : Type uW}
    [DecidableEq K]
    {agreesValue : World → V → Prop} {ownsValue : V → Cap → Prop}
    {world : World} {rest : List (Bundle K V)}
    {m : ResourceMapView K V} {key : K} {before after : V}
    (hentry : m.entries key = some before)
    (hagreesAfter : agreesValue world after)
    (sameFootprint : ∀ cap, ownsValue after cap ↔ ownsValue before cap)
    (hcontext : ContextValid agreesValue ownsValue world (.many m :: rest)) :
    ContextValid agreesValue ownsValue world
      (.many ((m.erase key).insert key after) :: rest) := by
  apply context_put (by simp)
  apply context_replace_head hagreesAfter sameFootprint
  exact context_take hentry hcontext

/-! ## Intrusive-list instance

The node permission is a typed extent. Runtime links are raw pointers, while
the aggregate key is the node's arena-relative offset. All nodes are from one
arena in v1, so pointer comparison never needs a cross-allocation rule. -/

structure IntrusiveNode where
  previous : Option RawPtr
  next : Option RawPtr
  payload : Int

def nodePointer (arena key : Int) : RawPtr :=
  ⟨arena, key⟩

def nodeCellOwns (cell : PointsToView IntrusiveNode) : (Int × Int) → Prop
  | (alloc, byte) =>
      alloc = cell.alloc ∧ cell.off ≤ byte ∧
      byte < cell.off + cell.layout.size

def nodeCellAgrees (_world : Unit) (cell : PointsToView IntrusiveNode) : Prop :=
  0 < cell.layout.size ∧ 0 ≤ cell.off

theorem node_put_sameFootprint (cell : PointsToView IntrusiveNode)
    (node : IntrusiveNode) (cap : Int × Int) :
    nodeCellOwns (cell.put node) cap ↔ nodeCellOwns cell cap := by
  cases cap
  rfl

inductive Linked
    (nodes : ResourceMapView Int (PointsToView IntrusiveNode))
    (arena : Int) : Option RawPtr → List Int → Prop where
  | nil (previous : Option RawPtr) : Linked nodes arena previous []
  | cons (previous : Option RawPtr) (key : Int) (rest : List Int)
      (node : IntrusiveNode) (cell : PointsToView IntrusiveNode)
      (stored : nodes.entries key = some cell)
      (initialized : cell.state = .init node)
      (located : cell.alloc = arena ∧ cell.off = key)
      (backward : node.previous = previous)
      (forward : node.next = rest.head?.map (nodePointer arena))
      (tail : Linked nodes arena (some (nodePointer arena key)) rest) :
      Linked nodes arena previous (key :: rest)

def IntrusiveList
    (nodes : ResourceMapView Int (PointsToView IntrusiveNode))
    (arena : Int) (head tail : Option RawPtr) (sequence : List Int) : Prop :=
  head = sequence.head?.map (nodePointer arena) ∧
  tail = sequence.getLast?.map (nodePointer arena) ∧
  sequence.Nodup ∧
  Linked nodes arena none sequence

theorem nodePointer_eq_iff {arena left right : Int} :
    nodePointer arena left = nodePointer arena right ↔ left = right := by
  constructor
  · intro h
    exact congrArg RawPtr.off h
  · intro h
    simp [h]

theorem nodePointer_order_iff {arena left right : Int} :
    (nodePointer arena left).off < (nodePointer arena right).off ↔ left < right :=
  Iff.rfl

/-- The visible list predicate talks only about the abstract sequence, map
entries, and runtime links. It contains no heap, capability, or separating
conjunction. -/
theorem two_node_list
    {arena firstKey secondKey : Int} (hne : firstKey ≠ secondKey)
    {layout : Layout} (hlayout : 0 < layout.size) :
    let firstNode : IntrusiveNode :=
      ⟨none, some (nodePointer arena secondKey), 10⟩
    let secondNode : IntrusiveNode :=
      ⟨some (nodePointer arena firstKey), none, 20⟩
    let firstCell : PointsToView IntrusiveNode :=
      ⟨arena, firstKey, layout, .init firstNode⟩
    let secondCell : PointsToView IntrusiveNode :=
      ⟨arena, secondKey, layout, .init secondNode⟩
    let nodes :=
      ((ResourceMapView.empty : ResourceMapView Int (PointsToView IntrusiveNode)).insert
        firstKey firstCell).insert secondKey secondCell
    IntrusiveList nodes arena
      (some (nodePointer arena firstKey))
      (some (nodePointer arena secondKey))
      [firstKey, secondKey] := by
  dsimp
  refine ⟨by simp [nodePointer], by simp [nodePointer], by simp [hne], ?_⟩
  apply Linked.cons none firstKey [secondKey]
      { previous := none, next := some (nodePointer arena secondKey), payload := 10 }
      { alloc := arena, off := firstKey, layout := layout,
        state := .init
          { previous := none, next := some (nodePointer arena secondKey), payload := 10 } }
  · simp [ResourceMapView.insert, ResourceMapView.empty, hne]
  · rfl
  · exact ⟨rfl, rfl⟩
  · rfl
  · rfl
  · apply Linked.cons (some (nodePointer arena firstKey)) secondKey []
        { previous := some (nodePointer arena firstKey), next := none, payload := 20 }
        { alloc := arena, off := secondKey, layout := layout,
          state := .init
            { previous := some (nodePointer arena firstKey), next := none, payload := 20 } }
    · simp [ResourceMapView.insert, ResourceMapView.empty]
    · rfl
    · exact ⟨rfl, rfl⟩
    · rfl
    · rfl
    · exact Linked.nil _

#check ResourceMapView.erase_insert_roundTrip
#check ResourceMapView.insert_erase_roundTrip
#check context_take
#check context_put
#check context_update_entry
#check node_put_sameFootprint
#check nodePointer_eq_iff
#check two_node_list

#print axioms ResourceMapView.erase_insert_roundTrip
#print axioms context_take
#print axioms context_put
#print axioms context_update_entry
#print axioms two_node_list

end ResourceMapProbe
