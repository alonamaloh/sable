/-
U1 — the concrete Lean resource probe for unsafe Sable.

Not a separation-logic library: one concrete byte-level model, one
interpretation of the affine context over it, and preservation theorems
for the primitive transformations. See `docs/notes/unsafe-plan.md` (U1)
for what this is meant to answer and `docs/notes/unsafe-sketch.md` for
why the architecture is shaped this way.

Read from `lean/`:  lean docs/notes/unsafe-probe.lean

The one design choice that makes the whole thing tractable: **backing is
per byte**. A span's view claims, for each index it covers, that the
heap has that byte. Empty spans are then vacuously backed (so they carry
no authority and constrain nothing), split and join become index
arithmetic, and the frame argument is pointwise — which is why omega
closes most of it.
-/

import Sable
open Sable

set_option linter.unusedVariables false

/-! ## The raw heap -/

/-- Raw storage is not `seq u8`: uninitialized is a distinct state, and
`init` must stay distinguishable from any inhabitant of a value type. -/
inductive ByteState where
  | uninit : ByteState
  | init   : Int → ByteState
  deriving DecidableEq

/-- Provenance plus offset, never an address: two live pointers may share
a machine address only if they share an allocation. -/
structure RawPtr where
  alloc : Int
  off   : Int

structure Allocation where
  size  : Int
  live  : Bool
  bytes : Seq ByteState

structure RawHeap where
  /-- Fresh-provenance counter; ids at or above it are unallocated. -/
  next   : Int
  allocs : Int → Option Allocation

/-- The only well-formedness the heap itself needs: the counter really is
fresh. This is what makes a new allocation disjoint from every live
resource without inspecting the context. -/
def RawHeap.wf (h : RawHeap) : Prop :=
  ∀ a, h.next ≤ a → h.allocs a = none

def RawHeap.store (h : RawHeap) (a k : Int) (b : ByteState) : RawHeap :=
  { h with allocs := fun i =>
      if i = a then (h.allocs i).map (fun al => { al with bytes := al.bytes.set k b })
      else h.allocs i }

def RawHeap.release (h : RawHeap) (a : Int) : RawHeap :=
  { h with allocs := fun i =>
      if i = a then (h.allocs i).map (fun al => { al with live := false })
      else h.allocs i }

def RawHeap.fresh (h : RawHeap) (size : Int) : RawHeap :=
  { next := h.next + 1,
    allocs := fun i =>
      if i = h.next then some ⟨size, true, ⟨size, fun _ => .uninit⟩⟩ else h.allocs i }

/-! ## Views — what Lean is allowed to see

A view is an ordinary value. Facts about it are knowledge and may be
copied freely; the authority it describes is what the checker keeps
affine, and never appears here. -/

structure SpanView where
  alloc : Int
  off   : Int
  len   : Int
  bytes : Seq ByteState

structure DeallocView where
  alloc : Int
  size  : Int

/-- A dynamic collection of permissions: one affine token, one pure map
view. `keys` is the domain; `view k` is meaningful only on it. -/
structure MapView where
  keys : Int → Prop
  view : Int → SpanView

/-! ## The affine context and its interpretation -/

/-- The unit of authority. Byte capabilities and the authority to release
an allocation are different things: carving a span must never mint the
right to free what it was carved from. -/
inductive Cap where
  | byte : Int → Int → Cap
  | free : Int → Cap

inductive Res where
  | span    : SpanView → Res
  | dealloc : DeallocView → Res
  | agg     : MapView → Res

def SpanView.ownsCap (v : SpanView) : Cap → Prop
  | .byte a k => a = v.alloc ∧ v.off ≤ k ∧ k < v.off + v.len
  | .free _   => False

def Res.owns : Res → Cap → Prop
  | .span v    => v.ownsCap
  | .dealloc d => fun c => match c with
      | .byte _ _ => False
      | .free a   => a = d.alloc
  | .agg m     => fun c => ∃ k, m.keys k ∧ (m.view k).ownsCap c

/-- Backing, stated per byte. `0 ≤ k < len` is the guard every generated
clause carries anyway. -/
def SpanView.backed (h : RawHeap) (v : SpanView) : Prop :=
  ∀ k, 0 ≤ k → k < v.len →
    ∃ al, h.allocs v.alloc = some al ∧ al.live = true ∧
      0 ≤ v.off + k ∧ v.off + k < al.size ∧
      al.bytes.get (v.off + k) = v.bytes.get k

def SpanView.wf (v : SpanView) : Prop :=
  v.bytes.len = v.len ∧ 0 ≤ v.off ∧ 0 ≤ v.len

def SpanView.agrees (h : RawHeap) (v : SpanView) : Prop :=
  v.wf ∧ v.backed h

def Res.agrees (h : RawHeap) : Res → Prop
  | .span v    => v.agrees h
  | .dealloc d => ∃ al, h.allocs d.alloc = some al ∧ al.live = true ∧ al.size = d.size
  | .agg m     => (∀ k, m.keys k → (m.view k).agrees h) ∧
                  (∀ j k, m.keys j → m.keys k → j ≠ k →
                    ∀ c, ¬((m.view j).ownsCap c ∧ (m.view k).ownsCap c))

def Disjoint (r s : Res) : Prop := ∀ c, ¬(r.owns c ∧ s.owns c)

def PairwiseDisjoint : List Res → Prop
  | []      => True
  | r :: rs => (∀ s ∈ rs, Disjoint r s) ∧ PairwiseDisjoint rs

/-- `Own h Δ` — the interpretation of the whole affine context over the
raw heap. This is the metatheory's object; no user clause mentions it,
and no generated VC receives it as a hypothesis. -/
def Own (h : RawHeap) (Δ : List Res) : Prop :=
  (∀ r ∈ Δ, r.agrees h) ∧ PairwiseDisjoint Δ

/-! ## Structural lemmas

Two lemmas carry almost every preservation proof: a resource whose
footprint shrinks stays disjoint from whatever the old one was disjoint
from, and a heap edit inside one resource's footprint is invisible to
every resource disjoint from it. -/

theorem Disjoint.mono_left {r r' s : Res} (hsub : ∀ c, r'.owns c → r.owns c)
    (h : Disjoint r s) : Disjoint r' s :=
  fun c ⟨h1, h2⟩ => h c ⟨hsub c h1, h2⟩

theorem Disjoint.symm {r s : Res} (h : Disjoint r s) : Disjoint s r :=
  fun c ⟨h1, h2⟩ => h c ⟨h2, h1⟩

theorem Disjoint.mono_right {r s s' : Res} (hsub : ∀ c, s'.owns c → s.owns c)
    (h : Disjoint r s) : Disjoint r s' :=
  (Disjoint.mono_left hsub h.symm).symm

/-! ### The frame lemma

A byte write is invisible to every resource that does not own that byte.
This is where framing comes from: not a frame rule in the logic, but
disjointness in the checker's context. -/

theorem SpanView.agrees_store {h : RawHeap} {v : SpanView} {a k : Int} {b : ByteState}
    (hv : v.agrees h) (hno : ¬ v.ownsCap (.byte a k)) :
    v.agrees (h.store a k b) := by
  obtain ⟨hwf, hb⟩ := hv
  refine ⟨hwf, ?_⟩
  intro j hj0 hjl
  obtain ⟨al, hal, hlive, hlo, hhi, hget⟩ := hb j hj0 hjl
  by_cases ha : v.alloc = a
  · subst ha
    refine ⟨{ al with bytes := al.bytes.set k b }, ?_, hlive, hlo, hhi, ?_⟩
    · simp [RawHeap.store, hal]
    · have hne : v.off + j ≠ k := by
        intro he
        exact hno ⟨rfl, by omega, by omega⟩
      simpa [Seq.get_set, hne] using hget
  · refine ⟨al, ?_, hlive, hlo, hhi, hget⟩
    simp [RawHeap.store, ha, hal]

theorem Res.agrees_store {h : RawHeap} {r : Res} {a k : Int} {b : ByteState}
    (hr : r.agrees h) (hno : ¬ r.owns (.byte a k)) :
    r.agrees (h.store a k b) := by
  cases r with
  | span v => exact SpanView.agrees_store hr hno
  | dealloc d =>
      obtain ⟨al, hal, hlive, hsize⟩ := hr
      by_cases ha : d.alloc = a
      · subst ha
        exact ⟨{ al with bytes := al.bytes.set k b }, by simp [RawHeap.store, hal], hlive, hsize⟩
      · exact ⟨al, by simp [RawHeap.store, ha, hal], hlive, hsize⟩
  | agg m =>
      obtain ⟨hall, hdis⟩ := hr
      refine ⟨fun j hj => SpanView.agrees_store (hall j hj) ?_, hdis⟩
      intro hown
      exact hno ⟨j, hj, hown⟩

/-! ## `split_off` and `join`

`split_off` keeps the prefix in the original token and returns the
suffix, so no product type is needed in the surface language. Both
directions are index arithmetic on the views; the authority side is the
two containment lemmas below. -/

def SpanView.take (v : SpanView) (n : Int) : SpanView :=
  { v with len := n, bytes := ⟨n, v.bytes.get⟩ }

def SpanView.drop (v : SpanView) (n : Int) : SpanView :=
  { alloc := v.alloc, off := v.off + n, len := v.len - n,
    bytes := ⟨v.len - n, fun k => v.bytes.get (n + k)⟩ }

def SpanView.cat (v1 v2 : SpanView) : SpanView :=
  { alloc := v1.alloc, off := v1.off, len := v1.len + v2.len,
    bytes := ⟨v1.len + v2.len,
              fun k => if k < v1.len then v1.bytes.get k else v2.bytes.get (k - v1.len)⟩ }

theorem take_owns_sub {v : SpanView} {n : Int} (hn0 : 0 ≤ n) (hnl : n ≤ v.len) :
    ∀ c, (Res.span (v.take n)).owns c → (Res.span v).owns c := by
  intro c hc
  cases c with
  | byte a k =>
      obtain ⟨h1, h2, h3⟩ := hc
      simp only [SpanView.take] at h1 h2 h3
      exact ⟨h1, h2, by omega⟩
  | free a => exact hc.elim

theorem drop_owns_sub {v : SpanView} {n : Int} (hn0 : 0 ≤ n) (hnl : n ≤ v.len) :
    ∀ c, (Res.span (v.drop n)).owns c → (Res.span v).owns c := by
  intro c hc
  cases c with
  | byte a k =>
      obtain ⟨h1, h2, h3⟩ := hc
      simp only [SpanView.drop] at h1 h2 h3
      exact ⟨h1, by omega, by omega⟩
  | free a => exact hc.elim

theorem cat_owns_sub {v1 v2 : SpanView} (halloc : v1.alloc = v2.alloc)
    (hadj : v1.off + v1.len = v2.off) (h1w : 0 ≤ v1.len) (h2w : 0 ≤ v2.len) :
    ∀ c, (Res.span (v1.cat v2)).owns c →
         (Res.span v1).owns c ∨ (Res.span v2).owns c := by
  intro c hc
  cases c with
  | byte a k =>
      obtain ⟨e1, e2, e3⟩ := hc
      simp only [SpanView.cat] at e1 e2 e3
      by_cases hk : k < v1.off + v1.len
      · exact Or.inl ⟨e1, e2, hk⟩
      · exact Or.inr ⟨by omega, by omega, by omega⟩
  | free a => exact hc.elim

theorem take_drop_disjoint {v : SpanView} :
    Disjoint (.span (v.take n)) (.span (v.drop n)) := by
  intro c ⟨hl, hr⟩
  cases c with
  | byte a k =>
      obtain ⟨_, h2, h3⟩ := hl
      obtain ⟨_, h5, _⟩ := hr
      simp only [SpanView.take] at h2 h3
      simp only [SpanView.drop] at h5
      omega
  | free a => exact hl.elim

theorem SpanView.agrees_take {h : RawHeap} {v : SpanView} {n : Int}
    (hn0 : 0 ≤ n) (hnl : n ≤ v.len) (hv : v.agrees h) : (v.take n).agrees h := by
  obtain ⟨⟨hlen, hoff, hvlen⟩, hb⟩ := hv
  refine ⟨⟨rfl, hoff, hn0⟩, ?_⟩
  intro j hj0 hjl
  simp only [SpanView.take] at hjl ⊢
  exact hb j hj0 (by omega)

theorem SpanView.agrees_drop {h : RawHeap} {v : SpanView} {n : Int}
    (hn0 : 0 ≤ n) (hnl : n ≤ v.len) (hv : v.agrees h) : (v.drop n).agrees h := by
  obtain ⟨⟨hlen, hoff, hvlen⟩, hb⟩ := hv
  refine ⟨⟨rfl, by simp [SpanView.drop]; omega, by simp [SpanView.drop]; omega⟩, ?_⟩
  intro j hj0 hjl
  simp only [SpanView.drop] at hjl ⊢
  obtain ⟨al, hal, hlive, hlo, hhi, hget⟩ := hb (n + j) (by omega) (by omega)
  exact ⟨al, hal, hlive, by omega, by omega, by rw [← hget]; congr 1; omega⟩

theorem SpanView.agrees_cat {h : RawHeap} {v1 v2 : SpanView}
    (halloc : v1.alloc = v2.alloc) (hadj : v1.off + v1.len = v2.off)
    (h1 : v1.agrees h) (h2 : v2.agrees h) : (v1.cat v2).agrees h := by
  obtain ⟨⟨e1, e2, e3⟩, hb1⟩ := h1
  obtain ⟨⟨f1, f2, f3⟩, hb2⟩ := h2
  refine ⟨⟨rfl, by simp [SpanView.cat]; omega, by simp [SpanView.cat]; omega⟩, ?_⟩
  intro j hj0 hjl
  simp only [SpanView.cat] at hjl ⊢
  by_cases hk : j < v1.len
  · obtain ⟨al, hal, hlive, hlo, hhi, hget⟩ := hb1 j hj0 hk
    exact ⟨al, hal, hlive, hlo, hhi, by simpa [hk] using hget⟩
  · obtain ⟨al, hal, hlive, hlo, hhi, hget⟩ := hb2 (j - v1.len) (by omega) (by omega)
    refine ⟨al, by rw [← halloc] at hal; exact hal, hlive, by omega, by omega, ?_⟩
    rw [← hget]
    simp only [hk, if_false]
    congr 1
    omega

/-! ### What owning a capability implies about the heap

Both the allocation rule and the free rule need one fact: a resource
that agrees with the heap and owns a byte is talking about a live
allocation, in bounds. Freshness and "nothing else touches this
allocation" both fall out of it. -/

theorem SpanView.owns_byte_inBounds {h : RawHeap} {v : SpanView} {a k : Int}
    (hv : v.agrees h) (ho : v.ownsCap (.byte a k)) :
    ∃ al, h.allocs a = some al ∧ 0 ≤ k ∧ k < al.size := by
  obtain ⟨e1, e2, e3⟩ := ho
  obtain ⟨_, hb⟩ := hv
  obtain ⟨al, hal, _, hlo, hhi, _⟩ := hb (k - v.off) (by omega) (by omega)
  refine ⟨al, ?_, by omega, by omega⟩
  rw [e1]; exact hal

theorem Res.owns_byte_inBounds {h : RawHeap} {r : Res} {a k : Int}
    (hr : r.agrees h) (ho : r.owns (.byte a k)) :
    ∃ al, h.allocs a = some al ∧ 0 ≤ k ∧ k < al.size := by
  cases r with
  | span v => exact SpanView.owns_byte_inBounds hr ho
  | dealloc d => exact ho.elim
  | agg m =>
      obtain ⟨j, hj, hown⟩ := ho
      exact SpanView.owns_byte_inBounds (hr.1 j hj) hown

theorem Res.owns_free_allocated {h : RawHeap} {r : Res} {a : Int}
    (hr : r.agrees h) (ho : r.owns (.free a)) :
    ∃ al, h.allocs a = some al := by
  cases r with
  | span v => exact ho.elim
  | dealloc d =>
      obtain ⟨al, hal, _, _⟩ := hr
      exact ⟨al, by rw [ho]; exact hal⟩
  | agg m => obtain ⟨_, _, hown⟩ := ho; exact hown.elim

/-! ### Context-level preservation: split and join -/

theorem own_split {h : RawHeap} {Δ : List Res} {v : SpanView} {n : Int}
    (hn0 : 0 ≤ n) (hnl : n ≤ v.len) (hown : Own h (.span v :: Δ)) :
    Own h (.span (v.take n) :: .span (v.drop n) :: Δ) := by
  obtain ⟨hag, hd0, hpd0⟩ := hown
  have hv : (Res.span v).agrees h := hag _ (by simp)
  refine ⟨?_, ?_, ?_, hpd0⟩
  · intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · exact SpanView.agrees_take hn0 hnl hv
    · exact SpanView.agrees_drop hn0 hnl hv
    · exact hag r (by simp [hr])
  · intro s hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact take_drop_disjoint
    · exact Disjoint.mono_left (take_owns_sub hn0 hnl) (hd0 s (by simp [hs]))
  · intro s hs
    exact Disjoint.mono_left (drop_owns_sub hn0 hnl) (hd0 s (by simp [hs]))

theorem own_join {h : RawHeap} {Δ : List Res} {v1 v2 : SpanView}
    (halloc : v1.alloc = v2.alloc) (hadj : v1.off + v1.len = v2.off)
    (hown : Own h (.span v1 :: .span v2 :: Δ)) :
    Own h (.span (v1.cat v2) :: Δ) := by
  obtain ⟨hag, hd1, hd2, hpd⟩ := hown
  have hv1 : (Res.span v1).agrees h := hag _ (by simp)
  have hv2 : (Res.span v2).agrees h := hag _ (by simp)
  have hl1 : 0 ≤ v1.len := hv1.1.2.2
  have hl2 : 0 ≤ v2.len := hv2.1.2.2
  refine ⟨?_, ?_, hpd⟩
  · intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact SpanView.agrees_cat halloc hadj hv1 hv2
    · exact hag r (by simp [hr])
  · intro s hs
    intro c ⟨hc, hsc⟩
    rcases cat_owns_sub halloc hadj hl1 hl2 c hc with hh | hh
    · exact hd1 s (by simp [hs]) c ⟨hh, hsc⟩
    · exact hd2 s hs c ⟨hh, hsc⟩

/-! ### `load8`, `store8`, `take8`

The view is what the contract talks about; `load_sound` is the theorem
that the machine agrees with it. Note what `own_write` needs and does
not need: it never mentions the other resources' contents, only that
they do not own the byte. -/

def SpanView.write (v : SpanView) (k : Int) (b : ByteState) : SpanView :=
  { v with bytes := v.bytes.set k b }

theorem write_owns_sub {v : SpanView} {k : Int} {b : ByteState} :
    ∀ c, (Res.span (v.write k b)).owns c → (Res.span v).owns c := by
  intro c hc
  cases c with
  | byte a j => exact hc
  | free a => exact hc.elim

theorem load_sound {h : RawHeap} {v : SpanView} {k b : Int}
    (hk0 : 0 ≤ k) (hkl : k < v.len) (hv : v.agrees h)
    (hinit : v.bytes.get k = .init b) :
    ∃ al, h.allocs v.alloc = some al ∧ al.live = true ∧
      al.bytes.get (v.off + k) = .init b := by
  obtain ⟨_, hb⟩ := hv
  obtain ⟨al, hal, hlive, _, _, hget⟩ := hb k hk0 hkl
  exact ⟨al, hal, hlive, by rw [hget, hinit]⟩

theorem own_write {h : RawHeap} {Δ : List Res} {v : SpanView} {k : Int} {b : ByteState}
    (hk0 : 0 ≤ k) (hkl : k < v.len) (hown : Own h (.span v :: Δ)) :
    Own (h.store v.alloc (v.off + k) b) (.span (v.write k b) :: Δ) := by
  obtain ⟨hag, hd0, hpd0⟩ := hown
  have hv : (Res.span v).agrees h := hag _ (by simp)
  have hvown : (Res.span v).owns (.byte v.alloc (v.off + k)) := ⟨rfl, by omega, by omega⟩
  obtain ⟨⟨hlen, hoff, hvlen⟩, hb⟩ := hv
  refine ⟨?_, ?_, hpd0⟩
  · intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · refine ⟨⟨by simpa [SpanView.write] using hlen, hoff, hvlen⟩, ?_⟩
      intro j hj0 hjl
      simp only [SpanView.write] at hjl ⊢
      obtain ⟨al, hal, hlive, hlo, hhi, hget⟩ := hb j hj0 hjl
      refine ⟨{ al with bytes := al.bytes.set (v.off + k) b }, ?_, hlive, hlo, hhi, ?_⟩
      · simp [RawHeap.store, hal]
      · by_cases hjk : j = k
        · subst hjk; simp [Seq.get_set]
        · have : v.off + j ≠ v.off + k := by omega
          simpa [Seq.get_set, this, hjk] using hget
    · exact Res.agrees_store (hag r (by simp [hr]))
        (fun ho => hd0 r (by simp [hr]) _ ⟨hvown, ho⟩)
  · intro s hs
    exact Disjoint.mono_left write_owns_sub (hd0 s hs)

/-- `take8` is `own_write` at `uninit`; reading the byte back is then not
an initialized read, which is the failed VC the plan promises. -/
theorem take_leaves_uninit {v : SpanView} {k : Int} :
    (v.write k .uninit).bytes.get k = .uninit := by
  simp [SpanView.write, Seq.get_set]

/-! ### `allocate` and `free`

Freshness is the only thing that makes a new allocation disjoint from
everything live, and it comes from heap well-formedness rather than from
inspecting the context. -/

theorem RawHeap.allocs_fresh_of_some {h : RawHeap} {a : Int} {al : Allocation} {size : Int}
    (hwf : h.wf) (hal : h.allocs a = some al) : (h.fresh size).allocs a = some al := by
  have hne : a ≠ h.next := by
    intro he
    rw [he, hwf h.next (by omega)] at hal
    simp at hal
  simp [RawHeap.fresh, hne, hal]

theorem SpanView.agrees_fresh {h : RawHeap} {v : SpanView} {size : Int}
    (hwf : h.wf) (hv : v.agrees h) : v.agrees (h.fresh size) := by
  obtain ⟨hw, hb⟩ := hv
  refine ⟨hw, fun j hj0 hjl => ?_⟩
  obtain ⟨al, hal, hlive, hlo, hhi, hget⟩ := hb j hj0 hjl
  exact ⟨al, RawHeap.allocs_fresh_of_some hwf hal, hlive, hlo, hhi, hget⟩

theorem Res.agrees_fresh {h : RawHeap} {r : Res} {size : Int}
    (hwf : h.wf) (hr : r.agrees h) : r.agrees (h.fresh size) := by
  cases r with
  | span v => exact SpanView.agrees_fresh hwf hr
  | dealloc d =>
      obtain ⟨al, hal, hlive, hsize⟩ := hr
      exact ⟨al, RawHeap.allocs_fresh_of_some hwf hal, hlive, hsize⟩
  | agg m => exact ⟨fun j hj => SpanView.agrees_fresh hwf (hr.1 j hj), hr.2⟩

def freshSpan (h : RawHeap) (size : Int) : SpanView :=
  { alloc := h.next, off := 0, len := size, bytes := ⟨size, fun _ => .uninit⟩ }

def freshDealloc (h : RawHeap) (size : Int) : DeallocView :=
  { alloc := h.next, size := size }

theorem own_alloc {h : RawHeap} {Δ : List Res} {size : Int}
    (hwf : h.wf) (hs : 0 ≤ size) (hown : Own h Δ) :
    Own (h.fresh size)
        (.span (freshSpan h size) :: .dealloc (freshDealloc h size) :: Δ)
      ∧ (h.fresh size).wf := by
  obtain ⟨hag, hpd⟩ := hown
  have hnext : (h.fresh size).allocs h.next = some ⟨size, true, ⟨size, fun _ => .uninit⟩⟩ := by
    simp [RawHeap.fresh]
  -- nothing live can name the fresh id
  have hfree : ∀ r ∈ Δ, ∀ c, ¬((Res.span (freshSpan h size)).owns c ∧ r.owns c) := by
    intro r hr c ⟨hnew, hold⟩
    cases c with
    | byte a k =>
        obtain ⟨e1, _, _⟩ := hnew
        obtain ⟨al, hal, _, _⟩ := Res.owns_byte_inBounds (hag r hr) hold
        rw [e1] at hal
        simp only [freshSpan] at hal
        rw [hwf h.next (by omega)] at hal
        simp at hal
    | free a => exact hnew.elim
  have hfree2 : ∀ r ∈ Δ, ∀ c, ¬((Res.dealloc (freshDealloc h size)).owns c ∧ r.owns c) := by
    intro r hr c ⟨hnew, hold⟩
    cases c with
    | byte a k => exact hnew.elim
    | free a =>
        obtain ⟨al, hal⟩ := Res.owns_free_allocated (hag r hr) hold
        rw [hnew] at hal
        simp only [freshDealloc] at hal
        rw [hwf h.next (by omega)] at hal
        simp at hal
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · refine ⟨⟨rfl, by simp [freshSpan], by simpa [freshSpan] using hs⟩, ?_⟩
      intro j hj0 hjl
      simp only [freshSpan] at hjl ⊢
      exact ⟨_, hnext, rfl, by omega, by simpa using hjl, rfl⟩
    · exact ⟨_, hnext, rfl, rfl⟩
    · exact Res.agrees_fresh hwf (hag r hr)
  · intro s hs'
    simp only [List.mem_cons] at hs'
    rcases hs' with rfl | hs'
    · intro c ⟨hl, hr⟩
      cases c with
      | byte a k => exact hr.elim
      | free a => exact hl.elim
    · exact hfree s hs'
  · exact fun s hs' => hfree2 s hs'
  · exact hpd
  · intro a ha
    have hne : a ≠ h.next := by simp [RawHeap.fresh] at ha ⊢; omega
    simp only [RawHeap.fresh, hne, if_false]
    exact hwf a (by simp [RawHeap.fresh] at ha; omega)

/-! ### `free`

Freeing needs to know that nothing else in the context touches the
allocation. That is not a hypothesis the caller supplies: it follows
from the consumed span covering the allocation and being disjoint from
everything else — which is the affine discipline paying for itself. -/

theorem RawHeap.allocs_release_ne {h : RawHeap} {a a' : Int} (hne : a' ≠ a) :
    (h.release a).allocs a' = h.allocs a' := by simp [RawHeap.release, hne]

theorem SpanView.agrees_release {h : RawHeap} {v : SpanView} {a : Int}
    (hv : v.agrees h) (hno : ∀ k, ¬ v.ownsCap (.byte a k)) :
    v.agrees (h.release a) := by
  obtain ⟨hw, hb⟩ := hv
  refine ⟨hw, fun j hj0 hjl => ?_⟩
  obtain ⟨al, hal, hlive, hlo, hhi, hget⟩ := hb j hj0 hjl
  have hne : v.alloc ≠ a := fun he => hno (v.off + j) ⟨he.symm, by omega, by omega⟩
  exact ⟨al, by rw [RawHeap.allocs_release_ne hne]; exact hal, hlive, hlo, hhi, hget⟩

theorem Res.agrees_release {h : RawHeap} {r : Res} {a : Int}
    (hr : r.agrees h) (hnb : ∀ k, ¬ r.owns (.byte a k)) (hnf : ¬ r.owns (.free a)) :
    r.agrees (h.release a) := by
  cases r with
  | span v => exact SpanView.agrees_release hr hnb
  | dealloc d =>
      obtain ⟨al, hal, hlive, hsize⟩ := hr
      have hne : d.alloc ≠ a := fun he => hnf he.symm
      exact ⟨al, by rw [RawHeap.allocs_release_ne hne]; exact hal, hlive, hsize⟩
  | agg m =>
      refine ⟨fun j hj => SpanView.agrees_release (hr.1 j hj) ?_, hr.2⟩
      exact fun k hown => hnb k ⟨j, hj, hown⟩

theorem own_free {h : RawHeap} {Δ : List Res} {v : SpanView} {d : DeallocView}
    {al : Allocation}
    (hsame : v.alloc = d.alloc) (hoff : v.off = 0) (hcov : v.len = al.size)
    (hal : h.allocs d.alloc = some al)
    (hown : Own h (.span v :: .dealloc d :: Δ)) :
    Own (h.release d.alloc) Δ := by
  obtain ⟨hag, hd1, hd2, hpd⟩ := hown
  refine ⟨fun r hr => ?_, hpd⟩
  refine Res.agrees_release (hag r (by simp [hr])) ?_ ?_
  · intro k hown
    obtain ⟨al', hal', hk0, hkl⟩ := Res.owns_byte_inBounds (hag r (by simp [hr])) hown
    rw [hal] at hal'
    have hee : al = al' := Option.some.inj hal'
    rw [hee] at hcov
    exact hd1 r (by simp [hr]) (.byte d.alloc k) ⟨⟨hsame.symm, by omega, by omega⟩, hown⟩
  · intro hown
    exact hd2 r hr (.free d.alloc) ⟨rfl, hown⟩

/-! ### Context reordering

`Own` cares about the *set* of live resources; list order is bookkeeping.
Two swaps are all the carving loop needs. -/

theorem own_swap {h : RawHeap} {Δ : List Res} {r s : Res}
    (hown : Own h (r :: s :: Δ)) : Own h (s :: r :: Δ) := by
  obtain ⟨hag, hd1, hd2, hpd⟩ := hown
  refine ⟨fun x hx => ?_, fun x hx => ?_,
          fun x hx => hd1 x (List.mem_cons_of_mem _ hx), hpd⟩
  · simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hag _ (by simp)
    · exact hag _ (by simp)
    · exact hag _ (by simp [hx])
  · simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact (hd1 s (by simp)).symm
    · exact hd2 x hx

theorem own_swap2 {h : RawHeap} {Δ : List Res} {r s t : Res}
    (hown : Own h (r :: s :: t :: Δ)) : Own h (r :: t :: s :: Δ) := by
  obtain ⟨hag, hd0, hd1, hd2, hpd⟩ := hown
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_,
          fun x hx => hd1 x (List.mem_cons_of_mem _ hx), hpd⟩
  · simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact hag _ (by simp)
    · exact hag _ (by simp)
    · exact hag _ (by simp)
    · exact hag _ (by simp [hx])
  · simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hd0 x (by simp)
    · exact hd0 x (by simp)
    · exact hd0 x (by simp [hx])
  · simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact (hd1 t (by simp)).symm
    · exact hd2 x hx

/-! ## Aggregate resources

A statically unknown number of permissions: **one** affine token holding
a pure map view. Note where interior disjointness comes from — not from
the map being a function, but from the token's interpretation, which
carries pairwise disjointness of everything in the domain. `take` and
`put` are the only way in and out. -/

def MapView.remove (m : MapView) (k : Int) : MapView :=
  { m with keys := fun j => m.keys j ∧ j ≠ k }

def MapView.insert (m : MapView) (k : Int) (v : SpanView) : MapView :=
  { keys := fun j => m.keys j ∨ j = k,
    view := fun j => if j = k then v else m.view j }

theorem own_take {h : RawHeap} {Δ : List Res} {m : MapView} {k : Int}
    (hk : m.keys k) (hown : Own h (.agg m :: Δ)) :
    Own h (.span (m.view k) :: .agg (m.remove k) :: Δ) := by
  obtain ⟨hag, hd0, hpd⟩ := hown
  obtain ⟨hall, hdis⟩ := hag (.agg m) (by simp)
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, hpd⟩
  · simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hall k hk
    · exact ⟨fun j hj => hall j hj.1, fun j1 j2 h1 h2 hne => hdis j1 j2 h1.1 h2.1 hne⟩
    · exact hag x (by simp [hx])
  · simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · intro c ⟨hl, hr⟩
      obtain ⟨j, ⟨hj, hjk⟩, ho⟩ := hr
      exact hdis k j hk hj (Ne.symm hjk) c ⟨hl, ho⟩
    · refine Disjoint.mono_left (r := .agg m) ?_ (hd0 x (by simp [hx]))
      intro c hc
      exact ⟨k, hk, hc⟩
  · refine Disjoint.mono_left (r := .agg m) ?_ (hd0 x (by simp [hx]))
    rintro c ⟨j, ⟨hj, _⟩, ho⟩
    exact ⟨j, hj, ho⟩

theorem own_put {h : RawHeap} {Δ : List Res} {m : MapView} {k : Int} {v : SpanView}
    (hnk : ¬ m.keys k) (hown : Own h (.span v :: .agg m :: Δ)) :
    Own h (.agg (m.insert k v) :: Δ) := by
  obtain ⟨hag, hd1, hd2, hpd⟩ := hown
  have hv : v.agrees h := hag (.span v) (by simp)
  obtain ⟨hall, hdis⟩ := hag (.agg m) (by simp)
  have hvm : Disjoint (.span v) (.agg m) := hd1 _ (by simp)
  refine ⟨fun x hx => ?_, fun x hx => ?_, hpd⟩
  · simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · refine ⟨fun j hj => ?_, fun j1 j2 h1 h2 hne c ⟨c1, c2⟩ => ?_⟩
      · simp only [MapView.insert] at hj ⊢
        by_cases hjk : j = k
        · simpa [hjk] using hv
        · rcases hj with hj | hj
          · simpa [hjk] using hall j hj
          · exact absurd hj hjk
      · simp only [MapView.insert] at h1 h2 c1 c2
        by_cases e1 : j1 = k
        · have e2 : j2 ≠ k := by omega
          simp only [e1] at c1
          simp only [if_neg e2] at c2
          rcases h2 with h2 | h2
          · exact hvm c ⟨c1, ⟨j2, h2, c2⟩⟩
          · exact absurd h2 e2
        · simp only [if_neg e1] at c1
          rcases h1 with h1 | h1
          · by_cases e2 : j2 = k
            · simp only [e2] at c2
              exact hvm c ⟨c2, ⟨j1, h1, c1⟩⟩
            · simp only [if_neg e2] at c2
              rcases h2 with h2 | h2
              · exact hdis j1 j2 h1 h2 hne c ⟨c1, c2⟩
              · exact absurd h2 e2
          · exact absurd h1 e1
    · exact hag x (by simp [hx])
  · intro c ⟨hl, hr⟩
    obtain ⟨j, hj, ho⟩ := hl
    simp only [MapView.insert] at hj ho
    by_cases hjk : j = k
    · simp only [hjk] at ho
      exact hd1 x (by simp [hx]) c ⟨ho, hr⟩
    · simp only [if_neg hjk] at ho
      rcases hj with hj | hj
      · exact hd2 x hx c ⟨⟨j, hj, ho⟩, hr⟩
      · exact absurd hj hjk

/-- The round trip: `take` then `put` restores an interpretable context,
and the map view it restores is the one it started from. -/
theorem own_take_put {h : RawHeap} {Δ : List Res} {m : MapView} {k : Int}
    (hk : m.keys k) (hown : Own h (.agg m :: Δ)) :
    Own h (.agg ((m.remove k).insert k (m.view k)) :: Δ) :=
  own_put (by simp [MapView.remove]) (own_take hk hown)

theorem take_put_keys {m : MapView} {k j : Int} (hk : m.keys k) :
    ((m.remove k).insert k (m.view k)).keys j ↔ m.keys j := by
  simp only [MapView.remove, MapView.insert]
  constructor
  · rintro (⟨h1, _⟩ | rfl) <;> simp_all
  · intro hj
    by_cases hjk : j = k
    · exact Or.inr hjk
    · exact Or.inl ⟨hj, hjk⟩

theorem take_put_view {m : MapView} {k j : Int} :
    ((m.remove k).insert k (m.view k)).view j = m.view j := by
  simp only [MapView.remove, MapView.insert]
  by_cases hjk : j = k
  · simp [hjk]
  · simp [hjk]

/-! ## The carving loop — U1 question 6

Two live tokens, `processed` and `remaining`, whose *shape* is fixed
across the backedge and whose *views* change every iteration. Each
iteration splits one byte off `remaining`, transforms it, and joins it
onto `processed`.

Three theorems, deliberately separate, because they are the three things
a loop rule has to supply:

* `carve_views_step` — the value-level invariant, which is all a user
  would write. No heap, no disjointness, no `*`.
* `carve_step_shape` — the checker's obligation: the resource shape at
  the backedge equals the shape at the head.
* `own_carve_step` — the metatheory's obligation: `Own` survives the
  backedge. Nothing in the user's invariant implies this, and nothing in
  the generated goal mentions it; it has to come from shape equality. -/

theorem carve_views_step {P R : SpanView} {orig : Seq ByteState}
    {f : ByteState → ByteState} {i n : Int}
    (hPl : P.len = i) (hRl : R.len = n - i) (hi : 0 ≤ i) (hin : i < n)
    (hPb : ∀ k, 0 ≤ k → k < i → P.bytes.get k = f (orig.get k))
    (hRb : ∀ k, 0 ≤ k → k < n - i → R.bytes.get k = orig.get (i + k)) :
    (P.cat ((R.take 1).write 0 (f (R.bytes.get 0)))).len = i + 1 ∧
    (R.drop 1).len = n - (i + 1) ∧
    (∀ k, 0 ≤ k → k < i + 1 →
      (P.cat ((R.take 1).write 0 (f (R.bytes.get 0)))).bytes.get k = f (orig.get k)) ∧
    (∀ k, 0 ≤ k → k < n - (i + 1) →
      (R.drop 1).bytes.get k = orig.get ((i + 1) + k)) := by
  refine ⟨by show P.len + 1 = i + 1; omega,
          by show R.len - 1 = n - (i + 1); omega, ?_, ?_⟩
  · intro k hk0 hk1
    show (if k < P.len then P.bytes.get k
          else ((R.take 1).write 0 (f (R.bytes.get 0))).bytes.get (k - P.len))
         = f (orig.get k)
    by_cases hk : k < P.len
    · rw [if_pos hk]
      exact hPb k hk0 (by omega)
    · rw [if_neg hk]
      have hkP : k - P.len = 0 := by omega
      rw [hkP]
      have hw : ((R.take 1).write 0 (f (R.bytes.get 0))).bytes.get 0
          = f (R.bytes.get 0) := by simp [SpanView.write, SpanView.take]
      rw [hw, hRb 0 (by omega) (by omega)]
      congr 2
      omega
  · intro k hk0 hk1
    show R.bytes.get (1 + k) = orig.get ((i + 1) + k)
    rw [hRb (1 + k) (by omega) (by omega)]
    congr 1
    omega

theorem carve_step_shape {P R : SpanView} {b : ByteState}
    (halloc : P.alloc = R.alloc) (hadj : P.off + P.len = R.off) :
    (P.cat ((R.take 1).write 0 b)).alloc = (R.drop 1).alloc ∧
    (P.cat ((R.take 1).write 0 b)).off + (P.cat ((R.take 1).write 0 b)).len
      = (R.drop 1).off := by
  refine ⟨by simp [SpanView.cat, SpanView.drop, halloc], ?_⟩
  simp only [SpanView.cat, SpanView.take, SpanView.write, SpanView.drop]
  omega

theorem own_carve_step {h : RawHeap} {Δ : List Res} {P R : SpanView} {b : ByteState}
    (halloc : P.alloc = R.alloc) (hadj : P.off + P.len = R.off) (hR : 0 < R.len)
    (hown : Own h (.span P :: .span R :: Δ)) :
    Own (h.store R.alloc (R.off + 0) b)
        (.span (P.cat ((R.take 1).write 0 b)) :: .span (R.drop 1) :: Δ) := by
  have s1 := own_swap hown
  have s2 := own_split (v := R) (n := 1) (by omega) (by omega) s1
  have s3 := own_write (v := R.take 1) (k := 0) (b := b) (by omega)
    (by simp [SpanView.take]) s2
  have s4 := own_swap2 s3
  have s5 := own_swap s4
  exact own_join (by simpa [SpanView.take, SpanView.write] using halloc)
    (by simpa [SpanView.take, SpanView.write] using hadj) s5

/-! ## Are the view contracts automation-friendly?

U1 question 1, measured the way it will actually be measured: goals
shaped like what vcgen emits — view fields as binders, callee posts as
hypotheses, guarded quantifiers, everything Int — closed by `sable_auto`
at the **production** heartbeat budget (ADR 0011). A model that needs an
unbounded budget here would be a false positive.

Note what is *absent* from every goal below: the heap, `Own`,
disjointness, provenance. The checker supplied those; what reaches Lean
is arithmetic over views. -/

set_option sable.grindHeartbeats 50000

/-- After `split_off`, the caller owes `join`'s adjacency precondition. -/
example (whole0 whole1 part : SpanView) (n : int)
    (h_pre_lo : 0 ≤ n) (h_pre_hi : n ≤ whole0.len)
    (h_keep_len : whole1.len = n)
    (h_keep_off : whole1.off = whole0.off)
    (h_keep_alloc : whole1.alloc = whole0.alloc)
    (h_part_len : part.len = whole0.len - n)
    (h_part_off : part.off = whole0.off + n)
    (h_part_alloc : part.alloc = whole0.alloc) :
    whole1.alloc = part.alloc ∧ whole1.off + whole1.len = part.off := by
  sable_auto

/-- A pointer formed at index `j` of a span is inside the span's extent —
the range precondition every `load8`/`store8` carries. -/
example (v : SpanView) (j : int)
    (h_wf_off : 0 ≤ v.off) (h_wf_len : 0 ≤ v.len)
    (h_lo : 0 ≤ j) (h_hi : j < v.len) :
    v.off ≤ v.off + j ∧ v.off + j < v.off + v.len := by
  sable_auto

/-- `store8` then `load8` at the same index: the read sees the write. -/
example (v0 v1 : SpanView) (j b : int)
    (h_pre_lo : 0 ≤ j) (h_pre_hi : j < v0.len)
    (h_post_len : v1.len = v0.len)
    (h_post_bytes : ∀ k, 0 ≤ k → k < v0.len →
        v1.bytes.get k = (if k = j then ByteState.init b else v0.bytes.get k)) :
    v1.bytes.get j = ByteState.init b := by
  sable_auto

/-- The frame obligation, after the checker has done its half: a second
span's bytes are unchanged, and nothing about disjointness appears. -/
example (w0 w1 : SpanView) (k : int)
    (h_len : w1.len = w0.len)
    (h_unchanged : ∀ j, 0 ≤ j → j < w0.len → w1.bytes.get j = w0.bytes.get j)
    (h_lo : 0 ≤ k) (h_hi : k < w1.len) :
    w1.bytes.get k = w0.bytes.get k := by
  sable_auto

/-- The carving loop's invariant, preserved across the backedge — the
value-level half, which is all a user writes. -/
example (P0 P1 R0 R1 : SpanView) (orig : seq ByteState)
    (f : ByteState → ByteState) (i n : int)
    (h_inv_plen : P0.len = i)
    (h_inv_rlen : R0.len = n - i)
    (h_inv_pb : ∀ k, 0 ≤ k → k < i → P0.bytes.get k = f (orig.get k))
    (h_inv_rb : ∀ k, 0 ≤ k → k < n - i → R0.bytes.get k = orig.get (i + k))
    (h_i0 : 0 ≤ i) (h_path : i < n)
    (h_p1_len : P1.len = P0.len + 1)
    (h_p1_b : ∀ k, 0 ≤ k → k < P0.len → P1.bytes.get k = P0.bytes.get k)
    (h_p1_top : P1.bytes.get P0.len = f (R0.bytes.get 0))
    (h_r1_len : R1.len = R0.len - 1)
    (h_r1_b : ∀ k, 0 ≤ k → k < R0.len - 1 → R1.bytes.get k = R0.bytes.get (1 + k)) :
    P1.len = i + 1 ∧ R1.len = n - (i + 1) ∧
    (∀ k, 0 ≤ k → k < i + 1 → P1.bytes.get k = f (orig.get k)) ∧
    (∀ k, 0 ≤ k → k < n - (i + 1) → R1.bytes.get k = orig.get ((i + 1) + k)) := by
  sable_auto

/-! ## No `sorry`

The trio below is Lean's standard axiom set; `sorryAx` never appears. -/

#print axioms own_split
#print axioms own_join
#print axioms own_write
#print axioms own_alloc
#print axioms own_free
#print axioms own_take
#print axioms own_put
#print axioms own_take_put
#print axioms load_sound
#print axioms carve_views_step
#print axioms carve_step_shape
#print axioms own_carve_step

/-!
## Findings — U1's six questions

**1. Are the pure view contracts concise and automation-friendly? Yes.**
The five goals above are shaped the way vcgen emits them and close under
`sable_auto` at the default 50000k budget with no budget warnings. The
whole file elaborates in ~1.7s.

**2. Can the hidden interpretation establish separation without exposing
`*` in user clauses? Yes, and it costs one lemma.** Nothing a user would
read mentions `Own`, `Disjoint`, or the heap. `Disjoint.mono_left` plus
per-byte backing carries every framing argument; `own_write` never
mentions another resource's contents, only that it does not own the
byte.

**3. Does the aggregate design work beyond a hand-picked finite list?
Yes — with one correction.** `MapView` is a total function plus a `keys`
predicate, so nothing is finite or enumerated. But interior disjointness
does **not** follow from the map being a function: `Res.agrees (.agg m)`
carries the pairwise clause explicitly, and `own_put` needs it as a
premise it cannot reconstruct. The earlier sketch claimed the function
property was enough; it is not.

**4. Which facts must the checker maintain rather than prove per call?**
The boundary came out sharp. The checker maintains token identity,
footprint containment across split/join, and freshness of allocation
ids. Lean proves index arithmetic and byte equalities. `own_free` is the
clean case: "nothing else in the context touches this allocation" is
*derived* from disjointness plus coverage — it is never a caller-side
obligation.

**5. Does abstract typed storage avoid premature byte-representation
machinery? Not answered here.** This probe is byte-only. What it does
establish is that the byte model has room: `Allocation.bytes` is
consulted only through `SpanView.backed`, so a typed extent kind is a
new case in one predicate and touches no span theorem. The concrete Lean
encoding of a heterogeneous typed extent is the open question and
deserves its own pass before U7b.

**6. Can a loop with fixed shape and changing views be verified with
ordinary value-level invariants? Yes.** Three separate theorems, and the
separation is the point: `carve_views_step` is what a user writes,
`carve_step_shape` is the checker's obligation, `own_carve_step` is the
metatheory's. The strongest result in the probe is *how* the last one is
proved — by composing `own_swap`, `own_split`, `own_write`, and
`own_join`, with no bespoke loop reasoning. So the backedge is not a new
proof burden: shape equality plus the per-operation rules is the whole
loop rule, and the induction over iterations is the standard one.

## Two design findings worth carrying into U2b

**Per-byte backing is load-bearing, and the obvious encoding is wrong.**
Stating backing once per span (`∃ al, … covering [off, off+len)`) makes
an *empty* span assert that its allocation is live. `own_free` then
breaks: a zero-length residual span in the freed allocation owns no byte,
so disjointness cannot rule it out, yet it stops agreeing. Per-byte
backing makes empty spans vacuously backed — no authority, no
constraint — and `free` needs no side condition. Split and join become
index arithmetic as a bonus.

**`Own` is a list here, but the context is a set.** The primitive rules
act on the head, so the carving loop needed `own_swap` and `own_swap2`
purely as bookkeeping. Either the checker's context should be an
unordered structure, or the rules should be stated positionally. This is
noise in the metatheory, not depth — but it is noise a first
implementation will otherwise reproduce.
-/
