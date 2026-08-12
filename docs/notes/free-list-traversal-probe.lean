/-
U8f probe — sorted in-band free-list traversal policy.

Run from `lean/`:

  lake env lean ../docs/notes/free-list-traversal-probe.lean

The runtime head and every link are ordinary u64 offsets. `root.len` is the
one-past-end sentinel, so key zero remains available for a real block. A
structural Chain packages finite reachability; increasing keys then give the
program loop the arithmetic variant `root.len - current`.
-/

import Sable
open Sable

namespace FreeListTraversalProbe

/-- A finite sorted free-list chain whose index is its runtime head key. -/
inductive Chain (limit : Int) : Int → Prop where
  | nil : Chain limit limit
  | cons (key size next : Int)
      (key_nonneg : 0 ≤ key)
      (header_fits : freeHeaderBytes ≤ size)
      (ordered_disjoint : key + size ≤ next)
      (next_bounded : next ≤ limit)
      (tail : Chain limit next) : Chain limit key

/-- Direct elimination form used by a traversal iteration. -/
theorem Chain.step {limit head : Int} (h : Chain limit head)
    (hne : head ≠ limit) :
    ∃ size next,
      freeHeaderBytes ≤ size ∧
      head + size ≤ next ∧
      next ≤ limit ∧
      Chain limit next := by
  cases h with
  | nil => exact (hne rfl).elim
  | cons key size next hkey hheader horder hbound tail =>
      exact ⟨size, next, hheader, horder, hbound, tail⟩

theorem Chain.head_bounds {limit head : Int}
    (hlimit : 0 ≤ limit) (h : Chain limit head) :
    0 ≤ head ∧ head ≤ limit := by
  cases h with
  | nil => exact ⟨hlimit, by omega⟩
  | cons key size next hkey hheader horder hbound tail =>
      simp [freeHeaderBytes, u64.layout] at hheader
      exact ⟨hkey, by omega⟩

theorem Chain.real_key_before_sentinel {limit head : Int}
    (h : Chain limit head) (hne : head ≠ limit) : head < limit := by
  obtain ⟨size, next, hheader, horder, hbound, _⟩ := h.step hne
  simp [freeHeaderBytes, u64.layout] at hheader
  omega

/-- Every real node has room for both typed header words inside the root. -/
theorem Chain.header_inside_root {limit head : Int}
    (h : Chain limit head) (hne : head ≠ limit) :
    head + freeHeaderBytes ≤ limit := by
  obtain ⟨size, next, hheader, horder, hbound, _⟩ := h.step hne
  omega

/-- Convenient premise-oriented form for generated loop obligations. -/
theorem step_variant
    {limit key size next : Int}
    (hheader : freeHeaderBytes ≤ size)
    (horder : key + size ≤ next)
    (hbound : next ≤ limit) :
    0 ≤ limit - next ∧ limit - next < limit - key := by
  simp [freeHeaderBytes, u64.layout] at hheader
  omega

/-- Both stored fields fit u64 whenever the root length does. -/
theorem fields_fit_u64
    {limit key size next : Int}
    (hkey : 0 ≤ key)
    (hheader : freeHeaderBytes ≤ size)
    (horder : key + size ≤ next)
    (hbound : next ≤ limit)
    (hlimit : limit ≤ u64.max) :
    (0 ≤ size ∧ size ≤ u64.max) ∧
    (0 ≤ next ∧ next ≤ u64.max) := by
  simp [freeHeaderBytes, u64.layout] at hheader
  omega

/-- Equality in the ordering constraint is exactly the local coalescing case. -/
theorem successor_adjacent
    {key size next : Int}
    (horder : key + size ≤ next)
    (hno_gap : ¬ key + size < next) : key + size = next := by
  omega

/-- Splitting at an aligned request leaves an aligned header-capable suffix. -/
theorem aligned_remainder
    {key size request : Int}
    (hkey : key % u64.layout.align = 0)
    (hrequest : request % u64.layout.align = 0)
    (hremainder : freeHeaderBytes ≤ size - request) :
    (key + request) % u64.layout.align = 0 ∧
    freeHeaderBytes ≤ size - request := by
  constructor
  · simp [u64.layout] at hkey hrequest ⊢
    omega
  · exact hremainder

/-- If the suffix is smaller than a header, allocation must consume the whole
block rather than manufacture an unusable free node. -/
theorem no_tiny_remainder
    {size request : Int}
    (hfit : request ≤ size)
    (htiny : size - request < freeHeaderBytes) :
    0 ≤ size - request ∧ ¬ freeHeaderBytes ≤ size - request := by
  exact ⟨by omega, by omega⟩

#check Chain.step
#check Chain.head_bounds
#check Chain.real_key_before_sentinel
#check Chain.header_inside_root
#check step_variant
#check fields_fit_u64
#check successor_adjacent
#check aligned_remainder
#check no_tiny_remainder

end FreeListTraversalProbe
