/-
U8f2 probe — lift the sorted offset chain over AllocatorView.headers.

Run from `lean/`:

  lake env lean ../docs/notes/stored-free-list-chain-probe.lean
-/

import Sable
open Sable

namespace StoredFreeListChainProbe

def hasFields
    (header : FreeHeaderView) (size next : Int) : Prop :=
  header.sizeCell.state = .init size ∧
  header.nextCell.state = .init next

def storesHeader
    (v : AllocatorView) (key : Int) (header : FreeHeaderView) : Prop :=
  v.headers key = some header ∧
  v.free key = none ∧
  header.key = key ∧
  header.wf ∧
  header.allocator = v.allocator

inductive StoredChain (v : AllocatorView) (limit : Int) : Int → Prop where
  | nil : StoredChain v limit limit
  | cons (key size next : Int) (header : FreeHeaderView)
      (stored : storesHeader v key header)
      (fields : hasFields header size next)
      (key_nonneg : 0 ≤ key)
      (header_fits : freeHeaderBytes ≤ size)
      (ordered_disjoint : key + size ≤ next)
      (next_bounded : next ≤ limit)
      (tail : StoredChain v limit next) : StoredChain v limit key

theorem storesHeader_headerAt
    {v : AllocatorView} {key : Int} {header : FreeHeaderView}
    (h : storesHeader v key header) : v.headerAt key = header := by
  simp [AllocatorView.headerAt, h.1]

theorem storesHeader_canTake
    {v : AllocatorView} {key : Int} {header : FreeHeaderView}
    (h : storesHeader v key header) : v.canTakeHeader key := by
  have hat : v.headerAt key = header := storesHeader_headerAt h
  exact ⟨by simp [h.1], h.2.1, by simpa [hat] using h.2.2.1,
    by simpa [hat] using h.2.2.2.1,
    by simpa [hat] using h.2.2.2.2⟩

theorem StoredChain.step {v : AllocatorView} {limit head : Int}
    (chain : StoredChain v limit head) (hne : head ≠ limit) :
    ∃ header size next,
      storesHeader v head header ∧
      hasFields header size next ∧
      freeHeaderBytes ≤ size ∧
      head + size ≤ next ∧
      next ≤ limit ∧
      StoredChain v limit next := by
  cases chain with
  | nil => exact (hne rfl).elim
  | cons key size next header stored fields hkey hheader horder hbound tail =>
      exact ⟨header, size, next, stored, fields, hheader, horder, hbound, tail⟩

theorem StoredChain.takeable {v : AllocatorView} {limit head : Int}
    (chain : StoredChain v limit head) (hne : head ≠ limit) :
    v.canTakeHeader head := by
  obtain ⟨header, _, _, stored, _⟩ := chain.step hne
  exact storesHeader_canTake stored

theorem StoredChain.step_variant {v : AllocatorView} {limit head : Int}
    (chain : StoredChain v limit head) (hne : head ≠ limit) :
    ∃ next, 0 ≤ limit - next ∧ limit - next < limit - head ∧
      StoredChain v limit next := by
  obtain ⟨_, size, next, _, _, hheader, horder, hbound, tail⟩ :=
    chain.step hne
  refine ⟨next, by omega, ?_, tail⟩
  simp [freeHeaderBytes, u64.layout] at hheader
  omega

theorem StoredChain.extract_restore
    {v : AllocatorView} {limit head : Int}
    (chain : StoredChain v limit head) (hne : head ≠ limit) :
    (v.takeHeader head).putHeader (v.headerAt head) = v := by
  exact AllocatorView.takeHeader_putHeader v head (chain.takeable hne)

theorem StoredChain.singleAfterPut
    {v : AllocatorView} {header : FreeHeaderView} {size limit : Int}
    (hput : v.canPutHeader header)
    (hfields : hasFields header size limit)
    (hkey : 0 ≤ header.key)
    (hsize : freeHeaderBytes ≤ size)
    (hbound : header.key + size ≤ limit) :
    StoredChain (v.putHeader header) limit header.key := by
  apply StoredChain.cons header.key size limit header
  · exact ⟨by simp [AllocatorView.putHeader],
      by simpa [AllocatorView.putHeader] using hput.2.2.1,
      rfl, hput.2.1,
      by change header.allocator = v.allocator; exact hput.1⟩
  · exact hfields
  · exact hkey
  · exact hsize
  · exact hbound
  · omega
  · exact StoredChain.nil

#check StoredChain.step
#check StoredChain.takeable
#check StoredChain.step_variant
#check StoredChain.extract_restore
#check StoredChain.singleAfterPut

end StoredFreeListChainProbe
