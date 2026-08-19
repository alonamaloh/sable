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
allocation, cleanup, and call ABI transitions remain outside this certificate
slice.
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

end Sable
