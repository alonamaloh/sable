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
length relation installed for the callee's post-state.

This validates those emitted transition facts.  It does not validate mutation
discovery or the complete source-to-symbolic translation.
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

end Sable
