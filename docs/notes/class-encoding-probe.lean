import Sable
open Sable
set_option linter.unusedVariables false

-- The class encoding: a Lean structure per class; methods bind the entry
-- state as _old_self; the current state is an update-chain string.

structure BoundedStack where
  buf : Sable.Seq Int
  len : Int

-- 1. Does simp/omega see through projections of update chains?
-- push success path: invariant re-established at exit.
theorem p_inv_exit (_old_self : BoundedStack) (x : Int)
    (h_inv_1 : (_old_self.len ≤ _old_self.buf.len))
    (h_inv_2 : (_old_self.buf.len > 0))
    (h_x : i32.min ≤ x ∧ x ≤ i32.max)
    (h_path : ¬(_old_self.len = _old_self.buf.len))
    (h_fact : 0 ≤ _old_self.len ∧ _old_self.len < ((_old_self.buf).len)) :
    ({ { _old_self with buf := ((_old_self.buf).set _old_self.len x) } with
        len := (_old_self.len + 1) }.len
      ≤ { { _old_self with buf := ((_old_self.buf).set _old_self.len x) } with
        len := (_old_self.len + 1) }.buf.len) := by sable_auto

-- 2. push post, success branch (result ↔ True path):
theorem p_post_push (_old_self : BoundedStack) (x : Int) (result : Prop)
    (h_inv_1 : (_old_self.len ≤ _old_self.buf.len))
    (h_path : ¬(_old_self.len = _old_self.buf.len))
    (h_result : (result ↔ True)) :
    (result → { { _old_self with buf := ((_old_self.buf).set _old_self.len x) } with
        len := (_old_self.len + 1) }.len = _old_self.len + 1
      ∧ { { _old_self with buf := ((_old_self.buf).set _old_self.len x) } with
        len := (_old_self.len + 1) }.buf.get (_old_self.len) = x) := by sable_auto

-- 3. push post, failure branch: self = old self (structure equality of the
-- unmodified chain — should be rfl-easy)
theorem p_post_push_fail (_old_self : BoundedStack) (x : Int) (result : Prop)
    (h_path : (_old_self.len = _old_self.buf.len))
    (h_result : (result ↔ False)) :
    (¬result → _old_self = _old_self) := by sable_auto

-- 4. init exit: invariant on a record literal
theorem p_init (cap : Int) (fresh_buf : Sable.Seq Int)
    (h_pre : (cap > 0))
    (h_alloc_len : (fresh_buf.len) = cap) :
    ((BoundedStack.mk fresh_buf 0).len ≤ (BoundedStack.mk fresh_buf 0).buf.len) := by sable_auto

-- 5. pop post via caller-side fresh state: invariant + posts as hyps
theorem p_caller (s0 s1 : BoundedStack) (r : Prop)
    (h_inv_s1_1 : (s1.len ≤ s1.buf.len))
    (h_post : (r → s1.len = s0.len + 1 ∧ s1.buf.get s0.len = 7))
    (h_r : r) :
    s1.len = s0.len + 1 := by sable_auto
