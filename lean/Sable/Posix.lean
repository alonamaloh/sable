/-
Sable prelude: views for non-memory resources.

The first two are POSIX-shaped: an open file description, and the external
world it lives in. They follow the same rule as `SpanView` — the resource
is authority the checker keeps affine, and what the logic sees is an
ordinary value whose facts are duplicable knowledge.

Everything is `Int` for the same reason the rest of the prelude is, and
everything here is arithmetic on purpose: the dynamic monitor has to be
able to evaluate these clauses, and a `Int → Prop` field would be
unmonitorable the moment a contract mentioned it.
-/

import Sable.Seq

namespace Sable

/-- The view of an `OpenFile`: which descriptor, and where in the file
this description is positioned.

The *position* lives here rather than in the world because that is where
POSIX puts it — an open file description has its own offset, and two
descriptions of one file advance independently. -/
structure OpenFileView where
  fd : Int
  pos : Int

/-- The view of a `PosixWorld`: the external state a foreign call may
observe or change.

`data` is the byte stream a descriptor reads from, indexed by absolute
position. `fds` is how many descriptors the world has handed out, so a
descriptor is valid exactly when `0 ≤ fd < fds` — crude, and monitorable,
which is the trade this rung wants.

What is deliberately *not* here: whether the next read is short, and
whether it fails. Those are real external behaviour and no contract can
predict them, so they appear in the machine and the monitor but never in
the view. A caller that wants to be correct must handle every outcome the
contract admits, which is the whole point of passing the world
explicitly.

`claimed` is which descriptors' *authority* has already been handed out:
`claimed.get fd ≠ 0` means an `OpenFile` for `fd` exists somewhere. The
world is the only source of that authority, and it can supply it once —
without this, affinity stops a program reusing one token but not minting
a second token for the same descriptor, which is the same duplication by
another route. -/
structure PosixWorldView where
  data : Seq Int
  fds : Int
  claimed : Seq Int

/-- Well-formedness of a world, assumed at every binding site: the
stream really is a *byte* stream, and the descriptor count is a count.

The byte range is load-bearing rather than tidy. Without it, a `read`
post that says "these bytes came from the stream" says nothing about
whether they are bytes, and reconstructing the caller's `[u8]` from them
fails — which is exactly how the exposure obligation caught the contract
being under-specified.

The range is stated for *every* index, not just `[0, len)`. Off-the-end
junk is our modelling choice as much as the stream is, and choosing it to
be a byte costs nothing and removes a window premise from every read
contract — which is the difference between a wrapper that verifies and one
that needs a hand proof. -/
def PosixWorldView.wf (w : PosixWorldView) : Prop :=
  0 ≤ w.fds ∧ 0 ≤ w.data.len ∧ ∀ k, 0 ≤ w.data.get k ∧ w.data.get k ≤ 255

@[simp] theorem PosixWorldView.wf_iff (w : PosixWorldView) :
    w.wf ↔ (0 ≤ w.fds ∧ 0 ≤ w.data.len ∧
      ∀ k, 0 ≤ w.data.get k ∧ w.data.get k ≤ 255) := Iff.rfl

/-- A descriptor this world has handed out. -/
def PosixWorldView.isOpen (w : PosixWorldView) (fd : Int) : Prop :=
  0 ≤ fd ∧ fd < w.fds

@[simp] theorem PosixWorldView.isOpen_iff (w : PosixWorldView) (fd : Int) :
    w.isOpen fd ↔ (0 ≤ fd ∧ fd < w.fds) := Iff.rfl

/-- A descriptor whose authority the world can still hand out: open, and
not already claimed. This is `open_file`'s precondition. -/
def PosixWorldView.available (w : PosixWorldView) (fd : Int) : Prop :=
  w.isOpen fd ∧ w.claimed.get fd = 0

@[simp] theorem PosixWorldView.available_iff (w : PosixWorldView) (fd : Int) :
    w.available fd ↔ (w.isOpen fd ∧ w.claimed.get fd = 0) := Iff.rfl

/-- The world after handing out `fd`'s authority.

Stated as a function of the old world rather than as a conjunction of
"this changed, everything else did not": a functional effect is one
rewrite for `grind`, where the conjunction form leaves it in case
analysis at every use (the lesson ADR 0026 records). -/
def PosixWorldView.claim (w : PosixWorldView) (fd : Int) : PosixWorldView :=
  { w with claimed := w.claimed.set fd 1 }

@[simp] theorem PosixWorldView.claim_data (w : PosixWorldView) (fd : Int) :
    (w.claim fd).data = w.data := rfl

@[simp] theorem PosixWorldView.claim_fds (w : PosixWorldView) (fd : Int) :
    (w.claim fd).fds = w.fds := rfl

@[simp] theorem PosixWorldView.claim_claimed (w : PosixWorldView) (fd : Int) :
    (w.claim fd).claimed = w.claimed.set fd 1 := rfl

/-- The bytes a read of `n` bytes at `pos` would return, as a claim about
the world's stream rather than a value: `read` reports how many bytes it
actually transferred, and only that many are constrained. -/
def PosixWorldView.byteAt (w : PosixWorldView) (pos : Int) : Int :=
  w.data.get pos

@[simp] theorem PosixWorldView.byteAt_def (w : PosixWorldView) (pos : Int) :
    w.byteAt pos = w.data.get pos := rfl

/-- A newly opened description starts at the beginning. -/
def OpenFileView.atStart (f : OpenFileView) (fd : Int) : Prop :=
  f.fd = fd ∧ f.pos = 0

@[simp] theorem OpenFileView.atStart_iff (f : OpenFileView) (fd : Int) :
    f.atStart fd ↔ (f.fd = fd ∧ f.pos = 0) := Iff.rfl

end Sable
