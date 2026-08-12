/-
Profile-independent MMIO observations and the ghost UART view used by
contracts. Events are stored in chronological order: appending an event
means it happened after every event already in the trace.
-/

import Lean

namespace Sable

/-- One externally observable MMIO access. Device and register names make
traces readable; the address, width, and value make them exact enough for
the differential oracle. Widths are in bits. -/
inductive MmioEvent where
  | read
      (device : String) (register : String)
      (address : Int) (width : Int) (value : Int)
  | write
      (device : String) (register : String)
      (address : Int) (width : Int) (value : Int)
  deriving Repr, DecidableEq

def uartDevice : String := "uart0"
def uartStatusRegister : String := "status"
def uartTxRegister : String := "tx"
def uartStatusAddress : Int := 4096
def uartTxAddress : Int := 4097
def uartWidth : Int := 8

def MmioEvent.uartStatusRead (value : Int) : MmioEvent :=
  .read uartDevice uartStatusRegister uartStatusAddress uartWidth value

def MmioEvent.uartTxWrite (value : Int) : MmioEvent :=
  .write uartDevice uartTxRegister uartTxAddress uartWidth value

/-- A stable, compact rendering used by observed SVM outcomes. -/
def MmioEvent.render : MmioEvent → String
  | .read device register address width value =>
      s!"read({device},{register},{address},{width},{value})"
  | .write device register address width value =>
      s!"write({device},{register},{address},{width},{value})"

/-- Keep only writes to the selected UART's transmit register. -/
def MmioEvent.uartTxValue? : MmioEvent → Option Int
  | .write device register address width value =>
      if device = uartDevice ∧ register = uartTxRegister ∧
          address = uartTxAddress ∧ width = uartWidth then
        some value
      else
        none
  | .read .. => none

/-- The contract-level view of the UART capability. The oracle is an
explicit input stream indexed by `cursor`; the trace is chronological. -/
structure UartView where
  ready : Bool
  oracle : Nat → Int
  cursor : Nat
  trace : List MmioEvent

/-- The next status byte without consuming it. -/
def UartView.status (u : UartView) : Int :=
  u.oracle u.cursor

/-- Every oracle entry is a byte. Scripted profiles use only zero and one,
but the abstract contract deliberately permits every `u8`. -/
def UartView.wf (u : UartView) : Prop :=
  ∀ i, 0 ≤ u.oracle i ∧ u.oracle i ≤ 255

/-- Consume exactly one oracle byte and record the corresponding status
read. The resulting readiness bit reflects whether that byte was nonzero. -/
def UartView.afterStatus (u : UartView) (value : Int) : UartView :=
  { u with
    ready := decide (value ≠ 0)
    cursor := u.cursor + 1
    trace := u.trace ++ [MmioEvent.uartStatusRead value] }

/-- Record one transmit write and require a fresh readiness observation
before a subsequent write. Range and readiness checks belong to the SVM
profile transition; this pure view function states only the effect. -/
def UartView.afterWrite (u : UartView) (value : Int) : UartView :=
  { u with
    ready := false
    trace := u.trace ++ [MmioEvent.uartTxWrite value] }

/-- Chronological bytes written to UART0's transmit register. -/
def UartView.writes (u : UartView) : List Int :=
  u.trace.filterMap MmioEvent.uartTxValue?

@[simp] theorem UartView.afterStatus_ready (u : UartView) (value : Int) :
    (u.afterStatus value).ready = decide (value ≠ 0) := rfl

@[simp] theorem UartView.afterStatus_cursor (u : UartView) (value : Int) :
    (u.afterStatus value).cursor = u.cursor + 1 := rfl

@[simp] theorem UartView.afterStatus_trace (u : UartView) (value : Int) :
    (u.afterStatus value).trace =
      u.trace ++ [MmioEvent.uartStatusRead value] := rfl

@[simp] theorem UartView.afterWrite_ready (u : UartView) (value : Int) :
    (u.afterWrite value).ready = false := rfl

@[simp] theorem UartView.afterWrite_cursor (u : UartView) (value : Int) :
    (u.afterWrite value).cursor = u.cursor := rfl

@[simp] theorem UartView.afterWrite_trace (u : UartView) (value : Int) :
    (u.afterWrite value).trace =
      u.trace ++ [MmioEvent.uartTxWrite value] := rfl

@[simp] theorem UartView.afterStatus_wf (u : UartView) (value : Int) :
    (u.afterStatus value).wf ↔ u.wf := Iff.rfl

@[simp] theorem UartView.afterWrite_wf (u : UartView) (value : Int) :
    (u.afterWrite value).wf ↔ u.wf := Iff.rfl

theorem UartView.status_u8 {u : UartView} (h : u.wf) :
    0 ≤ u.status ∧ u.status ≤ 255 :=
  h u.cursor

@[simp] theorem UartView.writes_afterStatus (u : UartView) (value : Int) :
    (u.afterStatus value).writes = u.writes := by
  simp [UartView.afterStatus, UartView.writes, MmioEvent.uartTxValue?,
    MmioEvent.uartStatusRead]

@[simp] theorem UartView.writes_afterWrite (u : UartView) (value : Int) :
    (u.afterWrite value).writes = u.writes ++ [value] := by
  simp [UartView.afterWrite, UartView.writes, MmioEvent.uartTxValue?,
    MmioEvent.uartTxWrite, uartDevice, uartTxRegister, uartTxAddress, uartWidth]

end Sable
