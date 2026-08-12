/- Direct guards for the `uart-poll-v1` profile wrapper. -/

import Sable.SVMUart

namespace Sable
namespace SVMUart

private def u64 (n : Int) : SVM.Expr := .intLit .u64 n
private def u8 (n : Int) : SVM.Expr := .intLit .u8 n

private def outcome (body : List SVM.Stmt) : String :=
  (run SVM.Prog.empty 1000000 100
    (Config.bare (.run body SVM.Env.empty [] .empty))).render

/-! ## Script selection and exact oracle consumption -/

#guard scriptedOracle 0 0 = 1
#guard scriptedOracle 0 100 = 1
#guard scriptedOracle 1 0 = 0
#guard scriptedOracle 1 1 = 0
#guard scriptedOracle 1 2 = 1
#guard scriptedOracle 1 100 = 1
#guard scriptedOracle 2 100 = 0

/- Immediate readiness consumes one oracle byte, then the write follows the
read in the chronological trace. -/
#guard outcome
  [ .testUartProfile (u64 0),
    .uartStatus "status",
    .uartWrite (u8 65),
    .ret (.var "status") ]
  = "done int 1 | profile=uart-poll-v1 cursor=1 trace=[read(uart0,status,4096,8,1),write(uart0,tx,4097,8,65)]"

/- The delayed script consumes exactly three values to observe readiness. -/
#guard outcome
  [ .testUartProfile (u64 1),
    .uartStatus "s0",
    .uartStatus "s1",
    .uartStatus "s2",
    .ret (.var "s2") ]
  = "done int 1 | profile=uart-poll-v1 cursor=3 trace=[read(uart0,status,4096,8,0),read(uart0,status,4096,8,0),read(uart0,status,4096,8,1)]"

/- Every other script remains not-ready while still consuming one value per
status operation. -/
#guard outcome
  [ .testUartProfile (u64 7),
    .uartStatus "s0",
    .uartStatus "s1",
    .ret (.var "s1") ]
  = "done int 0 | profile=uart-poll-v1 cursor=2 trace=[read(uart0,status,4096,8,0),read(uart0,status,4096,8,0)]"

/-! ## Partial-operation guards -/

/- A successful write clears readiness. A second write without another
status read is `undef`, and the completed observations remain visible. -/
#guard outcome
  [ .testUartProfile (u64 0),
    .uartStatus "status",
    .uartWrite (u8 65),
    .uartWrite (u8 66) ]
  = "undef | profile=uart-poll-v1 cursor=1 trace=[read(uart0,status,4096,8,1),write(uart0,tx,4097,8,65)]"

/- Selection does not itself grant readiness. -/
#guard outcome
  [ .testUartProfile (u64 1),
    .uartWrite (u8 65) ]
  = "undef | profile=uart-poll-v1 cursor=0 trace=[]"

/- A not-ready status does not authorize a write. -/
#guard outcome
  [ .testUartProfile (u64 1),
    .uartStatus "status",
    .uartWrite (u8 65) ]
  = "undef | profile=uart-poll-v1 cursor=1 trace=[read(uart0,status,4096,8,0)]"

/- Write values must have both integer shape and `u8` range. -/
#guard outcome
  [ .testUartProfile (u64 0),
    .uartStatus "status",
    .uartWrite (u64 256) ]
  = "undef | profile=uart-poll-v1 cursor=1 trace=[read(uart0,status,4096,8,1)]"

#guard outcome
  [ .testUartProfile (u64 0),
    .uartStatus "status",
    .uartWrite (.boolLit true) ]
  = "undef | profile=uart-poll-v1 cursor=1 trace=[read(uart0,status,4096,8,1)]"

/- A profile operation on the production-bare machine is `undef`. -/
#guard outcome [ .uartStatus "status" ] = "undef"
#guard outcome [ .uartWrite (u8 65) ] = "undef"

/- The test constructor itself requires an integer and may run only once. -/
#guard outcome [ .testUartProfile (.boolLit false) ] = "undef"

#guard outcome
  [ .testUartProfile (u64 0),
    .testUartProfile (u64 0) ]
  = "undef | profile=uart-poll-v1 cursor=0 trace=[]"

/-! ## Core delegation and observation compatibility -/

/- Bare, non-profile execution retains the core wire format byte-for-byte. -/
#guard outcome [ .assign "x" (u64 7), .ret (.var "x") ] = "done int 7"

/- Delegated core steps preserve the selected state through termination. -/
#guard outcome
  [ .testUartProfile (u64 0),
    .assign "x" (u64 7),
    .ret (.var "x") ]
  = "done int 7 | profile=uart-poll-v1 cursor=0 trace=[]"

/- Contract projection ignores status reads and keeps writes ordered. -/
private def projected : UartView :=
  ((((scriptedUart 0).afterStatus 1).afterWrite 65).afterStatus 1).afterWrite 66

#guard projected.writes = [65, 66]

end SVMUart
end Sable
