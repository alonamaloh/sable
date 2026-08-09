/-
Sable prelude: bounds of the program-language integer types.

Program values lift into Lean as `Int` (design §2.1); the VCgen guarantees
representability per operation, so these bounds appear both as hypotheses
(range facts on binders) and as goals (overflow obligations).

Names are chosen so clause authors can write `u32.max`, `i8.min`, etc.
after `open Sable`.
-/

namespace Sable

def u8.max  : Int := 255
def u16.max : Int := 65535
def u32.max : Int := 4294967295
def u64.max : Int := 18446744073709551615

def i8.min  : Int := -128
def i8.max  : Int := 127
def i16.min : Int := -32768
def i16.max : Int := 32767
def i32.min : Int := -2147483648
def i32.max : Int := 2147483647
def i64.min : Int := -9223372036854775808
def i64.max : Int := 9223372036854775807

end Sable
