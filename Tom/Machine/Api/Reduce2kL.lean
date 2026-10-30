import Tom.Machine.Img
import Tom.Machine.Fn.Reduce2kL
import Tom.Spec.ModShape

/-!
# `mp_reduce_is_2k_l`: the standard contract

From the entry, `mp_reduce_is_2k_l(a)` with `a` shaped returns to `ra` with
`a0 = isReduce2kL a` (`MP_NO` for zero, `MP_YES` for one digit, otherwise
`MP_YES` iff at least `used / 2` digits are `MP_DIGIT_MAX`), the callee-saved
registers and all of memory unchanged (no frame, no store: no stack region).
-/

namespace Tom.Machine.Api.Reduce2kL

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

structure Pre (m : Mem) (pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  ra_al : ra.toNat % 4 = 0
  img : Img m

def Ret (m : Mem) (v : Abi) (outp : Array String) (a : MpInt) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  At ra [(1, ra), (10, BitVec.ofNat 64 (isReduce2kL a))] m v.keep outp cf

def entry : BitVec 64 := 0x80001db4#64

/-- **`mp_reduce_is_2k_l` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa adp : Nat} {a : MpInt} {ra : BitVec 64},
    Pre m pa adp a ra →
    Triple (At entry (Fn.Reduce2kL.entryL ra pa) m v.keep outp) (Ret m v outp a ra)

end Tom.Machine.Api.Reduce2kL
