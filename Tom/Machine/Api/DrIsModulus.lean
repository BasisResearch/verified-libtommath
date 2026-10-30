import Tom.Machine.Img
import Tom.Machine.Fn.DrIsModulus
import Tom.Spec.ModShape

/-!
# `mp_dr_is_modulus`: the standard contract

From the entry, `mp_dr_is_modulus(a)` with `a` shaped returns to `ra` with
`a0 = MP_YES` (`1`) iff `IsDrModulus a` (at least two digits, all but the
lowest `MP_MASK`), `MP_NO` (`0`) otherwise; the callee-saved registers and
all of memory unchanged (no frame, no store: no stack region).
-/

namespace Tom.Machine.Api.DrIsModulus

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

/-- What `mp_dr_is_modulus(a)` needs. -/
structure Pre (m : Mem) (pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  sa : a.Shape
  ga : MpGeom pa adp a.alloc
  ra_al : ra.toNat % 4 = 0
  img : Img m

def Ret (m : Mem) (v : Abi) (outp : Array String) (a : MpInt) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  At ra [(1, ra), (10, BitVec.ofNat 64 (if IsDrModulus a then 1 else 0))] m v.keep outp cf

def entry : BitVec 64 := 0x80005594#64

/-- **`mp_dr_is_modulus` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa adp : Nat} {a : MpInt} {ra : BitVec 64},
    Pre m pa adp a ra →
    Triple (At entry (Fn.DrIsModulus.entryL ra pa) m v.keep outp) (Ret m v outp a ra)

end Tom.Machine.Api.DrIsModulus
