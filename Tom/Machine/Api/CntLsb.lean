import Tom.Machine.Img
import Tom.Machine.Fn.CntLsb
import Tom.Spec.Bits

/-!
# `mp_cnt_lsb`: the standard contract

From the entry, `mp_cnt_lsb(a)` with `a` valid returns to `ra` with `a0 =
cntLsb a` (`0` for zero, otherwise `28 x` plus the trailing zeros of digit
`x`, the lowest nonzero one, by the C's `lnz` nibble table in `.rodata`),
the callee-saved registers and all of memory unchanged (no frame, no store:
no stack region).

Beyond `Valid`: `28 * used < 2^31` (the C's `int` count).
-/

namespace Tom.Machine.Api.CntLsb

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

structure Pre (m : Mem) (pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  ga : MpGeom pa adp a.alloc
  bits : Layout.digitBits * a.used < 2 ^ 31
  ra_al : ra.toNat % 4 = 0
  img : Img m

def Ret (m : Mem) (v : Abi) (outp : Array String) (a : MpInt) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  At ra [(1, ra), (10, BitVec.ofNat 64 (cntLsb a))] m v.keep outp cf

def entry : BitVec 64 := 0x80005054#64

/-- **`mp_cnt_lsb` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa adp : Nat} {a : MpInt} {ra : BitVec 64},
    Pre m pa adp a ra →
    Triple (At entry (Fn.CntLsb.entryL ra pa) m v.keep outp) (Ret m v outp a ra)

end Tom.Machine.Api.CntLsb
