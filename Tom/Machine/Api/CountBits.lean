import Tom.Machine.Img
import Tom.Machine.Fn.CountBits
import Tom.Spec.Bits

/-!
# `mp_count_bits`: the standard contract

From the entry, `mp_count_bits(a)` with `a` valid returns to `ra` with `a0 =
countBits a` (`= bitLen (mag a)`, `Tom.countBits_spec`), the callee-saved
registers and all of memory unchanged (no frame, no store: the stack region
of `Api/Un.lean` is omitted, the frame is the identity).

Beyond `Valid`: `28 * used < 2^31`, so that the C's `int` result
`(used - 1) * MP_DIGIT_BIT + …` does not overflow.
-/

namespace Tom.Machine.Api.CountBits

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

/-- What `mp_count_bits(a)` needs. -/
structure Pre (m : Mem) (pa adp : Nat) (a : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  va : a.Valid
  ga : MpGeom pa adp a.alloc
  bits : Layout.digitBits * a.used < 2 ^ 31
  ra_al : ra.toNat % 4 = 0
  img : Img m

/-- Back at `ra` with the result in `a0`, memory unchanged. -/
def Ret (m : Mem) (v : Abi) (outp : Array String) (a : MpInt) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  At ra [(1, ra), (10, BitVec.ofNat 64 (countBits a))] m v.keep outp cf

def entry : BitVec 64 := 0x800050f0#64

/-- **`mp_count_bits` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa adp : Nat} {a : MpInt} {ra : BitVec 64},
    Pre m pa adp a ra →
    Triple (At entry (Fn.CountBits.entryL ra pa) m v.keep outp) (Ret m v outp a ra)

end Tom.Machine.Api.CountBits
