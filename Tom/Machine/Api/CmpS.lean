import Tom.Machine.Img
import Tom.Machine.Fn.CmpS
import Tom.Spec.Cmp

/-!
# `mp_cmp`: the standard contract

From the entry, `mp_cmp(a, b)` with `a`, `b` valid returns to `ra` with
`a0` the `mp_ord` code of `cmpS a b` (`= compare (val a) (val b)`,
`Tom.cmpS_spec`), the callee-saved registers and all of memory unchanged.
Neither it nor its tail-called `mp_cmp_mag` has a frame or a store, so the
read-only regions of `Api/Two.lean` (`isR`) are not needed (the stack
region is omitted; the frame is the identity), and `a`, `b` may alias.
-/

namespace Tom.Machine.Api.CmpS

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

/-- What `mp_cmp(a, b)` needs. -/
structure Pre (m : Mem) (pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  va : a.Valid
  vb : b.Valid
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  ra_al : ra.toNat % 4 = 0
  img : Img m

/-- Back at `ra` with the result in `a0`, memory unchanged. -/
def Ret (m : Mem) (v : Abi) (outp : Array String) (a b : MpInt) (ra : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  At ra [(1, ra), (10, BitVec.ofInt 64 (ordCode (cmpS a b)))] m v.keep outp cf

def entry : BitVec 64 := 0x800006ec#64

/-- **`mp_cmp` on the machine.** -/
def Statement : Prop :=
  ∀ {m : Mem} {v : Abi} {outp : Array String} {pa adp pb bdp : Nat} {a b : MpInt} {ra : BitVec 64},
    Pre m pa adp pb bdp a b ra →
    Triple (At entry (Fn.CmpS.entryL ra pa pb) m v.keep outp) (Ret m v outp a b ra)

end Tom.Machine.Api.CmpS
