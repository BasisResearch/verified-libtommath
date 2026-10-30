import Tom.Machine.Seg.DrSetup
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Word
import Vsa.Sim.TripleCat

/-!
# `mp_dr_setup` on the machine: the segment

`mp_dr_setup(a, d)` at `0x8000578c` (6 instructions, no frame):
```
578c ld a4,16(a0); lui a5,0x10000; lw a4,0(a4); subw a5,a5,a4; sw a5,0(a1); ret
```
`*d = 2^28 - dp[0]`.
-/

namespace Tom.Machine.Fn.DrSetup

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "drs_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpDrSetupBase = 0x8000578c := rfl
   have : mpDrSetupCode.length = 6 := rfl))

/-- Registers at the entry. -/
def entryL (ra : BitVec 64) (pa pd : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pd)]

/-- The loads and the store's slot. -/
structure Facts (m : Mem) (pa adp pd d0 : Nat) : Prop where
  rs : Ram pa 24
  rd : Ram adp 4
  rw_ : Ram pd 4
  dp_v : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp
  d_v : bytesT4 m adp = BitVec.ofNat 32 d0
  d_le : d0 ≤ 2 ^ 28
  pd_al : pd % 4 = 0
  pd_code : pd + 4 ≤ mpDrSetupBase ∨ mpDrSetupBase + 24 ≤ pd

theorem step (ra : BitVec 64) (v : Abi) (outp : Array String) (pa adp pd d0 : Nat) (m : Mem)
    (hc : CodeAt m mpDrSetupBase mpDrSetupCode) (hra : ra.toNat % 4 = 0) (hf : Facts m pa adp pd d0) :
    Triple (At 0x8000578c#64 (entryL ra pa pd) m v.keep outp)
      (At ra [(1, ra)] (writeLog m [(pd, 4, BitVec.ofNat 64 (2 ^ 28 - d0))]) v.keep outp) := by
  drs_ctx
  have h1 : BitVec.signExtend 64 (bytesT4 m adp) = BitVec.ofNat 64 d0 := by
    rw [hf.d_v, signExtend_ofNat32 _ (by omega)]
  have h2 := hf.dp_v
  seg_step drs ra [rd8 m (pa + 16), rd4 m adp] [1, 10, 11] abiKeys [entryL] [] [h1, h2] hc

end Tom.Machine.Fn.DrSetup
