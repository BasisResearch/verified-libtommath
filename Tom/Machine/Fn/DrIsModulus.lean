import Tom.Machine.Seg.DrIsModulus
import Tom.Machine.Repr
import Tom.Machine.Kit.Leaf
import Tom.Machine.Code
import Tom.Machine.Kit.Word
import Vsa.Sim.TripleCat

/-!
# `mp_dr_is_modulus` on the machine: the segments

`mp_dr_is_modulus(a)` at `0x80005594` (20 instructions, no frame, no store):
```
5594 lw a3,0(a0); li a5,1; bge a5,a3,55dc               -- used < 2: MP_NO
55a0 ld a5,16(a0); addiw a3,a3,-2; slli a4,a3,32; srli a3,a4,30
55b0 lui a2,0x10000; addi a4,a5,8; add a3,a3,a4         -- a3 = dp + 4 used
55bc addi a5,a5,4; addi a2,a2,-1                        -- a5 = dp + 4, a2 = MP_MASK
55c4 lw a4,0(a5); addi a5,a5,4; bne a4,a2,55dc          -- loop head
55d0 bne a5,a3,55c4
55d4 li a0,1; ret
55dc li a0,0; ret
```
At the loop head at index `i`, `a5 = dp + 4 i`.
-/


namespace Tom.Machine.Fn.DrIsModulus

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "drm_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpDrIsModulusBase = 0x80005594 := rfl
   have : mpDrIsModulusCode.length = 20 := rfl))

def entryL (ra : BitVec 64) (pa : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 pa)]

def retL (ra r : BitVec 64) : GRegs := [(1, ra), (10, r)]

/-- Registers at the loop head at index `i`. -/
def headL (ra : BitVec 64) (adp u i : Nat) : GRegs :=
  [(1, ra), (12, BitVec.ofNat 64 268435455), (13, BitVec.ofNat 64 (adp + 4 * u)),
   (15, BitVec.ofNat 64 (adp + 4 * i))]

/-- Digit `i`'s load. -/
structure DFacts (m : Mem) (adp u i d : Nat) : Prop where
  rd : Ram (adp + 4 * i) 4
  arr : adp + 4 * u ≤ 0x100000000
  d_v : bytesT4 m (adp + 4 * i) = BitVec.ofNat 32 d
  d_lt : d < 2 ^ 31
  i_lt : i < u

theorem DFacts.sx {m : Mem} {adp u i d : Nat} (h : DFacts m adp u i d) :
    BitVec.signExtend 64 (bytesT4 m (adp + 4 * i)) = BitVec.ofNat 64 d := by
  rw [h.d_v, signExtend_ofNat32 _ h.d_lt]

section
variable (ra : BitVec 64) (v : Abi) (outp : Array String) (m : Mem)
  (hc : CodeAt m mpDrIsModulusBase mpDrIsModulusCode)
include hc

theorem small_step (pa u : Nat) (hra : ra.toNat % 4 = 0) (hf : UFacts m pa u) (hu : u < 2) :
    Triple (At 0x80005594#64 (entryL ra pa) m v.keep outp) (At ra (retL ra 0#64) (writeLog m []) v.keep outp) := by
  drm_ctx
  have h1 := hf.sx
  seg_step dmSmall ra [rd4 m pa] [1, 10] abiKeys [entryL] [retL] [h1] hc

theorem enter_step (pa adp u : Nat) (hf : UFacts m pa u) (hu : 2 ≤ u)
    (hdp : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp) (hadp : adp + 4 * u ≤ 0x100000000) :
    Triple (At 0x80005594#64 (entryL ra pa) m v.keep outp) (At 0x800055c4#64 (headL ra adp u 1) (writeLog m []) v.keep outp) := by
  drm_ctx
  have h1 := hf.sx
  seg_step dmEnter 0x800055c4#64 [rd4 m pa, rd8 m (pa + 16)] [1, 10] abiKeys [entryL] [headL] [h1, hdp] hc

theorem no_step (adp u i d : Nat) (hra : ra.toNat % 4 = 0) (hf : DFacts m adp u i d) (hd : d ≠ 268435455) :
    Triple (At 0x800055c4#64 (headL ra adp u i) m v.keep outp) (At ra (retL ra 0#64) (writeLog m []) v.keep outp) := by
  drm_ctx
  have h1 := hf.sx
  seg_step dmNo ra [rd4 m (adp + 4 * i)] [1, 12, 13, 15] abiKeys [headL] [retL] [h1] hc

theorem next_step (adp u i d : Nat) (hf : DFacts m adp u i d) (hd : d = 268435455) (hi : i + 1 < u) :
    Triple (At 0x800055c4#64 (headL ra adp u i) m v.keep outp)
      (At 0x800055c4#64 (headL ra adp u (i + 1)) (writeLog m []) v.keep outp) := by
  drm_ctx
  have h1 := hf.sx
  seg_step dmNext 0x800055c4#64 [rd4 m (adp + 4 * i)] [1, 12, 13, 15] abiKeys [headL] [headL] [h1] hc

theorem yes_step (adp u i d : Nat) (hra : ra.toNat % 4 = 0) (hf : DFacts m adp u i d) (hd : d = 268435455)
    (hi : i + 1 = u) :
    Triple (At 0x800055c4#64 (headL ra adp u i) m v.keep outp) (At ra (retL ra 1#64) (writeLog m []) v.keep outp) := by
  drm_ctx
  have h1 := hf.sx
  seg_step dmYes ra [rd4 m (adp + 4 * i)] [1, 12, 13, 15] abiKeys [headL] [retL] [h1] hc

end

end Tom.Machine.Fn.DrIsModulus
