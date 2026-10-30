import Tom.Machine.Seg.CmpS
import Tom.Machine.Fn.MpSub

/-!
# `mp_cmp` on the machine: the segments

`mp_cmp(a, b)` at `0x800006ec` (15 instructions, no frame, no store):
```
6ec lw a5,8(a0); lw a4,8(a1); mv a3,a1; beq a4,a5,708   -- signs equal?
6fc li a0,1; beq a5,a0,720; ret                         -- a negative: MP_LT, else MP_GT
708 li a5,1; beq a4,a5,714; j mp_cmp_mag                -- both nonnegative: mp_cmp_mag(a, b)
714 mv a1,a0; mv a0,a3; j mp_cmp_mag                    -- both negative: mp_cmp_mag(b, a)
720 li a0,-1; ret
```
The sign loads are `MpSub.SFacts`.
-/


namespace Tom.Machine.Fn.CmpS

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg
open Tom.Machine.Fn.MpSub (SFacts)

macro "cmps_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpCmpBase = 0x800006ec := rfl
   have : mpCmpCode.length = 15 := rfl))

/-- Registers at the entry, and at the tail jumps to `mp_cmp_mag`. -/
def entryL (ra : BitVec 64) (pa pb : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)]

/-- Registers at the return with result `r`. -/
def retL (ra r : BitVec 64) : GRegs := [(1, ra), (10, r)]

abbrev neg1 : BitVec 64 := 0xffffffffffffffff#64

section
variable (ra : BitVec 64) (v : Abi) (outp : Array String) (pa pb sa sb : Nat) (m : Mem)
  (hc : CodeAt m mpCmpBase mpCmpCode) (hf : SFacts m pa pb sa sb)
include hc hf

/-- Different signs, `a` negative: `MP_LT`. -/
theorem lt_step (hra : ra.toNat % 4 = 0) (hne : sa ≠ sb) (hs : sa = 1) :
    Triple (At 0x800006ec#64 (entryL ra pa pb) m v.keep outp) (At ra (retL ra neg1) (writeLog m []) v.keep outp) := by
  cmps_ctx
  have ⟨h1, h2⟩ := hf.sx
  seg_step csLT ra [rd4 m (pa + 8), rd4 m (pb + 8)] [1, 10, 11] abiKeys [entryL] [retL] [h1, h2] hc

/-- Different signs, `a` not negative: `MP_GT`. -/
theorem gt_step (hra : ra.toNat % 4 = 0) (hne : sa ≠ sb) (hs : sa ≠ 1) :
    Triple (At 0x800006ec#64 (entryL ra pa pb) m v.keep outp) (At ra (retL ra 1#64) (writeLog m []) v.keep outp) := by
  cmps_ctx
  have ⟨h1, h2⟩ := hf.sx
  seg_step csGT ra [rd4 m (pa + 8), rd4 m (pb + 8)] [1, 10, 11] abiKeys [entryL] [retL] [h1, h2] hc

/-- Equal signs, not negative: tail-jump to `mp_cmp_mag(a, b)`. -/
theorem pos_step (he : sa = sb) (hs : sb ≠ 1) :
    Triple (At 0x800006ec#64 (entryL ra pa pb) m v.keep outp)
      (At 0x80000764#64 (entryL ra pa pb) (writeLog m []) v.keep outp) := by
  cmps_ctx
  have ⟨h1, h2⟩ := hf.sx
  seg_step csPos 0x80000764#64 [rd4 m (pa + 8), rd4 m (pb + 8)] [1, 10, 11] abiKeys [entryL] [entryL] [h1, h2] hc

/-- Equal signs, negative: tail-jump to `mp_cmp_mag(b, a)`. -/
theorem neg_step (he : sa = sb) (hs : sb = 1) :
    Triple (At 0x800006ec#64 (entryL ra pa pb) m v.keep outp)
      (At 0x80000764#64 (entryL ra pb pa) (writeLog m []) v.keep outp) := by
  cmps_ctx
  have ⟨h1, h2⟩ := hf.sx
  seg_step csNeg 0x80000764#64 [rd4 m (pa + 8), rd4 m (pb + 8)] [1, 10, 11] abiKeys [entryL] [entryL] [h1, h2] hc

end

end Tom.Machine.Fn.CmpS
