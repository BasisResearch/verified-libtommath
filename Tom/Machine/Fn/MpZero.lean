import Tom.Machine.Seg.MpZero
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Fn.Memset

/-!
# `mp_zero` on the machine: the segments

`mp_zero(a)` at `0x80002178` (9 instructions):
```
2178 lw a2,4(a0); sw zero,8(a0); sw zero,0(a0)   -- sign := MP_ZPOS, used := 0
2184 blez a2,2198                                -- alloc = 0: return
2188 ld a0,16(a0); slli a2,a2,2; li a1,0; j memset   -- memset(dp, 0, 4 alloc)
2198 ret
```
`mzeroE` is the `alloc = 0` path, `mzeroM` the tail jump into `memset`.
-/


namespace Tom.Machine.Fn.MpZero

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "mzero_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpZeroBase = 0x80002178 := rfl
   have : mpZeroCode.length = 9 := rfl))

def entry : BitVec 64 := 0x80002178#64

/-- The arguments: `a0 = a`. -/
def entryL (ra : BitVec 64) (p : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 p)]

/-- The stores: `sign := 0`, `used := 0`. -/
def zlog (p : Nat) : List WEntry := [(p + 8, 4, 0#64), (p, 4, 0#64)]

/-- The struct: `alloc` and the digit pointer, the struct off the code. -/
structure SFacts (m : Mem) (p dp al : Nat) : Prop where
  rp : Ram p 24
  p_al : p % 8 = 0
  al_v : bytesT4 m (p + 4) = BitVec.ofNat 32 al
  dp_v : bytesT8 m (p + 16) = BitVec.ofNat 64 dp
  al_lt : al < 2 ^ 31
  code_off : p + 24 ≤ mpZeroBase ∨ mpZeroBase + 36 ≤ p

theorem SFacts.sx {m : Mem} {p dp al : Nat} (h : SFacts m p dp al) :
    BitVec.signExtend 64 (bytesT4 m (p + 4)) = BitVec.ofNat 64 al := by
  rw [h.al_v, signExtend_ofNat32 _ h.al_lt]

/-- `alloc = 0`: the stores, return. -/
theorem e_step (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp : Nat) (m : Mem)
    (hc : CodeAt m mpZeroBase mpZeroCode) (hf : SFacts m p dp 0) (hra : ra.toNat % 4 = 0) :
    Triple (At entry (entryL ra p) m v.keep outp) (At ra [(1, ra)] (writeLog m (zlog p)) v.keep outp) := by
  mzero_ctx
  have hsx := hf.sx
  seg_step mzeroE ra [rd4 m (p + 4)] [1, 10] abiKeys [entry, entryL, zlog] [] [hsx] hc

/-- `alloc > 0`: the stores, tail-jump to `memset(dp, 0, 4 alloc)`. -/
theorem m_step (ra : BitVec 64) (v : Abi) (outp : Array String) (p dp al : Nat) (m : Mem)
    (hc : CodeAt m mpZeroBase mpZeroCode) (hf : SFacts m p dp al) (hal : 0 < al) :
    Triple (At entry (entryL ra p) m v.keep outp)
      (At Memset.entry (Memset.entryL ra dp 0#64 (4 * al)) (writeLog m (zlog p)) v.keep outp) := by
  mzero_ctx
  have hsx := hf.sx
  seg_step mzeroM Memset.entry [rd4 m (p + 4), rd8 m (p + 16)] [1, 10] abiKeys [entry, entryL, zlog]
    [Memset.entryL]
    [hsx, hf.dp_v] hc

end Tom.Machine.Fn.MpZero
