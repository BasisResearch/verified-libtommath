import Tom.Machine.Seg.CountBits
import Tom.Machine.Repr
import Tom.Machine.Kit.Leaf
import Tom.Machine.Code
import Tom.Machine.Kit.Word
import Vsa.Sim.TripleCat

/-!
# `mp_count_bits` on the machine: the segments

`mp_count_bits(a)` at `0x800050f0` (17 instructions, no frame, no store):
```
50f0 lw a5,0(a0); beqz a5,512c                       -- zero: 0
50f8 ld a3,16(a0); slli a2,a5,2; addiw a4,a5,-1; add a5,a3,a2
5108 lw a5,-4(a5)                                    -- q = dp[used - 1]
510c slliw a0,a4,3; subw a0,a0,a4; slliw a0,a0,2     -- r = 28 * (used - 1)
5118 beqz a5,5130
511c srliw a5,a5,1; addiw a0,a0,1; bnez a5,511c      -- loop head
5128 ret
512c li a0,0; 5130 ret
```
At the loop head `a5 = q ≠ 0` and `a0 = r`.
-/


namespace Tom.Machine.Fn.CountBits

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "cbits_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpCountBitsBase = 0x800050f0 := rfl
   have : mpCountBitsCode.length = 17 := rfl))

/-- Registers at the entry. -/
def entryL (ra : BitVec 64) (pa : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 pa)]

/-- Registers at the return with result `r`. -/
def retL (ra r : BitVec 64) : GRegs := [(1, ra), (10, r)]

/-- Registers at the loop head. -/
def loopL (ra : BitVec 64) (q r : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 r), (15, BitVec.ofNat 64 q)]

/-- The digit pointer and the top digit. -/
structure TFacts (m : Mem) (pa adp u t : Nat) : Prop where
  rt : Ram (adp + 4 * (u - 1)) 4
  dp_v : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp
  t_v : bytesT4 m (adp + 4 * (u - 1)) = BitVec.ofNat 32 t
  t_lt : t < 2 ^ 31
  u_pos : 1 ≤ u
  r_lt : 28 * u < 2 ^ 31

theorem TFacts.sx {m : Mem} {pa adp u t : Nat} (h : TFacts m pa adp u t) :
    BitVec.signExtend 64 (bytesT4 m (adp + 4 * (u - 1))) = BitVec.ofNat 64 t := by
  rw [h.t_v, signExtend_ofNat32 _ h.t_lt]

/-- `a->used == 0`: return `0`. -/
theorem zero_step (ra : BitVec 64) (v : Abi) (outp : Array String) (pa : Nat) (m : Mem)
    (hc : CodeAt m mpCountBitsBase mpCountBitsCode) (hra : ra.toNat % 4 = 0) (hf : UFacts m pa 0) :
    Triple (At 0x800050f0#64 (entryL ra pa) m v.keep outp) (At ra (retL ra 0#64) (writeLog m []) v.keep outp) := by
  cbits_ctx
  have h1 := hf.sx
  seg_step cbZero ra [rd4 m pa] [1, 10] abiKeys [entryL] [retL] [h1] hc

/-- `a->used ≠ 0`: `q = dp[used - 1] ≠ 0`, `r = 28 (used - 1)`, to the loop head. -/
theorem enter_step (ra : BitVec 64) (v : Abi) (outp : Array String) (pa adp u t : Nat) (m : Mem)
    (hc : CodeAt m mpCountBitsBase mpCountBitsCode) (hf : UFacts m pa u) (ht : TFacts m pa adp u t)
    (ht0 : t ≠ 0) :
    Triple (At 0x800050f0#64 (entryL ra pa) m v.keep outp)
      (At 0x8000511c#64 (loopL ra t (28 * (u - 1))) (writeLog m []) v.keep outp) := by
  cbits_ctx
  have h1 := hf.sx
  have h2 := ht.sx
  have h3 := ht.dp_v
  have := ht.r_lt; have := ht.u_pos
  have hsl : Sail.shift_bits_left (BitVec.ofNat 64 u) (2#6) = BitVec.ofNat 64 (4 * u) := by
    rw [shl_ofNatW' u 2 4 (by decide) (by decide), Nat.mul_comm]
  refine Tom.Machine.seg_at' cbEnter (pc1 := 0x8000511c#64) [rd4 m pa, rd8 m (pa + 16), rd4 m (adp + 4 * (u - 1))] [1, 10] abiKeys ?_ ?_ ?_ ?_
  · tom_facts hc
    all_goals leaf_auto [entryL] [h1, h2, h3, Vsa.Sim.shamtOf, BitVec.reduceExtractLsb', BitVec.reduceExtractLsb, hsl]
  · seg_nfo [cbEnter, entryL]
  · sub_auto [cbEnter, entryL, loopL] [h1, h2, h3]
    refine ⟨?_, True.intro⟩
    rw [show (u + 18446744073709551615) % 4294967296 % 4294967296 % 4294967296 = u - 1 by omega]
    exact mul28W _ (by omega)
  · seg_nfo [cbEnter, entryL]
    try val_nf [h1, h2, h3]
    try regs_close

/-- One shift with `q / 2 ≠ 0`: back to the loop head. -/
theorem loop_step (ra : BitVec 64) (v : Abi) (outp : Array String) (q r : Nat) (m : Mem)
    (hc : CodeAt m mpCountBitsBase mpCountBitsCode) (hq : q < 2 ^ 31) (hr : r + 1 < 2 ^ 31) (h2 : q / 2 ≠ 0) :
    Triple (At 0x8000511c#64 (loopL ra q r) m v.keep outp)
      (At 0x8000511c#64 (loopL ra (q / 2) (r + 1)) (writeLog m []) v.keep outp) := by
  cbits_ctx
  have := hq
  seg_step cbLoop 0x8000511c#64 ([] : List (List (BitVec 8))) [1, 10, 15] abiKeys [loopL] [loopL] [] hc

/-- The last shift (`q / 2 = 0`): return `r + 1`. -/
theorem exit_step (ra : BitVec 64) (v : Abi) (outp : Array String) (q r : Nat) (m : Mem)
    (hc : CodeAt m mpCountBitsBase mpCountBitsCode) (hra : ra.toNat % 4 = 0) (hq : q < 2 ^ 31)
    (hr : r + 1 < 2 ^ 31) (h2 : q / 2 = 0) :
    Triple (At 0x8000511c#64 (loopL ra q r) m v.keep outp)
      (At ra (retL ra (BitVec.ofNat 64 (r + 1))) (writeLog m []) v.keep outp) := by
  cbits_ctx
  seg_step cbExit ra ([] : List (List (BitVec 8))) [1, 10, 15] abiKeys [loopL] [retL] [] hc

end Tom.Machine.Fn.CountBits
