import Tom.Machine.Seg.CntLsb
import Tom.Machine.Repr
import Tom.Machine.Kit.Leaf
import Tom.Machine.Code
import Tom.Machine.Kit.Word
import Tom.Machine.Kit.Bits
import Tom.Machine.Kit.Ro
import Vsa.Sim.TripleCat

/-!
# `mp_cnt_lsb` on the machine: the segments

`mp_cnt_lsb(a)` at `0x80005054` (39 instructions, no frame, no store):
```
5054 lw a4,0(a0); beqz a4,50c0                          -- zero: 0
505c ld a1,16(a0); li a2,0; mv a3,a1; bgtz a4,5078
5070 addiw a2,a2,1; beq a4,a2,50c8                      -- x++ (x == used: not for valid a)
5078 lw a5,0(a3); addi a3,a3,4; beqz a5,5070            -- digit loop head: a3 = dp + 4x
5084 slliw a4,a2,3; subw a4,a4,a2; slliw a4,a4,2        -- r = 28 x
5090 andi a3,a5,1; bnez a3,50c0                         -- q odd: r
5098 auipc a1,0x13; addi a1,a1,-1048                    -- a1 = lnz (.rodata)
50a0 andi a3,a5,15; slli a3,a3,2; add a3,a1,a3; lw a2,0(a3)   -- nibble loop head
     andi a3,a5,15; srliw a5,a5,4; addw a4,a2,a4; beqz a3,50a0
50c0 mv a0,a4; ret
```
-/


namespace Tom.Machine.Fn.CntLsb

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "lz_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpCntLsbBase = 0x80005054 := rfl
   have : mpCntLsbCode.length = 39 := rfl))

def entryL (ra : BitVec 64) (pa : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 pa)]

def retL (ra r : BitVec 64) : GRegs := [(1, ra), (10, r)]

/-- The digit loop head at index `x`. -/
def headL (ra : BitVec 64) (adp u x : Nat) : GRegs :=
  [(1, ra), (11, BitVec.ofNat 64 adp), (12, BitVec.ofNat 64 x), (13, BitVec.ofNat 64 (adp + 4 * x)),
   (14, BitVec.ofNat 64 u)]

/-- At `5090`: `q` the digit, `r` the count so far. -/
def joinL (ra : BitVec 64) (r q : Nat) : GRegs := [(1, ra), (14, BitVec.ofNat 64 r), (15, BitVec.ofNat 64 q)]

/-- The nibble loop head. -/
def innerL (ra : BitVec 64) (r q : Nat) : GRegs :=
  [(1, ra), (11, BitVec.ofNat 64 0x80017c80), (14, BitVec.ofNat 64 r), (15, BitVec.ofNat 64 q)]

/-- `andi rd, rs, 1`. -/
theorem and1_ofNat (x : Nat) : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  rw [show (1 : Nat) % 2 ^ 64 = 2 ^ 1 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `slli a3,a3,2`. -/
theorem shl2 (x : Nat) : Sail.shift_bits_left (BitVec.ofNat 64 x) (2#6) = BitVec.ofNat 64 (4 * x) := by
  rw [shl_ofNatW' x 2 4 (by decide) (by decide), Nat.mul_comm]

/-- `addw a4,a2,a4` with `a2` a sign-extended small load. -/
theorem addw_small (X : BitVec 32) (n r : Nat) (hX : BitVec.signExtend 64 X = BitVec.ofNat 64 n)
    (hn : n ≤ 4) (hr : r + 4 < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.signExtend 64 X) + BitVec.ofNat 32 (r % 4294967296)) =
      BitVec.ofNat 64 (r + n) := by
  rw [hX, extractLsb_ofNatW _ (by omega), Nat.mod_eq_of_lt (show r < 4294967296 by omega)]
  rw [show BitVec.ofNat (31 - 0 + 1) n + BitVec.ofNat 32 r = BitVec.ofNat 32 (n + r) from ofNat_add_ofNatW n r,
    sext_ofNatW (by decide) _ (by omega), Nat.add_comm]

structure DFacts (m : Mem) (adp u x d : Nat) : Prop where
  rd : Ram (adp + 4 * x) 4
  arr : adp + 4 * u ≤ 0x100000000
  d_v : bytesT4 m (adp + 4 * x) = BitVec.ofNat 32 d
  d_lt : d < 2 ^ 31
  x_lt : x < u
  r_lt : 28 * u < 2 ^ 31

theorem DFacts.sx {m : Mem} {adp u x d : Nat} (h : DFacts m adp u x d) :
    BitVec.signExtend 64 (bytesT4 m (adp + 4 * x)) = BitVec.ofNat 64 d := by
  rw [h.d_v, signExtend_ofNat32 _ h.d_lt]

/-- `lnz[q & 15]`'s load. -/
structure LFacts (m : Mem) (q r : Nat) : Prop where
  l_v : bytesT4 m (0x80017c80 + 4 * (q % 16)) = BitVec.ofNat 32 (lnzTab (q % 16))
  l_le : lnzTab (q % 16) ≤ 4
  q_lt : q < 2 ^ 31
  r_lt : r + 4 < 2 ^ 31

theorem LFacts.sx {m : Mem} {q r : Nat} (h : LFacts m q r) :
    BitVec.signExtend 64 (bytesT4 m (0x80017c80 + 4 * (q % 16))) = BitVec.ofNat 64 (lnzTab (q % 16)) := by
  rw [h.l_v, signExtend_ofNat32 _ (by have := h.l_le; omega)]

section
variable (ra : BitVec 64) (v : Abi) (outp : Array String) (m : Mem)
  (hc : CodeAt m mpCntLsbBase mpCntLsbCode)
include hc

theorem zero_step (pa : Nat) (hra : ra.toNat % 4 = 0) (hf : UFacts m pa 0) :
    Triple (At 0x80005054#64 (entryL ra pa) m v.keep outp) (At ra (retL ra (BitVec.ofNat 64 0)) (writeLog m []) v.keep outp) := by
  lz_ctx
  have h1 := hf.sx
  seg_step lzZero ra [rd4 m pa] [1, 10] abiKeys [entryL] [retL] [h1] hc

theorem enter_step (pa adp u : Nat) (hf : UFacts m pa u) (hu : 1 ≤ u)
    (hdp : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp) :
    Triple (At 0x80005054#64 (entryL ra pa) m v.keep outp) (At 0x80005078#64 (headL ra adp u 0) (writeLog m []) v.keep outp) := by
  lz_ctx
  have h1 := hf.sx
  seg_step lzEnter 0x80005078#64 [rd4 m pa, rd8 m (pa + 16)] [1, 10] abiKeys [entryL] [headL] [h1, hdp] hc

theorem skip_step (adp u x : Nat) (hf : DFacts m adp u x 0) (hx : x + 1 ≠ u) :
    Triple (At 0x80005078#64 (headL ra adp u x) m v.keep outp)
      (At 0x80005078#64 (headL ra adp u (x + 1)) (writeLog m []) v.keep outp) := by
  lz_ctx
  have h1 := hf.sx
  seg_step lzSkip 0x80005078#64 [rd4 m (adp + 4 * x)] [1, 11, 12, 13, 14] abiKeys [headL] [headL] [h1] hc

theorem found_step (adp u x d : Nat) (hf : DFacts m adp u x d) (hd : d ≠ 0) :
    Triple (At 0x80005078#64 (headL ra adp u x) m v.keep outp)
      (At 0x80005090#64 (joinL ra (28 * x) d) (writeLog m []) v.keep outp) := by
  lz_ctx
  have h1 := hf.sx
  seg_stepw lzFound 0x80005090#64 [rd4 m (adp + 4 * x)] [1, 11, 12, 13, 14] abiKeys [headL] [joinL] [h1] hc using
    (refine ⟨?_, ?_⟩
     · rw [Nat.mod_eq_of_lt (show x < 4294967296 by omega)]; exact mul28W _ (by omega)
     · exact True.intro)

theorem odd_step (hra : ra.toNat % 4 = 0) (r q : Nat) (hq : q % 2 = 1) :
    Triple (At 0x80005090#64 (joinL ra r q) m v.keep outp)
      (At ra (retL ra (BitVec.ofNat 64 r)) (writeLog m []) v.keep outp) := by
  lz_ctx
  seg_step lzOdd ra ([] : List (List (BitVec 8))) [1, 14, 15] abiKeys [joinL] [retL] [and1_ofNat] hc

theorem even_step (r q : Nat) (hq : q % 2 = 0) :
    Triple (At 0x80005090#64 (joinL ra r q) m v.keep outp)
      (At 0x800050a0#64 (innerL ra r q) (writeLog m []) v.keep outp) := by
  lz_ctx
  seg_step lzEven 0x800050a0#64 ([] : List (List (BitVec 8))) [1, 14, 15] abiKeys [joinL] [innerL] [and1_ofNat] hc

theorem in_step (r q : Nat) (hf : LFacts m q r) (hq : q % 16 = 0) :
    Triple (At 0x800050a0#64 (innerL ra r q) m v.keep outp)
      (At 0x800050a0#64 (innerL ra (r + lnzTab (q % 16)) (q / 16)) (writeLog m []) v.keep outp) := by
  lz_ctx
  have h1 := hf.sx
  have h2 := shl2 (q % 16)
  seg_stepw lzIn 0x800050a0#64 [rd4 m (0x80017c80 + 4 * (q % 16))] [1, 11, 14, 15] abiKeys [innerL] [innerL]
    [h1, h2, and15_ofNat, Vsa.Sim.shamtOf, BitVec.reduceExtractLsb', BitVec.reduceExtractLsb] hc using
    (refine ⟨addw_small _ _ _ h1 hf.l_le hf.r_lt, ?_⟩
     congr 1; omega)

theorem out_step (hra : ra.toNat % 4 = 0) (r q : Nat) (hf : LFacts m q r) (hq : q % 16 ≠ 0) :
    Triple (At 0x800050a0#64 (innerL ra r q) m v.keep outp)
      (At ra (retL ra (BitVec.ofNat 64 (r + lnzTab (q % 16)))) (writeLog m []) v.keep outp) := by
  lz_ctx
  have h1 := hf.sx
  have h2 := shl2 (q % 16)
  seg_stepw lzOut ra [rd4 m (0x80017c80 + 4 * (q % 16))] [1, 11, 14, 15] abiKeys [innerL] [retL]
    [h1, h2, and15_ofNat, Vsa.Sim.shamtOf, BitVec.reduceExtractLsb', BitVec.reduceExtractLsb] hc using
    (exact addw_small _ _ _ h1 hf.l_le hf.r_lt)

end

end Tom.Machine.Fn.CntLsb
