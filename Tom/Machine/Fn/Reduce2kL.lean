import Tom.Machine.Seg.Reduce2kL
import Tom.Machine.Repr
import Tom.Machine.Kit.Leaf
import Tom.Machine.Code
import Tom.Machine.Kit.Word
import Tom.Machine.Kit.Alu1
import Vsa.Sim.TripleCat

/-!
# `mp_reduce_is_2k_l` on the machine: the segments

`mp_reduce_is_2k_l(a)` at `0x80001db4` (26 instructions, no frame, no store):
```
1db4 lw a4,0(a0); beqz a4,1dfc                          -- used == 0: MP_NO
1dbc li a5,1; beq a4,a5,1dfc                            -- used == 1: MP_YES
1dc4 bge a5,a4,1e10                                     -- (used < 0)
1dc8 ld a5,16(a0); slli a2,a4,2; lui a1,0x10000; add a2,a2,a5; addi a1,a1,-1; li a0,0
1de0 lw a3,0(a5); addi a5,a5,4; beq a3,a1,1e04          -- loop head: a5 = dp + 4i, a0 = count
1dec bne a5,a2,1de0
1df0 sraiw a4,a4,1; slt a4,a0,a4; seqz a4,a4            -- !(count < used / 2)
1dfc mv a0,a4; ret
1e04 addiw a0,a0,1; bne a5,a2,1de0; j 1df0
```
The `seqz` at `1df8` is one step (`seqz_at`).
-/


namespace Tom.Machine.Fn.Reduce2kL

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "r2kl_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpReduceIs2kLBase = 0x80001db4 := rfl
   have : mpReduceIs2kLCode.length = 26 := rfl))

def entryL (ra : BitVec 64) (pa : Nat) : GRegs := [(1, ra), (10, BitVec.ofNat 64 pa)]

def retL (ra r : BitVec 64) : GRegs := [(1, ra), (10, r)]

/-- Registers at the loop head at index `i` with count `c`. -/
def headL (ra : BitVec 64) (adp u i c : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 c), (11, BitVec.ofNat 64 268435455), (12, BitVec.ofNat 64 (adp + 4 * u)),
   (14, BitVec.ofNat 64 u), (15, BitVec.ofNat 64 (adp + 4 * i))]

/-- Registers with `a4 = x` (at the `seqz`, and at the final `mv`). -/
def a4L (ra x : BitVec 64) : GRegs := [(1, ra), (14, x)]

structure DFacts (m : Mem) (adp u i d c : Nat) : Prop where
  rd : Ram (adp + 4 * i) 4
  arr : adp + 4 * u ≤ 0x100000000
  d_v : bytesT4 m (adp + 4 * i) = BitVec.ofNat 32 d
  d_lt : d < 2 ^ 31
  i_lt : i < u
  u_lt : u < 2 ^ 31
  c_le : c ≤ i

theorem DFacts.sx {m : Mem} {adp u i d c : Nat} (h : DFacts m adp u i d c) :
    BitVec.signExtend 64 (bytesT4 m (adp + 4 * i)) = BitVec.ofNat 64 d := by
  rw [h.d_v, signExtend_ofNat32 _ h.d_lt]

section
variable (ra : BitVec 64) (v : Abi) (outp : Array String) (m : Mem)
  (hc : CodeAt m mpReduceIs2kLBase mpReduceIs2kLCode)
include hc

theorem zero_step (pa : Nat) (hra : ra.toNat % 4 = 0) (hf : UFacts m pa 0) :
    Triple (At 0x80001db4#64 (entryL ra pa) m v.keep outp) (At ra (retL ra 0#64) (writeLog m []) v.keep outp) := by
  r2kl_ctx
  have h1 := hf.sx
  seg_step kZero ra [rd4 m pa] [1, 10] abiKeys [entryL] [retL] [h1] hc

theorem one_step (pa : Nat) (hra : ra.toNat % 4 = 0) (hf : UFacts m pa 1) :
    Triple (At 0x80001db4#64 (entryL ra pa) m v.keep outp) (At ra (retL ra 1#64) (writeLog m []) v.keep outp) := by
  r2kl_ctx
  have h1 := hf.sx
  seg_step kOne ra [rd4 m pa] [1, 10] abiKeys [entryL] [retL] [h1] hc

theorem enter_step (pa adp u : Nat) (hf : UFacts m pa u) (hu : 2 ≤ u)
    (hdp : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp) :
    Triple (At 0x80001db4#64 (entryL ra pa) m v.keep outp)
      (At 0x80001de0#64 (headL ra adp u 0 0) (writeLog m []) v.keep outp) := by
  r2kl_ctx
  have h1 := hf.sx
  seg_step kEnter 0x80001de0#64 [rd4 m pa, rd8 m (pa + 16)] [1, 10] abiKeys [entryL] [headL] [h1, hdp] hc

theorem neNext_step (adp u i d c : Nat) (hf : DFacts m adp u i d c) (hd : d ≠ 268435455) (hi : i + 1 < u) :
    Triple (At 0x80001de0#64 (headL ra adp u i c) m v.keep outp)
      (At 0x80001de0#64 (headL ra adp u (i + 1) c) (writeLog m []) v.keep outp) := by
  r2kl_ctx
  have h1 := hf.sx
  seg_step kNeNext 0x80001de0#64 [rd4 m (adp + 4 * i)] [1, 10, 11, 12, 14, 15] abiKeys [headL] [headL] [h1] hc

theorem eqNext_step (adp u i d c : Nat) (hf : DFacts m adp u i d c) (hd : d = 268435455) (hi : i + 1 < u) :
    Triple (At 0x80001de0#64 (headL ra adp u i c) m v.keep outp)
      (At 0x80001de0#64 (headL ra adp u (i + 1) (c + 1)) (writeLog m []) v.keep outp) := by
  r2kl_ctx
  have h1 := hf.sx
  seg_step kEqNext 0x80001de0#64 [rd4 m (adp + 4 * i)] [1, 10, 11, 12, 14, 15] abiKeys [headL] [headL] [h1] hc

theorem neEnd_step (adp u i d c : Nat) (hf : DFacts m adp u i d c) (hd : d ≠ 268435455) (hi : i + 1 = u) :
    Triple (At 0x80001de0#64 (headL ra adp u i c) m v.keep outp)
      (At 0x80001df8#64 (a4L ra (BitVec.ofNat 64 (if c < u / 2 then 1 else 0))) (writeLog m []) v.keep outp) := by
  r2kl_ctx
  have h1 := hf.sx
  seg_stepw kNeEnd 0x80001df8#64 [rd4 m (adp + 4 * i)] [1, 10, 11, 12, 14, 15] abiKeys [headL] [a4L] [h1] hc using
    (first | exact slt_half _ _ (by omega) (by omega) | exact ⟨slt_half _ _ (by omega) (by omega), True.intro⟩)

theorem eqEnd_step (adp u i d c : Nat) (hf : DFacts m adp u i d c) (hd : d = 268435455) (hi : i + 1 = u) :
    Triple (At 0x80001de0#64 (headL ra adp u i c) m v.keep outp)
      (At 0x80001df8#64 (a4L ra (BitVec.ofNat 64 (if c + 1 < u / 2 then 1 else 0))) (writeLog m []) v.keep outp) := by
  r2kl_ctx
  have h1 := hf.sx
  seg_stepw kEqEnd 0x80001df8#64 [rd4 m (adp + 4 * i)] [1, 10, 11, 12, 14, 15] abiKeys [headL] [a4L] [h1] hc using
    (rw [show (c + 1) % 4294967296 % 4294967296 = c + 1 by omega]
     exact slt_half _ _ (by omega) (by omega))

theorem ret_step (hra : ra.toNat % 4 = 0) (x : BitVec 64) :
    Triple (At 0x80001dfc#64 (a4L ra x) m v.keep outp) (At ra (retL ra x) (writeLog m []) v.keep outp) := by
  r2kl_ctx
  seg_step kRet ra ([] : List (List (BitVec 8))) [1, 14] abiKeys [a4L] [retL] [] hc

/-- The `seqz a4,a4` at `1df8`. -/
theorem seqz_step (t : Nat) (ht : t < 2) :
    Triple (At 0x80001df8#64 (a4L ra (BitVec.ofNat 64 t)) m v.keep outp)
      (At 0x80001dfc#64 (a4L ra (BitVec.ofNat 64 (if t = 0 then 1 else 0))) m v.keep outp) := by
  have h := seqz_at (pc := 0x80001df8#64) (w := 0x00173713#32) (rd := 14) (rs1 := 14)
    (L := a4L ra (BitVec.ofNat 64 t)) (keep := v.keep) (outp := outp)
    (hc.word (a := (0x80001df8#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
    (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩
    (by decide) (Or.inr (by simp [keysG, a4L])) (by decide) (by simp [keysG, a4L])
    (by simp [Abi.keep, keysG, sKeepL]) (by simp [Abi.keep, keysG, sKeepL])
  have hpc : Sail.BitVec.addInt (0x80001df8#64 : BitVec 64) 4 = 0x80001dfc#64 := by decide
  rw [hpc, show srcVal 14 (a4L ra (BitVec.ofNat 64 t)) = BitVec.ofNat 64 t from by simp [srcVal, lookupG, a4L],
    ite_ofNat_eq_zero (by omega)] at h
  exact Triple.rmap (fun cf h' => h'.reshape (by simp [a4L, eraseG]) (fun p hp => by simp [hp])) h

end

end Tom.Machine.Fn.Reduce2kL
