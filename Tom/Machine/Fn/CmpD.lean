import Tom.Machine.Seg.CmpD
import Tom.Machine.Repr
import Tom.Machine.Code
import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.Alu1
import Vsa.Sim.TripleCat

/-!
# `mp_cmp_d` on the machine: the segments

`mp_cmp_d(a, b)` at `0x80000728` (15 instructions, no frame, no store):
```
728 lw a3,8(a0); li a5,1; mv a4,a0; beq a3,a5,75c      -- a->sign == MP_NEG: MP_LT
738 lw a3,0(a0); mv a0,a5; blt a5,a3,760               -- a->used > 1: MP_GT
744 ld a5,16(a4); lw a5,0(a5); bltu a1,a5,760          -- dp[0] > b: MP_GT
750 sltu a5,a5,a1; negw a0,a5; ret                     -- -(dp[0] < b)
75c li a0,-1; 760 ret
```
Chains `cdNeg`, `cdGT1`, `cdGT2`, `cdLE` (to the `sltu`), `cdTail` (after it);
the `sltu` is one step by `sltu_at` (`Kit/Alu1.lean`).
-/


namespace Tom.Machine.Fn.CmpD

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg

macro "cmpd_ctx" : tactic => `(tactic|
  (facts_ctx
   have : mpCmpDBase = 0x80000728 := rfl
   have : mpCmpDCode.length = 15 := rfl))

/-- Registers at the entry. -/
def entryL (ra : BitVec 64) (pa b : Nat) : GRegs :=
  [(1, ra), (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 b)]

/-- Registers at the return with result `r`. -/
def retL (ra r : BitVec 64) : GRegs := [(1, ra), (10, r)]

/-- At the `sltu` (`750`): `a5 = dp[0]`, `a1 = b`. -/
def leL (ra : BitVec 64) (b d : Nat) : GRegs :=
  [(1, ra), (11, BitVec.ofNat 64 b), (15, BitVec.ofNat 64 d)]

/-- After the `sltu` (`754`): `a5 = (dp[0] < b)`. -/
def tailL (ra t : BitVec 64) : GRegs := [(1, ra), (15, t)]

/-- The loads: the sign, `used`, the digit pointer and `dp[0]`. -/
structure Facts (m : Mem) (pa adp s u d : Nat) : Prop where
  rs : Ram pa 24
  rd : Ram adp 4
  s_v : bytesT4 m (pa + 8) = BitVec.ofNat 32 s
  u_v : bytesT4 m pa = BitVec.ofNat 32 u
  dp_v : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp
  d_v : bytesT4 m adp = BitVec.ofNat 32 d
  s_lt : s < 2 ^ 31
  u_lt : u < 2 ^ 31
  d_lt : d < 2 ^ 31

theorem Facts.sx {m : Mem} {pa adp s u d : Nat} (h : Facts m pa adp s u d) :
    BitVec.signExtend 64 (bytesT4 m (pa + 8)) = BitVec.ofNat 64 s ∧
      BitVec.signExtend 64 (bytesT4 m pa) = BitVec.ofNat 64 u ∧
      BitVec.signExtend 64 (bytesT4 m adp) = BitVec.ofNat 64 d :=
  ⟨by rw [h.s_v, signExtend_ofNat32 _ h.s_lt], by rw [h.u_v, signExtend_ofNat32 _ h.u_lt],
   by rw [h.d_v, signExtend_ofNat32 _ h.d_lt]⟩

/-- The all-ones word. -/
abbrev neg1 : BitVec 64 := 0xffffffffffffffff#64

section
variable (ra : BitVec 64) (v : Abi) (outp : Array String) (pa adp b s u d : Nat) (m : Mem)
  (hc : CodeAt m mpCmpDBase mpCmpDCode) (hf : Facts m pa adp s u d)
include hc hf

/-- `a->sign == MP_NEG`: `MP_LT`. -/
theorem neg_step (hra : ra.toNat % 4 = 0) (hs : s = 1) :
    Triple (At 0x80000728#64 (entryL ra pa b) m v.keep outp) (At ra (retL ra neg1) (writeLog m []) v.keep outp) := by
  cmpd_ctx
  have ⟨h1, h2, h3⟩ := hf.sx
  subst hs
  seg_step cdNeg ra [rd4 m (pa + 8)] [1, 10, 11] abiKeys [entryL] [retL] [h1, h2, h3] hc

/-- `a->used > 1`: `MP_GT`. -/
theorem gt1_step (hra : ra.toNat % 4 = 0) (hs : s ≠ 1) (hu : 1 < u) :
    Triple (At 0x80000728#64 (entryL ra pa b) m v.keep outp) (At ra (retL ra 1#64) (writeLog m []) v.keep outp) := by
  cmpd_ctx
  have ⟨h1, h2, h3⟩ := hf.sx
  seg_step cdGT1 ra [rd4 m (pa + 8), rd4 m pa] [1, 10, 11] abiKeys [entryL] [retL] [h1, h2, h3] hc

/-- `dp[0] > b`: `MP_GT`. -/
theorem gt2_step (hra : ra.toNat % 4 = 0) (hb : b < 2 ^ 31) (hs : s ≠ 1) (hu : u ≤ 1) (hd : b < d) :
    Triple (At 0x80000728#64 (entryL ra pa b) m v.keep outp) (At ra (retL ra 1#64) (writeLog m []) v.keep outp) := by
  cmpd_ctx
  have ⟨h1, h2, h3⟩ := hf.sx
  have h4 := hf.dp_v
  seg_step cdGT2 ra [rd4 m (pa + 8), rd4 m pa, rd8 m (pa + 16), rd4 m adp] [1, 10, 11] abiKeys
    [entryL] [retL] [h1, h2, h3, h4] hc

/-- `dp[0] ≤ b`: on to the `sltu`. -/
theorem le_step (hb : b < 2 ^ 31) (hs : s ≠ 1) (hu : u ≤ 1) (hd : d ≤ b) :
    Triple (At 0x80000728#64 (entryL ra pa b) m v.keep outp) (At 0x80000750#64 (leL ra b d) (writeLog m []) v.keep outp) := by
  cmpd_ctx
  have ⟨h1, h2, h3⟩ := hf.sx
  have h4 := hf.dp_v
  seg_step cdLE 0x80000750#64 [rd4 m (pa + 8), rd4 m pa, rd8 m (pa + 16), rd4 m adp] [1, 10, 11] abiKeys
    [entryL] [leL] [h1, h2, h3, h4] hc

end

/-- The `sltu a5,a5,a1` at `750`. -/
theorem sltu_step (ra : BitVec 64) (v : Abi) (outp : Array String) (b d : Nat) (m : Mem)
    (hc : CodeAt m mpCmpDBase mpCmpDCode) (hb : b < 2 ^ 31) (hd : d < 2 ^ 31) :
    Triple (At 0x80000750#64 (leL ra b d) m v.keep outp)
      (At 0x80000754#64 (tailL ra (if d < b then 1#64 else 0#64)) m v.keep outp) := by
  have h := sltu_at (pc := 0x80000750#64) (w := 0x00b7b7b3#32) (rd := 15) (rs1 := 15) (rs2 := 11)
    (L := leL ra b d) (keep := v.keep) (outp := outp)
    (hc.word (a := (0x80000750#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
    (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩
    (by decide) (Or.inr (by simp [keysG, leL])) (by decide) (Or.inr (by simp [keysG, leL])) (by decide)
    (by simp [keysG, leL]) (by simp [Abi.keep, keysG, sKeepL]) (by simp [Abi.keep, keysG, sKeepL])
  have hpc : Sail.BitVec.addInt (0x80000750#64 : BitVec 64) 4 = 0x80000754#64 := by decide
  have hv : (if (BitVec.ofNat 64 d).toNat < (BitVec.ofNat 64 b).toNat then 1#64 else 0#64) =
      (if d < b then 1#64 else 0#64) := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]
  rw [hpc, sltu_val, show srcVal 15 (leL ra b d) = BitVec.ofNat 64 d from by simp [srcVal, lookupG, leL],
    show srcVal 11 (leL ra b d) = BitVec.ofNat 64 b from by simp [srcVal, lookupG, leL], hv] at h
  exact Triple.rmap (fun cf h' => h'.reshape (by simp [leL, tailL, eraseG]) (fun p hp => by simp [hp])) h

/-- `negw a0,a5; ret` with `a5 = 1`: `MP_LT`. -/
theorem tail_lt (ra : BitVec 64) (v : Abi) (outp : Array String) (m : Mem)
    (hc : CodeAt m mpCmpDBase mpCmpDCode) (hra : ra.toNat % 4 = 0) :
    Triple (At 0x80000754#64 (tailL ra 1#64) m v.keep outp) (At ra (retL ra neg1) (writeLog m []) v.keep outp) := by
  cmpd_ctx
  refine Tom.Machine.seg_at' cdTail (pc1 := ra) ([] : List (List (BitVec 8))) [1, 15] abiKeys ?_ ?_ ?_ ?_
  · tom_facts hc
    all_goals leaf_auto [tailL] []
  · seg_nfo [cdTail, tailL]
    exact Tom.Machine.ret_target' _ hra
  · sub_auto [cdTail, tailL, retL] []
    all_goals decide
  · seg_nfo [cdTail, tailL]

/-- `negw a0,a5; ret` with `a5 = 0`: `MP_EQ`. -/
theorem tail_eq (ra : BitVec 64) (v : Abi) (outp : Array String) (m : Mem)
    (hc : CodeAt m mpCmpDBase mpCmpDCode) (hra : ra.toNat % 4 = 0) :
    Triple (At 0x80000754#64 (tailL ra 0#64) m v.keep outp) (At ra (retL ra 0#64) (writeLog m []) v.keep outp) := by
  cmpd_ctx
  seg_step cdTail ra ([] : List (List (BitVec 8))) [1, 15] abiKeys [tailL] [retL] [] hc

end Tom.Machine.Fn.CmpD
