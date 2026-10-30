import Tom.Machine.Kit.Alu1

/-!
# `slt rd, rs1, rs2`

`Kit/Alu1.lean`'s `sltu_at` for the signed comparison (`s_mp_exptmod_fast`'s window size
`7 + (3529 < x)`), and its value on two `ofNat` words below `2^63` (`slt_ofNat`).
-/

namespace Tom.Machine

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa Vsa.Sim
open Vsa.Logic
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (Config MState)

/-- **`slt rd, rs1, rs2`** from `At pc L`: one step to `pc + 4` with `rd := (rs1 <s rs2)`. -/
theorem slt_at {pc : BitVec 64} {w : BitVec 32} {rd rs1 rs2 : Nat}
    {L : GRegs} {m : Mem} {keep : GRegs} {outp : Array String}
    (hb : m[pc.toNat]? = some (w.extractLsb' 0 8) ∧ m[pc.toNat + 1]? = some (w.extractLsb' 8 8) ∧
      m[pc.toNat + 2]? = some (w.extractLsb' 16 8) ∧ m[pc.toNat + 3]? = some (w.extractLsb' 24 8))
    (hword : ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
      (w.extractLsb' 0 8)) = w)
    (hnotrvc : Sail.BitVec.extractLsb ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append
      (w.extractLsb' 8 8)).append (w.extractLsb' 0 8)) 1 0 = (0b11#2 : BitVec 2))
    (hdec' : ∀ s : SequentialState RegisterType trivialChoiceSource,
      s.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) →
      s.regs.get? Register.cur_privilege =
        some ((Privilege.Machine) : RegisterType Register.cur_privilege) →
      s.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) →
      (ext_decode w).run s =
        .ok (instruction.RTYPE (gprIdx rs2, gprIdx rs1, gprIdx rd, rop.SLT)) s)
    (hfetch : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hrs1 : rs1 = 0 ∨ rs1 ∈ keysG L) (hrs1' : rs1 ≤ 31)
    (hrs2 : rs2 = 0 ∨ rs2 ∈ keysG L) (hrs2' : rs2 ≤ 31)
    (hLk : ∀ n ∈ keysG L, 1 ≤ n ∧ n ≤ 31)
    (hkk : ∀ n ∈ keysG keep, 1 ≤ n ∧ n ≤ 31) (hrdk : rd ∉ keysG keep) :
    Triple (At pc L m keep outp)
      (At (BitVec.addInt pc 4)
        ((rd, zero_extend (m := 64)
          (bool_to_bit (zopz0zI_s (srcVal rs1 L) (srcVal rs2 L)))) :: eraseG rd L)
        m keep outp) :=
  alu1_at hb hword hnotrvc hdec'
    (fun _ hL => execute_rtype_slt_char (gprIdx rs2) (gprIdx rs1) (gprIdx rd)
      (srcVal rs1 L) (srcVal rs2 L) _ _
      (rX_srcVal pc hL hrs1 hrs1') (rX_srcVal pc hL hrs2 hrs2') (wX_gpr _ _ rd hrd.1 hrd.2))
    hfetch hrd hLk hkk hrdk

/-- `slt`'s value on two nonnegative words. -/
theorem slt_ofNat {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_s (BitVec.ofNat 64 a) (BitVec.ofNat 64 b))) =
      BitVec.ofNat 64 (if a < b then 1 else 0) := by
  have e : zopz0zI_s (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
    unfold zopz0zI_s
    have h1 : (BitVec.ofNat 64 a).toInt = (a : Int) := by
      rw [BitVec.toInt_eq_toNat_of_msb]
      · simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
      · rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    have h2 : (BitVec.ofNat 64 b).toInt = (b : Int) := by
      rw [BitVec.toInt_eq_toNat_of_msb]
      · simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
      · rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
    rw [h1, h2]; simp
  rw [e]
  by_cases h : a < b
  · simp only [h, decide_true, ↓reduceIte]; rfl
  · simp only [h, decide_false, ↓reduceIte]; rfl

end Tom.Machine
