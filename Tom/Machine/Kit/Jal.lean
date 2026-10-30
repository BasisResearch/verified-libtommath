import Tom.Machine.Kit.Jalr

/-!
# A call: `jal ra, target`

`jal_at` is `jalr_at` (Kit/Jalr.lean) for a direct call: one step to
`pc + sext imm`, with `ra := pc + 4`; the pins `L' ⊆ L` other than `ra`,
memory, `keep` and the console unchanged. Over the copied `Vsa.Sim.stepObs_jal`.
-/

namespace Tom.Machine

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa Vsa.Sim
open Vsa.Logic
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (Config MState)

theorem jal_at {pc : BitVec 64} {w : BitVec 32} {imm : BitVec 21}
    {L L' : GRegs} {m : Mem} {keep : GRegs} {outp : Array String}
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
      (ext_decode w).run s = .ok (instruction.JAL (imm, regidx.Regidx 0x01#5)) s)
    (hfetch : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0)
    (htgt : (pc + sign_extend (m := 64) imm).toNat % 4 = 0)
    (hL' : ∀ p ∈ L', p ∈ L) (hL'k : ∀ n ∈ keysG L', 2 ≤ n ∧ n ≤ 31)
    (hkk : ∀ n ∈ keysG keep, 2 ≤ n ∧ n ≤ 31) :
    Triple (At pc L m keep outp)
      (At (pc + sign_extend (m := 64) imm) ((1, BitVec.addInt pc 4) :: L') m keep outp) := by
  intro c hc
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hmem := hc.mem
  have hb' := hb
  rw [← hmem] at hb'
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb'
  have hG := hc.good
  have hd := hdec' (afterPrelude c.σ)
    (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
    (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
    (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg)
  obtain ⟨σ', i', hs, hi', hG', hmem', hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps pc vm w imm (regidx.Regidx 0x01#5)
      Register.x1 (BitVec.addInt pc 4) _ _ _ _ hG hc.pcv hmi hb0 hb1 hb2 hb3
      hfetch.1 hfetch.2.1 hfetch.2.2 hnotrvc hword hd htgt
      (by decide) (by decide) (by decide) (by decide) (by decide) (wX_bits_x1 _ _) hc.tick
  -- the register frame: everything but the noise registers and `x1`
  have hfr : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ m ∈ [1], (gprReg m == R) = false) → σ'.regs.get? R = c.σ.regs.get? R := by
    intro R hn hw
    exact (hobs.1 R (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
      (hn Register.mip (by decide))).trans
      (get?_sigmaPost_jal c.σ pc vm imm Register.x1 _ R (hn Register.minstret (by decide))
        (hn Register.PC (by decide)) (hw 1 (by simp)) (hn Register.nextPC (by decide))
        (hn Register.minstret_increment (by decide)))
  have hok : ∀ K : GRegs, (∀ n ∈ keysG K, 2 ≤ n ∧ n ≤ 31) → ∀ n ∈ keysG K, (1 ≤ n ∧ n ≤ 31) ∧
      (∀ rr ∈ noiseRegs, (rr == gprReg n) = false) ∧ (∀ m ∈ [1], (gprReg m == gprReg n) = false) := by
    intro K hK n hn
    have h := hK n hn
    refine ⟨⟨by omega, h.2⟩, noise_gpr n (by omega) h.2, fun m hm => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    exact gprReg_beq_false 1 (by omega) n (by omega) (by omega) (by omega) (by omega)
  refine ⟨⟨σ', i', c.steps + 1⟩, Vsa.Machine.Steps.head hs (Vsa.Machine.Steps.refl _), ?_⟩
  have hregs1 : GHolds σ' ((1, BitVec.addInt pc 4) :: L') :=
    ⟨readback σ' _ hobs Register.x1 (by decide) (by decide) (by decide) (by
        show ((((sigma3_jal c.σ pc imm Register.x1 _).regs.insert Register.PC _).insert
          Register.minstret (BitVec.addInt vm 1))).get? Register.x1 = _
        rw [Std.ExtDHashMap.get?_insert]
        simp only [show (Register.minstret == Register.x1) = false from by decide,
          Bool.false_eq_true, ↓reduceDIte]
        rw [Std.ExtDHashMap.get?_insert]
        simp only [show (Register.PC == Register.x1) = false from by decide,
          Bool.false_eq_true, ↓reduceDIte]
        show (((afterNextPC (afterPrelude c.σ) pc).regs.insert Register.nextPC _).insert
          Register.x1 _).get? Register.x1 = _
        rw [Std.ExtDHashMap.get?_insert_self]),
      gholds_keep_of_frame L' (hok L' hL'k) hfr (gholds_of_mem hc.regs hL')⟩
  exact
    { good := hG'
      tick := hi'
      mem := hmem'.trans hmem
      pcv := readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (by
        show ((((sigma3_jal c.σ pc imm Register.x1 _).regs.insert Register.PC _).insert
          Register.minstret (BitVec.addInt vm 1))).get? Register.PC = _
        rw [Std.ExtDHashMap.get?_insert]
        simp only [show (Register.minstret == Register.PC) = false from by decide,
          Bool.false_eq_true, ↓reduceDIte]
        rw [Std.ExtDHashMap.get?_insert_self])
      minstret := ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
        (by decide) (by decide) (by decide) (by
          show ((((sigma3_jal c.σ pc imm Register.x1 _).regs.insert Register.PC _).insert
            Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
          rw [Std.ExtDHashMap.get?_insert_self])⟩
      regs := hregs1
      keep := gholds_keep_of_frame keep (hok keep hkk) hfr hc.keep
      out := hobs.2.trans hc.out
      pw := (hfr Register.htif_payload_writes (by decide) (by decide)).trans hc.pw
      th := by
        obtain ⟨v, hv⟩ := hc.th
        exact ⟨v, (hfr Register.htif_tohost (by decide) (by decide)).trans hv⟩
      gprs := allGprs_of_frame hc.gprs hfr fun m hm => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        subst hm
        exact ⟨by decide, gholds_isSome hregs1 (List.mem_cons_self ..)⟩ }

end Tom.Machine
