import Tom.Machine.Kit.At
import Vsa.Sim.StepObs
import Vsa.Sim.Muldi3Spec

/-!
# A linking `jalr`, and moving pins between `L` and `keep`

`jalr ra, imm(rs1)` (an indirect call) is not a segment terminator
(`Vsa.Sim.TKind.jr` is `jalr x0`). `jalr_at` is its one-step rule between
`At` states: the target is `update (rs1 + sext imm) 0 0`, `ra := pc + 4`,
memory, `keep` and the console unchanged.

`At.reshape` moves register pins between the computed list `L` and `keep`,
so that a segment used from two call sites can be stated once over a small
`L`, with the caller's other pins in `keep`. `frameOK_nowrite`/`frameOK_of`
decide a segment's `FrameOK` for a `keep` with symbolic keys.
-/

namespace Tom.Machine

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa Vsa.Sim
open Vsa.Logic
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (Config MState)

/-! ## Register-frame helpers -/

theorem noise_gpr' : ∀ n, n < 32 → 1 ≤ n → ∀ rr ∈ noiseRegs, (rr == gprReg n) = false := by
  decide

theorem noise_gpr (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ 31) :
    ∀ rr ∈ noiseRegs, (rr == gprReg n) = false :=
  noise_gpr' n (by omega) h1

theorem htif_gpr' : ∀ n, n < 32 → 1 ≤ n →
    (gprReg n == Register.htif_payload_writes) = false ∧ (gprReg n == Register.htif_tohost) = false := by
  decide

/-- A chain that writes no register keeps any `keep` set of GPR pins. -/
theorem frameOK_nowrite (ks : List Nat) (bs : List BBlock) (hw : wrChain bs = [])
    (hk : KeysOK ks) : FrameOK ks bs := by
  refine ⟨fun n hn => ⟨hk n hn, noise_gpr n (hk n hn).1 (hk n hn).2, ?_⟩, ?_⟩
  · rw [hw]; intro m hm; cases hm
  · rw [hw]; intro m hm; cases hm

/-- A chain keeps a `keep` set of GPR pins none of whose keys it writes. -/
theorem frameOK_of (ks : List Nat) (bs : List BBlock)
    (hw : ∀ m ∈ wrChain bs, 1 ≤ m ∧ m ≤ 31)
    (hk : ∀ n ∈ ks, (1 ≤ n ∧ n ≤ 31) ∧ n ∉ wrChain bs) : FrameOK ks bs := by
  refine ⟨fun n hn => ⟨(hk n hn).1, noise_gpr n (hk n hn).1.1 (hk n hn).1.2, fun m hm => ?_⟩,
    fun m hm => htif_gpr' m (by have := hw m hm; omega) (hw m hm).1⟩
  have hn := hk n hn
  have hm' := hw m hm
  exact gprReg_beq_false m (by omega) n (by omega) hm'.1 hn.1.1
    (fun e => hn.2 (e ▸ hm))

theorem gholds_append {σ : MState} : ∀ {A B : GRegs}, GHolds σ (A ++ B) ↔ GHolds σ A ∧ GHolds σ B
  | [], _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | (_, _) :: A, B => by
    show (_ ∧ GHolds σ (A ++ B)) ↔ (_ ∧ GHolds σ A) ∧ GHolds σ B
    rw [gholds_append]; exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

/-- Move pins between `L` and `keep` (and drop some): every pin of the new
`L'` and `keep'` was a pin of `L` or `keep`. -/
theorem At.reshape {pc : BitVec 64} {L L' K K' : GRegs} {m : Mem} {outp : Array String}
    {c : Config} (h : At pc L m K outp c) (hL : ∀ p ∈ L', p ∈ L ++ K)
    (hK : ∀ p ∈ K', p ∈ L ++ K) : At pc L' m K' outp c :=
  have hall : GHolds c.σ (L ++ K) := gholds_append.2 ⟨h.regs, h.keep⟩
  { h with regs := gholds_of_mem hall hL, keep := gholds_of_mem hall hK }

/-! ## The linking `jalr` step -/

theorem get?_sigmaTick_jalr (σ : MState) (pc vminstret tgt : BitVec 64)
    (rd_reg : Register) (link : RegisterType rd_reg)
    (vmip vmtime vmtimecmp vmcycle : BitVec 64) (R : Register)
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false) :
    (sigmaTick_jalr σ pc vminstret tgt rd_reg link vmip vmtime vmtimecmp vmcycle).regs.get? R
      = (sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.get? R := by
  show (((((sigmaPost_jalr σ pc vminstret tgt rd_reg link).regs.insert Register.mcycle _).insert
      Register.mtime _).insert Register.mip _)).get? R = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmi, Bool.false_eq_true, ↓reduceDIte]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmt, Bool.false_eq_true, ↓reduceDIte]
  rw [Std.ExtDHashMap.get?_insert]
  simp only [hmc, Bool.false_eq_true, ↓reduceDIte]

/-- The tick-absorbing observational step of a linking `jalr`. -/
theorem stepObs_jalr
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vrs1 : BitVec 64)
    (w : BitVec 32) (imm : BitVec 12) (rs1 rd : regidx) (rd_reg : Register)
    (link : RegisterType rd_reg) (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hb0 : σ.mem[pc.toNat]? = some b0) (hb1 : σ.mem[pc.toNat + 1]? = some b1)
    (hb2 : σ.mem[pc.toNat + 2]? = some b2) (hb3 : σ.mem[pc.toNat + 3]? = some b3)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : FetchOK pc.toNat) (halign : pc.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : (ext_decode w).run (afterPrelude σ)
      = .ok (instruction.JALR (imm, rs1, rd)) (afterPrelude σ))
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vrs1 (afterNextPC (afterPrelude σ) pc))
    (htgt : (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hrd_npc : (rd_reg == Register.nextPC) = false)
    (hrd_mi : (rd_reg == Register.minstret_increment) = false)
    (hrd_ms : (rd_reg == Register.minstret) = false)
    (hrd_hart : (rd_reg == Register.hart_state) = false)
    (hrd : NonPinned rd_reg)
    (hwr : (wX_bits rd (BitVec.addInt pc 4)).run
        {(afterNextPC (afterPrelude σ) pc) with
          regs := (afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
            (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)}
        = .ok () (sigma3_jalr σ pc (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg link))
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jalr σ pc vminstret (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1)
          rd_reg link) := by
  by_cases htick : i + 1 = 2
  · have hGp := goodstate_sigmaPost_jalr σ pc vminstret
      (BitVec.update (vrs1 + sign_extend (m := 64) imm) 0 0#1) rd_reg hrd link hG
    obtain ⟨vmip, hmip⟩ := hGp.mip
    obtain ⟨vmtime, hmtime⟩ := hGp.mtime
    obtain ⟨vmtimecmp, hmtimecmp⟩ := hGp.mtimecmp
    obtain ⟨vmcycle, hmcycle⟩ := hGp.mcycle
    obtain ⟨hstep, hGt⟩ := step_jalr_tick σ i u pc vminstret vrs1 w imm rs1 rd rd_reg link
      b0 b1 b2 b3 vmip vmtime vmtimecmp vmcycle
      hG hpc hminstret hmip hmtime hmtimecmp hmcycle
      hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt
      hrd_npc hrd_mi hrd_ms hrd_hart hrd hwr htick
    refine ⟨_, 0, hstep, by decide, hGt, rfl, ?_, rfl⟩
    intro R hmc hmt hmi
    exact get?_sigmaTick_jalr σ pc vminstret _ rd_reg link vmip vmtime vmtimecmp vmcycle
      R hmc hmt hmi
  · obtain ⟨hstep, hGt⟩ := step_jalr_notick σ i u pc vminstret vrs1 w imm rs1 rd rd_reg link
      b0 b1 b2 b3 hG hpc hminstret hb0 hb1 hb2 hb3 hlo hhi halign hnotrvc hword hdec hrs1 htgt
      hrd_npc hrd_mi hrd_ms hrd_hart hrd hwr htick
    exact ⟨_, i + 1, hstep, by omega, hGt, rfl, ReadsLikePost.rfl _⟩

/-- **A linking `jalr ra, imm(rs1)`** from `At pc L`: one step to the target
`update (rs1 + sext imm) 0 0`, with `ra := pc + 4`, the pins `L' ⊆ L` other
than `ra`, and memory, `keep` and the console unchanged. The word facts
(`hb` from `CodeAt.word`, `hword`, `hnotrvc`, `hdec` by `decodeW`, `hfetch`)
are closed by `decide` at a literal word. -/
theorem jalr_at {pc : BitVec 64} {w : BitVec 32} {imm : BitVec 12} {rs1 : Nat}
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
      (ext_decode w).run s = .ok (instruction.JALR (imm, gprIdx rs1, regidx.Regidx 0x01#5)) s)
    (hfetch : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0)
    (hrs : rs1 ∈ keysG L) (hrs31 : rs1 ≤ 31)
    (htgt : (BitVec.update (srcVal rs1 L + sign_extend (m := 64) imm) 0 0#1).toNat % 4 = 0)
    (hL' : ∀ p ∈ L', p ∈ L) (hL'k : ∀ n ∈ keysG L', 2 ≤ n ∧ n ≤ 31)
    (hkk : ∀ n ∈ keysG keep, 2 ≤ n ∧ n ≤ 31) :
    Triple (At pc L m keep outp)
      (At (BitVec.update (srcVal rs1 L + sign_extend (m := 64) imm) 0 0#1)
        ((1, BitVec.addInt pc 4) :: L') m keep outp) := by
  intro c hc
  obtain ⟨vm, hmi⟩ := hc.minstret
  have hmem := hc.mem
  have hb' := hb
  rw [← hmem] at hb'
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb'
  have hG := hc.good
  have hsp := srcPin_srcVal c.σ L rs1 (Or.inr hrs) hc.regs
  have hrx := rX_src c.σ pc rs1 hrs31 _ hsp
  have hd := hdec' (afterPrelude c.σ)
    (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
    (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
    (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg)
  obtain ⟨σ', i', hs, hi', hG', hmem', hobs⟩ :=
    stepObs_jalr c.σ c.tick c.steps pc vm (srcVal rs1 L) w imm (gprIdx rs1) (regidx.Regidx 0x01#5)
      Register.x1 (BitVec.addInt pc 4) _ _ _ _ hG hc.pcv hmi hb0 hb1 hb2 hb3
      hfetch.1 hfetch.2.1 hfetch.2.2 hnotrvc hword hd hrx htgt
      (by decide) (by decide) (by decide) (by decide) (by decide) (wX_bits_x1 _ _) hc.tick
  -- the register frame: everything but the noise registers and `x1`
  have hfr : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ m ∈ [1], (gprReg m == R) = false) → σ'.regs.get? R = c.σ.regs.get? R := by
    intro R hn hw
    exact (hobs.1 R (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
      (hn Register.mip (by decide))).trans
      (get?_sigmaPost_jalr c.σ pc vm _ Register.x1 _ R (hn Register.minstret (by decide))
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
        show ((((sigma3_jalr c.σ pc _ Register.x1 _).regs.insert Register.PC _).insert
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
        show ((((sigma3_jalr c.σ pc _ Register.x1 _).regs.insert Register.PC _).insert
          Register.minstret (BitVec.addInt vm 1))).get? Register.PC = _
        rw [Std.ExtDHashMap.get?_insert]
        simp only [show (Register.minstret == Register.PC) = false from by decide,
          Bool.false_eq_true, ↓reduceDIte]
        rw [Std.ExtDHashMap.get?_insert_self])
      minstret := ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
        (by decide) (by decide) (by decide) (by
          show ((((sigma3_jalr c.σ pc _ Register.x1 _).regs.insert Register.PC _).insert
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
