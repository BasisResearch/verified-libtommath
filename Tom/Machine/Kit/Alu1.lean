import Tom.Machine.Kit.Jalr
import Vsa.Sim.BlockMem
import Vsa.Sim.ExecuteAlu
import Tom.Machine.Code

/-!
# One ALU instruction the segment evaluator does not know: `sltiu`, `sltu`, `sra`

The segment kinds (`Vsa.Sim.MKind`) have no `SLTIU`, `SLTU` or `SRA`, so a
`#derive_case` chain cannot run through `seqz rd, rs` (`sltiu rd, rs, 1`),
`snez rd, rs` (`sltu rd, x0, rs`) or `sra`. Each is one step here, between `At`
states, in the style of `jal_at` (Kit/Jal.lean).

`alu1_at` is the common rule: an instruction word that decodes to some `ast`
whose execution (`hexec`, at every state where `L` holds) writes `v` to `rd`
and nothing else. The post state is at `pc + 4` with pins
`(rd, v) :: eraseG rd L`, memory, `keep` and the console unchanged. It is the
`.slti` case of `Vsa/Sim/BlockMem.lean` (`stepObs_alu`, `obs_gpr_rd`,
`gholds_eraseG`, `frame_step_alu`) restated for `At`. `sltiu_at`, `sltu_at`
and `sra_at` supply `hexec` from the copied `execute_*_char` lemmas, and
`seqz_at`/`snez_at` evaluate the comparison.

Side conditions (all `decide` on literal indices and pin lists):
`1 ≤ rd ≤ 31`; each source is `x0` or a key of `L` (and `≤ 31`); the keys of
`L` and of `keep` are in `1..31`; `rd ∉ keysG keep`.
-/

namespace Tom.Machine

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa Vsa.Sim
open Vsa.Logic
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (Config MState)

/-- **One register-writing ALU step** from `At pc L`: the word `w` at `pc`
decodes to `ast` (`hdec'`), and executing `ast` writes `v` to GPR `rd`
(`hexec`, given the pins `L`). One step to `pc + 4` with `rd := v`, the other
pins of `L` kept, and memory, `keep` and the console unchanged. -/
theorem alu1_at {pc : BitVec 64} {w : BitVec 32} {ast : instruction} {rd : Nat} {v : BitVec 64}
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
      (ext_decode w).run s = .ok ast s)
    (hexec : ∀ σ : MState, GHolds σ L →
      (execute ast).run (afterNextPC (afterPrelude σ) pc)
        = .ok RETIRE_SUCCESS (sigma3_alu σ pc (gprReg rd) (gprRT rd v)))
    (hfetch : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hLk : ∀ n ∈ keysG L, 1 ≤ n ∧ n ≤ 31)
    (hkk : ∀ n ∈ keysG keep, 1 ≤ n ∧ n ≤ 31) (hrdk : rd ∉ keysG keep) :
    Triple (At pc L m keep outp)
      (At (BitVec.addInt pc 4) ((rd, v) :: eraseG rd L) m keep outp) := by
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
  obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := gpr_rd_ok rd (by omega) hrd.1
  obtain ⟨σ', i', hs, hi', hG', hmem', hobs⟩ :=
    stepObs_alu c.σ c.tick c.steps pc vm w ast (gprReg rd) (gprRT rd v) _ _ _ _
      hG hc.pcv hmi hword hnotrvc hd (hexec c.σ hc.regs)
      hr1 hr2 hr3 hr4 hr5
      hb0 hb1 hb2 hb3 hfetch.1 hfetch.2.1 hfetch.2.2 hc.tick
  -- the register frame: everything but the noise registers and `rd`
  have hfr : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ k ∈ [rd], (gprReg k == R) = false) → σ'.regs.get? R = c.σ.regs.get? R :=
    fun R hn hw => frame_step_alu hobs R hn (hw rd (List.mem_singleton_self _))
  have hok : ∀ n ∈ keysG keep, (1 ≤ n ∧ n ≤ 31) ∧
      (∀ rr ∈ noiseRegs, (rr == gprReg n) = false) ∧
      (∀ k ∈ [rd], (gprReg k == gprReg n) = false) := by
    intro n hn
    have h := hkk n hn
    refine ⟨h, noise_gpr n h.1 h.2, fun k hk => ?_⟩
    rw [List.mem_singleton] at hk
    subst hk
    exact gprReg_beq_false _ (by omega) n (by omega) hrd.1 h.1 (fun e => hrdk (e ▸ hn))
  have hht := htif_gpr' rd (by omega) hrd.1
  have hhfr : ∀ R, (R = Register.htif_payload_writes ∨ R = Register.htif_tohost) →
      σ'.regs.get? R = c.σ.regs.get? R := by
    intro R hR
    rcases hR with rfl | rfl
    · exact frame_step_alu hobs _ (by decide) hht.1
    · exact frame_step_alu hobs _ (by decide) hht.2
  refine ⟨⟨σ', i', c.steps + 1⟩, Vsa.Machine.Steps.head hs (Vsa.Machine.Steps.refl _), ?_⟩
  exact
    { good := hG'
      tick := hi'
      mem := hmem'.trans hmem
      pcv := obs_alu_pc hobs
      minstret := obs_alu_minstret hobs
      regs := ⟨obs_gpr_rd rd hrd.1 hrd.2 v hobs, gholds_eraseG hobs hrd.1 hrd.2 L hLk hc.regs⟩
      keep := gholds_keep_of_frame keep hok hfr hc.keep
      out := hobs.2.trans hc.out
      pw := (hhfr _ (Or.inl rfl)).trans hc.pw
      th := by
        obtain ⟨v, hv⟩ := hc.th
        exact ⟨v, (hhfr _ (Or.inr rfl)).trans hv⟩
      gprs := allGprs_of_frame hc.gprs hfr fun k hk => by
        rw [List.mem_singleton] at hk
        subst hk
        exact ⟨hrd, by rw [obs_gpr_rd k hrd.1 hrd.2 v hobs]; rfl⟩ }

/-- The source read of `alu1_at`'s `hexec`: a source that is `x0` or pinned
in `L` reads `srcVal rs L`. -/
theorem rX_srcVal {σ : MState} {L : GRegs} {rs : Nat} (pc : BitVec 64) (hL : GHolds σ L)
    (hrs : rs = 0 ∨ rs ∈ keysG L) (hrs31 : rs ≤ 31) :
    (rX_bits (gprIdx rs)).run (afterNextPC (afterPrelude σ) pc)
      = .ok (srcVal rs L) (afterNextPC (afterPrelude σ) pc) :=
  rX_src σ pc rs hrs31 _ (srcPin_srcVal σ L rs hrs hL)

/-! ## `sltiu`, `sltu`, `sra` -/

/-- **`sltiu rd, rs1, imm`** from `At pc L`: one step to `pc + 4` with
`rd := (rs1 <u sext imm)`, the rest as `alu1_at`. -/
theorem sltiu_at {pc : BitVec 64} {w : BitVec 32} {imm : BitVec 12} {rd rs1 : Nat}
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
      (ext_decode w).run s = .ok (instruction.ITYPE (imm, gprIdx rs1, gprIdx rd, iop.SLTIU)) s)
    (hfetch : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hrs : rs1 = 0 ∨ rs1 ∈ keysG L) (hrs31 : rs1 ≤ 31)
    (hLk : ∀ n ∈ keysG L, 1 ≤ n ∧ n ≤ 31)
    (hkk : ∀ n ∈ keysG keep, 1 ≤ n ∧ n ≤ 31) (hrdk : rd ∉ keysG keep) :
    Triple (At pc L m keep outp)
      (At (BitVec.addInt pc 4)
        ((rd, zero_extend (m := 64)
          (bool_to_bit (zopz0zI_u (srcVal rs1 L) (sign_extend (m := 64) imm)))) :: eraseG rd L)
        m keep outp) :=
  alu1_at hb hword hnotrvc hdec'
    (fun _ hL => execute_itype_sltiu_char imm (gprIdx rs1) (gprIdx rd) (srcVal rs1 L) _ _
      (rX_srcVal pc hL hrs hrs31) (wX_gpr _ _ rd hrd.1 hrd.2))
    hfetch hrd hLk hkk hrdk

/-- **`sltu rd, rs1, rs2`** from `At pc L`: one step to `pc + 4` with
`rd := (rs1 <u rs2)`, the rest as `alu1_at`. -/
theorem sltu_at {pc : BitVec 64} {w : BitVec 32} {rd rs1 rs2 : Nat}
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
        .ok (instruction.RTYPE (gprIdx rs2, gprIdx rs1, gprIdx rd, rop.SLTU)) s)
    (hfetch : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hrs1 : rs1 = 0 ∨ rs1 ∈ keysG L) (hrs1' : rs1 ≤ 31)
    (hrs2 : rs2 = 0 ∨ rs2 ∈ keysG L) (hrs2' : rs2 ≤ 31)
    (hLk : ∀ n ∈ keysG L, 1 ≤ n ∧ n ≤ 31)
    (hkk : ∀ n ∈ keysG keep, 1 ≤ n ∧ n ≤ 31) (hrdk : rd ∉ keysG keep) :
    Triple (At pc L m keep outp)
      (At (BitVec.addInt pc 4)
        ((rd, zero_extend (m := 64)
          (bool_to_bit (zopz0zI_u (srcVal rs1 L) (srcVal rs2 L)))) :: eraseG rd L)
        m keep outp) :=
  alu1_at hb hword hnotrvc hdec'
    (fun _ hL => execute_rtype_sltu_char (gprIdx rs2) (gprIdx rs1) (gprIdx rd)
      (srcVal rs1 L) (srcVal rs2 L) _ _
      (rX_srcVal pc hL hrs1 hrs1') (rX_srcVal pc hL hrs2 hrs2') (wX_gpr _ _ rd hrd.1 hrd.2))
    hfetch hrd hLk hkk hrdk

/-- **`sra rd, rs1, rs2`** from `At pc L`: one step to `pc + 4` with
`rd := rs1 >>ₐ (rs2 & 63)`, the rest as `alu1_at`. -/
theorem sra_at {pc : BitVec 64} {w : BitVec 32} {rd rs1 rs2 : Nat}
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
        .ok (instruction.RTYPE (gprIdx rs2, gprIdx rs1, gprIdx rd, rop.SRA)) s)
    (hfetch : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hrs1 : rs1 = 0 ∨ rs1 ∈ keysG L) (hrs1' : rs1 ≤ 31)
    (hrs2 : rs2 = 0 ∨ rs2 ∈ keysG L) (hrs2' : rs2 ≤ 31)
    (hLk : ∀ n ∈ keysG L, 1 ≤ n ∧ n ≤ 31)
    (hkk : ∀ n ∈ keysG keep, 1 ≤ n ∧ n ≤ 31) (hrdk : rd ∉ keysG keep) :
    Triple (At pc L m keep outp)
      (At (BitVec.addInt pc 4)
        ((rd, shift_bits_right_arith (srcVal rs1 L) (Sail.BitVec.extractLsb (srcVal rs2 L) 5 0))
          :: eraseG rd L)
        m keep outp) :=
  alu1_at hb hword hnotrvc hdec'
    (fun _ hL => execute_rtype_sra_char (gprIdx rs2) (gprIdx rs1) (gprIdx rd)
      (srcVal rs1 L) (srcVal rs2 L) _ _
      (rX_srcVal pc hL hrs1 hrs1') (rX_srcVal pc hL hrs2 hrs2') (wX_gpr _ _ rd hrd.1 hrd.2))
    hfetch hrd hLk hkk hrdk

/-! ## The comparison values, and `seqz`/`snez` -/

/-- The value an `sltu`/`sltiu` writes, as an `if` on `toNat`. -/
theorem sltu_val (a b : BitVec 64) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u a b)) =
      if a.toNat < b.toNat then 1#64 else 0#64 := by
  have e : zopz0zI_u a b = decide (a.toNat < b.toNat) := by
    unfold zopz0zI_u; simp [Sail.BitVec.toNatInt]
  rw [e]
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, ↓reduceIte]; rfl
  · simp only [h, decide_false, ↓reduceIte]; rfl

/-- The value `seqz` (`sltiu rd, rs, 1`) writes. -/
theorem seqz_val (a : BitVec 64) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u a (sign_extend (m := 64) (1#12)))) =
      if a = 0#64 then 1#64 else 0#64 := by
  rw [show sign_extend (m := 64) (1#12) = 1#64 from by decide, sltu_val]
  by_cases h : a = 0#64
  · subst h; rfl
  · have h1 : ¬ a.toNat < (1#64).toNat := by
      have : a.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
      simp only [BitVec.toNat_ofNat]; omega
    simp only [h1, h, ↓reduceIte]

/-- The value `snez` (`sltu rd, x0, rs`) writes. -/
theorem snez_val (b : BitVec 64) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) b)) = if b = 0#64 then 0#64 else 1#64 := by
  rw [sltu_val]
  by_cases h : b = 0#64
  · subst h; rfl
  · have h1 : (0#64).toNat < b.toNat := by
      have : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
      simp only [BitVec.toNat_ofNat]; omega
    simp only [h1, h, ↓reduceIte]

/-- `if x = 0` on an `ofNat` value with `x < 2^64`, in `ofNat` form. -/
theorem ite_ofNat_eq_zero {x : Nat} (hx : x < 2 ^ 64) :
    (if BitVec.ofNat 64 x = 0#64 then 1#64 else 0#64) = BitVec.ofNat 64 (if x = 0 then 1 else 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 x ≠ 0#64 := fun e => h (by
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
      simpa using this)
    simp only [this, h, ↓reduceIte]

/-- **`seqz rd, rs1`** (`sltiu rd, rs1, 1`) from `At pc L`: one step to
`pc + 4` with `rd := (rs1 = 0 ? 1 : 0)`; side conditions as `sltiu_at`. -/
theorem seqz_at {pc : BitVec 64} {w : BitVec 32} {rd rs1 : Nat}
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
      (ext_decode w).run s = .ok (instruction.ITYPE (1#12, gprIdx rs1, gprIdx rd, iop.SLTIU)) s)
    (hfetch : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hrs : rs1 = 0 ∨ rs1 ∈ keysG L) (hrs31 : rs1 ≤ 31)
    (hLk : ∀ n ∈ keysG L, 1 ≤ n ∧ n ≤ 31)
    (hkk : ∀ n ∈ keysG keep, 1 ≤ n ∧ n ≤ 31) (hrdk : rd ∉ keysG keep) :
    Triple (At pc L m keep outp)
      (At (BitVec.addInt pc 4)
        ((rd, if srcVal rs1 L = 0#64 then 1#64 else 0#64) :: eraseG rd L) m keep outp) := by
  rw [← seqz_val]
  exact sltiu_at hb hword hnotrvc hdec' hfetch hrd hrs hrs31 hLk hkk hrdk

/-- **`snez rd, rs2`** (`sltu rd, x0, rs2`) from `At pc L`: one step to
`pc + 4` with `rd := (rs2 = 0 ? 0 : 1)`; side conditions as `sltu_at`. -/
theorem snez_at {pc : BitVec 64} {w : BitVec 32} {rd rs2 : Nat}
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
        .ok (instruction.RTYPE (gprIdx rs2, gprIdx 0, gprIdx rd, rop.SLTU)) s)
    (hfetch : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0)
    (hrd : 1 ≤ rd ∧ rd ≤ 31) (hrs2 : rs2 = 0 ∨ rs2 ∈ keysG L) (hrs2' : rs2 ≤ 31)
    (hLk : ∀ n ∈ keysG L, 1 ≤ n ∧ n ≤ 31)
    (hkk : ∀ n ∈ keysG keep, 1 ≤ n ∧ n ≤ 31) (hrdk : rd ∉ keysG keep) :
    Triple (At pc L m keep outp)
      (At (BitVec.addInt pc 4)
        ((rd, if srcVal rs2 L = 0#64 then 0#64 else 1#64) :: eraseG rd L) m keep outp) := by
  rw [← snez_val]
  exact sltu_at (rs1 := 0) hb hword hnotrvc hdec' hfetch hrd (Or.inl rfl) (by decide)
    hrs2 hrs2' hLk hkk hrdk

end Tom.Machine

/-! ## Usage: `seqz a7, a7` in `mp_sub` (0x80001f68, word 0x0018b893) -/

namespace Tom.Machine

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic Tom.Machine.Code

example (M : Mem) (hc : CodeAt M mpSubBase mpSubCode) (x s0 : BitVec 64) (keep : GRegs)
    (outp : Array String) (hkk : ∀ n ∈ keysG keep, 1 ≤ n ∧ n ≤ 31) (hrdk : 17 ∉ keysG keep) :
    Triple (At 0x80001f68#64 [(17, x), (8, s0)] M keep outp)
      (At 0x80001f6c#64 [(17, if x = 0#64 then 1#64 else 0#64), (8, s0)] M keep outp) := by
  have h := seqz_at (pc := 0x80001f68#64) (w := 0x0018b893#32) (rd := 17) (rs1 := 17)
    (L := [(17, x), (8, s0)]) (keep := keep) (outp := outp)
    (hc.word (a := (0x80001f68#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
    (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩
    (by decide) (Or.inr (by simp [keysG])) (by decide) (by simp [keysG]) hkk hrdk
  simpa [srcVal, lookupG, eraseG, Sail.BitVec.addInt] using h

end Tom.Machine
