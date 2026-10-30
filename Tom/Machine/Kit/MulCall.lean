import Tom.Machine.Fn.Libgcc
import Tom.Machine.Kit.Jal
import Tom.Machine.Kit.Frame

/-!
# A `jal __muldi3` inside a loop body

`muldi3_call`: from `At pc L m keep` with `jal ra, __muldi3` at `pc`, the
arguments `a0 = x`, `a1 = y` and the caller's live registers `Lk` in `L`, the
machine returns to `pc + 4` with `a0 = x * y`, `ra = pc + 4`, `Lk` and `keep`
kept and memory unchanged (`Api.Libgcc.Muldi3.StatementK` with the keep-set
`Lk ++ keep`, which must avoid `a0`–`a3`: `KeepOK mulWrites`). The caller
states the post's registers as any `L2` drawn from those (`hL2`). The digit
loops of `mp_mul_d`, `s_mp_mul_digs_fast` and `s_mp_sqr_fast` call it once
per product, between two segments.

`ofNat_mul_ofNat`, `zext_ofNat32`: the product and an `lwu` in `Nat` form.
-/

namespace Tom.Machine

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa Vsa.Sim Vsa.Logic
open Sail.ConcurrencyInterfaceV1.PreSail
open Tom.Machine.Api.Libgcc

theorem muldi3_call {pc : BitVec 64} {w : BitVec 32} {imm : BitVec 21} {base : Nat}
    {code : List (BitVec 32)} {L Lk L2 : GRegs} {m : Mem} {keep : GRegs} {outp : Array String}
    {x y : BitVec 64} (himg : Img m) (hc : CodeAt m base code) (hw : WordIn base code pc.toNat w = true)
    (hword : ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
      (w.extractLsb' 0 8)) = w)
    (hnotrvc : Sail.BitVec.extractLsb ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append
      (w.extractLsb' 8 8)).append (w.extractLsb' 0 8)) 1 0 = (0b11#2 : BitVec 2))
    (hdec : ∀ s : SequentialState RegisterType trivialChoiceSource,
      s.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) →
      s.regs.get? Register.cur_privilege =
        some ((Privilege.Machine) : RegisterType Register.cur_privilege) →
      s.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) →
      (ext_decode w).run s = .ok (instruction.JAL (imm, regidx.Regidx 0x01#5)) s)
    (hfetch : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0)
    (htgt : pc + sign_extend (m := 64) imm = muldi3Entry)
    (hra : (Sail.BitVec.addInt pc 4).toNat % 4 = 0)
    (hL : ∀ p ∈ (10, x) :: (11, y) :: Lk, p ∈ L)
    (hLk : ∀ n ∈ keysG ((10, x) :: (11, y) :: Lk), 2 ≤ n ∧ n ≤ 31)
    (hkk : ∀ n ∈ keysG keep, 2 ≤ n ∧ n ≤ 31)
    (hK : KeepOK mulWrites (Lk ++ keep))
    (hL2 : ∀ p ∈ L2, p ∈ (1, Sail.BitVec.addInt pc 4) :: (10, x * y) :: Lk) :
    Triple (At pc L m keep outp) (At (Sail.BitVec.addInt pc 4) L2 m keep outp) := by
  refine Triple.seq (jal_at (L' := (10, x) :: (11, y) :: Lk) (hc.word hw) hword hnotrvc hdec hfetch
    (by rw [htgt]; decide) hL hLk hkk) ?_
  rw [htgt]
  refine Triple.dimap (fun c h => h.reshape (L' := [(1, Sail.BitVec.addInt pc 4), (10, x), (11, y)])
      (K' := Lk ++ keep) ?_ ?_) (fun c h => h.reshape ?_ ?_) (Fn.Libgcc.Muldi3.correctK himg hra hK)
  · intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp
  · intro p hp; rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
    · exact List.mem_append_right _ h
  · intro p hp
    rcases List.mem_cons.1 (hL2 p hp) with rfl | hp'
    · simp
    rcases List.mem_cons.1 hp' with rfl | hp''
    · simp
    · exact List.mem_append_right _ (List.mem_append_left _ hp'')
  · intro p hp; exact List.mem_append_right _ (List.mem_append_right _ hp)

/-- **A call by `jal`** into a callee contract stated from its entry with its
own register list `L0` and keep-set `K`, both drawn from the return address,
the pins `Larg ⊆ L` carried across the `jal`, and the caller's `keep`. -/
theorem jal_call {pc entry : BitVec 64} {w : BitVec 32} {imm : BitVec 21} {base : Nat}
    {code : List (BitVec 32)} {L Larg L0 K : GRegs} {m : Mem} {keep : GRegs} {outp : Array String}
    {Q : Vsa.Machine.Config → Prop} (hc : CodeAt m base code) (hw : WordIn base code pc.toNat w = true)
    (hword : ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
      (w.extractLsb' 0 8)) = w)
    (hnotrvc : Sail.BitVec.extractLsb ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append
      (w.extractLsb' 8 8)).append (w.extractLsb' 0 8)) 1 0 = (0b11#2 : BitVec 2))
    (hdec : ∀ s : SequentialState RegisterType trivialChoiceSource,
      s.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) →
      s.regs.get? Register.cur_privilege =
        some ((Privilege.Machine) : RegisterType Register.cur_privilege) →
      s.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) →
      (ext_decode w).run s = .ok (instruction.JAL (imm, regidx.Regidx 0x01#5)) s)
    (hfetch : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0)
    (htgt : pc + sign_extend (m := 64) imm = entry) (hal : entry.toNat % 4 = 0)
    (hL : ∀ p ∈ Larg, p ∈ L) (hLk : ∀ n ∈ keysG Larg, 2 ≤ n ∧ n ≤ 31)
    (hkk : ∀ n ∈ keysG keep, 2 ≤ n ∧ n ≤ 31)
    (hL0 : ∀ p ∈ L0, p ∈ ((1, Sail.BitVec.addInt pc 4) :: Larg) ++ keep)
    (hK : ∀ p ∈ K, p ∈ ((1, Sail.BitVec.addInt pc 4) :: Larg) ++ keep)
    (hcallee : Triple (At entry L0 m K outp) Q) :
    Triple (At pc L m keep outp) Q := by
  refine Triple.seq (jal_at (L' := Larg) (hc.word hw) hword hnotrvc hdec hfetch (by rw [htgt]; exact hal)
    hL hLk hkk) ?_
  rw [htgt]
  exact Triple.lmap (fun c h => h.reshape hL0 hK) hcallee

/-- `Img` through any change off the text section. -/
theorem Img.of_text {m M : Mem} (h : Img m)
    (hs : ∀ x, Code.textBase ≤ x → x < Code.textBase + Code.textLen → M[x]? = m[x]?) : Img M :=
  Img.reads (ρ := fun _ : Unit => textIv) (r := ()) (Iv.sub_self _) m M
    (fun x hx => by simp only [InAny, Iv.In, textIv, or_false] at hx; exact hs x hx.1 hx.2) h

/-- An `lwu` of a word below `2^32`. -/
theorem zext32_ofNat (x : Nat) (h : x < 2 ^ 32) :
    zero_extend (m := 64) (BitVec.ofNat 32 x) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp [zero_extend, Sail.BitVec.zeroExtend, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)]

theorem ofNat_mul_ofNat (x y : Nat) : BitVec.ofNat 64 x * BitVec.ofNat 64 y = BitVec.ofNat 64 (x * y) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]

/-- Sign extension of a word, negative or not, as one `ofNat` (no case split:
the sign bit is `d % 2^32 / 2^31`). -/
theorem sext_ofNatW_div {w : Nat} (hw : w = 32) (d : Nat) :
    BitVec.signExtend 64 (BitVec.ofNat w d) =
      BitVec.ofNat 64 (d % 4294967296 + d % 4294967296 / 2147483648 * 18446744069414584320) := by
  apply BitVec.eq_of_toNat_eq
  rw [sext_toNatW hw, BitVec.toNat_ofNat]
  subst hw
  rw [BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceSub, decide_eq_true_eq]
  split <;> omega

/-- `sraiw` on a non-negative word. -/
theorem sra32_ofNatW {w : Nat} (hw : w = 32) (d k : Nat) (h : d % 4294967296 < 2 ^ 31) (hk : k < 32) :
    shift_bits_right_arith (BitVec.ofNat w d) (BitVec.ofNat 5 k) = BitVec.ofNat w (d % 4294967296 / 2 ^ k) := by
  subst hw
  unfold shift_bits_right_arith
  apply BitVec.eq_of_toNat_eq
  have hm : (BitVec.ofNat 32 d).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega
  rw [BitVec.toNat_sshiftRight_of_msb_false hm]
  simp [Sail.BitVec.toNatInt, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show k < 32 by omega)]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide)))]

/-- `slliw` on an `ofNat` word. -/
theorem shl32_ofNatW {w : Nat} (x k : Nat) :
    Sail.shift_bits_left (BitVec.ofNat w x) (BitVec.ofNat 5 k) = BitVec.ofNat w (x * 2 ^ (k % 32)) := by
  unfold Sail.shift_bits_left
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]

theorem and1_ofNat (x : Nat) : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  rw [show (1 : Nat) % 2 ^ 64 = 2 ^ 1 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `addiw rd, rs, -1` on a small `ofNat` (`b->used - 1`, all ones for `0`). -/
theorem sext_m1 {w : Nat} (hw : w = 32) (x : Nat) (h : x < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat w ((x + 18446744073709551615) % 4294967296)) =
      BitVec.ofNat 64 (x + 18446744073709551615) := by
  subst hw
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · decide
  · rw [signExtend_ofNatW rfl _ (by omega)]
    apply BitVec.eq_of_toNat_eq; simp only [toNat_ofNat']; omega

/-- `subw rd, 1, rs` on a small `ofNat` (`1 - b->used`). -/
theorem sext_1m {w : Nat} (hw : w = 32) (x : Nat) (h : x < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat w (4294967296 - x % 4294967296 % 4294967296 + 1)) =
      BitVec.ofNat 64 (18446744073709551617 - x) := by
  rw [sext_ofNatW_div hw]
  apply BitVec.eq_of_toNat_eq; simp only [toNat_ofNat']
  rcases Nat.lt_or_ge x 2 with hx | hx
  · have e : (4294967296 - x % 4294967296 % 4294967296 + 1) % 4294967296 = 1 - x := by omega
    rw [e, show (1 - x) / 2147483648 = 0 by omega]; omega
  · have e : (4294967296 - x % 4294967296 % 4294967296 + 1) % 4294967296 = 4294967297 - x := by omega
    rw [e, show (4294967297 - x) / 2147483648 = 1 by omega]; omega

end Tom.Machine

namespace Tom.Machine

/-- A branch-guard leaf that `tom_facts` leaves bare (an empty block before the
branch, so no `TermFacts` wrapper for `leaf_nf` to unfold): the register
lookups, the loaded values `eqs`, `val_nf`, the compare lemmas, `omega`. -/
syntax "guard_auto" " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| guard_auto [$ds,*] [$es,*]) => `(tactic|
      (try simp only [$ds,*]
       simp only [Vsa.Sim.guardB, Vsa.Sim.eaddrM, Vsa.Sim.srcVal, Vsa.Sim.lookupG,
         Vsa.Sim.runGM, Vsa.Sim.stepGM, Vsa.Sim.stepLdsM, Vsa.Sim.wvalM, Vsa.Sim.eraseG,
         Vsa.Sim.bytesVal, Vsa.Sim.ldsRunM, ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff,
         Option.getD_some, List.headD, List.tail_cons, Tom.Machine.writeLog_nil, List.append_nil,
         Sail.BitVec.addInt, LeanRV64DExecutable.Functions.sign_extend,
         Sail.BitVec.signExtend, Sail.BitVec.extractLsb, Tom.Machine.bv_append_eq, BitVec.reduceAppend,
         BitVec.reduceSignExtend, BitVec.signExtend_eq, Tom.Machine.toNat_ofNat_add,
         Tom.Machine.toNat_ofNat']
       try simp only [$es,*]
       try val_nf [$es,*]
       all_goals simp (disch := omega) only [Tom.Machine.ofNat_add_ofNat, Tom.Machine.blt_ofNat,
         Tom.Machine.bltu_ofNat', Tom.Machine.bgeu_ofNat', Tom.Machine.bge_zero_ofNat, Tom.Machine.bge_ofNat,
         Tom.Machine.bge_zero_sextW, Tom.Machine.ofNat_beq', bne, decide_eq_true_eq, decide_eq_false_iff_not,
         Bool.not_eq_true', Bool.not_eq_false', beq_self_eq_true, Bool.not_true]
       all_goals omega))

/-- `seg_step` for chains that compute negative words (`addiw`/`subw` below
zero): after `val_nf`, sign-extended words become one `ofNat` by
`sext_ofNatW_div`, so `regs_close` closes them by `omega`
(`seg_stepx chain pc lds ks kk [defs] [post] [eqs] hc`). -/
syntax "seg_stepx " term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max
  " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term:max : tactic
macro_rules
  | `(tactic| seg_stepx $bs $pc $lds $ks $kk [$ds,*] [$ps,*] [$es,*] $hc) => do
      let b ← `(Lean.Parser.Tactic.simpLemma| $bs:term)
      let l1 : Array (Lean.TSyntax ``Lean.Parser.Tactic.simpLemma) := #[b] ++ ds.getElems
      let l2 := l1 ++ ps.getElems
      `(tactic|
        (refine Tom.Machine.seg_at' $bs (pc1 := $pc) $lds $ks $kk ?_ ?_ ?_ ?_
         · tom_facts $hc
           all_goals first | leaf_auto [$ds,*] [$es,*] | guard_auto [$ds,*] [$es,*]
         · seg_nfo [$l1,*]
           try (try val_nf [$es,*]
                exact Tom.Machine.ret_target' _ (by assumption))
         · (try simp only [$l2,*]
            simp only [Tom.Machine.SubL]
            seg_nfo [$l2,*]
            try simp only [Option.some.injEq]
            try val_nf [$es,*]
            try simp (disch := omega) only [Tom.Machine.sext_m1, Tom.Machine.sext_1m, Tom.Machine.sra32_ofNatW,
              Tom.Machine.shl32_ofNatW, Tom.Machine.ofNat_add_ofNat, Tom.Machine.extractLsb_ofNat32',
              Tom.Machine.signExtend_ofNatW, Nat.reducePow, Nat.reduceMod]
            try simp (disch := omega) only [Tom.Machine.sext_ofNatW_div]
            try regs_close)
         · seg_nfo [$l1,*]
           try val_nf [$es,*]
           try simp (disch := omega) only [Tom.Machine.sext_m1, Tom.Machine.sext_1m, Tom.Machine.sra32_ofNatW,
              Tom.Machine.shl32_ofNatW, Tom.Machine.ofNat_add_ofNat, Tom.Machine.extractLsb_ofNat32',
              Tom.Machine.signExtend_ofNatW, Nat.reducePow, Nat.reduceMod]
           try simp (disch := omega) only [Tom.Machine.sext_ofNatW_div]
           try regs_close))

end Tom.Machine
