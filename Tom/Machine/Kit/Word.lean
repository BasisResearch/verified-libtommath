import Tom.Machine.Kit.Auto
import Vsa.Sim.BlockMem

/-!
# 32-bit word arithmetic (`slliw`, `subw`) on `ofNat` values, and `seg_stepw`

The segment normal form of a chain of `*w` instructions is a nest of
`signExtend 64`, `extractLsb 31 0` and `Sail.shift_bits_left` at the width
`31 - 0 + 1`. The lemmas here are width-polymorphic (`w`, with `w = 32` a
`decide` side condition where it matters) and free of `%`, so their side
conditions are plain `omega` bounds (`omega` is incomplete on the `% 2^32`
atoms the `Kit/Arith.lean` forms leave).

`mul28W`: `slliw t,x,3; subw t,t,x; slliw t,t,2` is `28 * x`
(`x * MP_DIGIT_BIT` in `mp_count_bits`, `mp_cnt_lsb`); `slt_half`:
`sraiw t,u,1; slt t,c,t` is `c < u / 2` (`mp_reduce_is_2k_l`).

`seg_stepw … using tac`: `seg_step` whose register and write-log equations
left open by `sub_auto`/`regs_close` are closed by `tac`.
-/

namespace Tom.Machine

open LeanRV64DExecutable LeanRV64DExecutable.Functions

theorem shl_ofNatW {w m : Nat} (x k : Nat) (hk : k < 2 ^ m) :
    Sail.shift_bits_left (BitVec.ofNat w x) (BitVec.ofNat m k) = BitVec.ofNat w (x * 2 ^ k) := by
  unfold Sail.shift_bits_left
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hk]

/-- `shl_ofNatW` with the multiplier a literal `c` (`omega` treats `x * 2 ^ k` as an atom). -/
theorem shl_ofNatW' {w m : Nat} (x k c : Nat) (hk : k < 2 ^ m) (hc : 2 ^ k = c) :
    Sail.shift_bits_left (BitVec.ofNat w x) (BitVec.ofNat m k) = BitVec.ofNat w (x * c) := by
  rw [shl_ofNatW x k hk, hc]

theorem sext_ofNatW {w : Nat} (hw : w = 32) (d : Nat) (h : d < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat w d) = BitVec.ofNat 64 d := by
  subst hw; exact signExtend_ofNat32 d h

theorem subw_ofNatW {w : Nat} (x y : Nat) (h : y ≤ x) (hx : x < 2 ^ w) :
    BitVec.ofNat w x - BitVec.ofNat w y = BitVec.ofNat w (x - y) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt (show y < 2 ^ w by omega)]
  rw [show 2 ^ w - y + x = (x - y) + 2 ^ w by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem extractLsb_ofNatW (x : Nat) (h : x < 2 ^ 32) :
    (BitVec.ofNat 64 x).extractLsb 31 0 = BitVec.ofNat (31 - 0 + 1) x := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega), Nat.mod_eq_of_lt h]

/-- `slliw t,x,3; subw t,t,x; slliw t,t,2`: `t = 28 * x`. -/
theorem mul28W (x : Nat) (h : 28 * x < 2 ^ 31) :
    BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.extractLsb 31 0 (BitVec.signExtend 64
      (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.ofNat 32 x) 3#5)) -
        BitVec.ofNat 32 x))) 2#5) = BitVec.ofNat 64 (28 * x) := by
  rw [shl_ofNatW' _ _ 8 (by decide) (by decide), sext_ofNatW (by decide) _ (by omega),
    extractLsb_ofNatW _ (by omega), subw_ofNatW _ _ (by omega) (by omega), sext_ofNatW (by decide) _ (by omega),
    extractLsb_ofNatW _ (by omega), shl_ofNatW' _ _ 4 (by decide) (by decide),
    sext_ofNatW (by decide) _ (by omega)]
  congr 1; omega

/-- `sraiw t,u,1` on a non-negative word. -/
theorem sraw1_ofNat (u : Nat) (hu : u < 2 ^ 31) :
    shift_bits_right_arith (BitVec.ofNat 32 (u % 4294967296)) (1#5) = BitVec.ofNat 32 (u / 2) := by
  unfold shift_bits_right_arith
  rw [Nat.mod_eq_of_lt (by omega)]
  have hmsb : (BitVec.ofNat 32 u).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show u < 2 ^ 32 by omega)]
    simp; omega
  rw [show (Sail.BitVec.toNatInt (1#5)).toNat = 1 from rfl]
  rw [BitVec.sshiftRight_eq_of_msb_false hmsb]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show u < 2 ^ 32 by omega)]
  omega

/-- An `slt`/`sltu` result. -/
theorem bit_val (p : Bool) :
    zero_extend (m := 64) (bool_to_bit p) = BitVec.ofNat 64 (if p then 1 else 0) := by
  cases p <;> rfl

/-- `sraiw t,u,1; slt t,c,t`: `c < u / 2`. -/
theorem slt_half (c u : Nat) (hc : c < 2 ^ 31) (hu : u < 2 ^ 31) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_s (BitVec.ofNat 64 c)
      (BitVec.signExtend 64 (shift_bits_right_arith (BitVec.ofNat 32 (u % 4294967296)) (1#5))))) =
      BitVec.ofNat 64 (if c < u / 2 then 1 else 0) := by
  rw [sraw1_ofNat u hu, signExtend_ofNat32 _ (by omega), blt_ofNat _ _ (by omega) (by omega), bit_val]
  simp

/-- `seg_step` with a closer `tac` for the register and log equations it leaves. -/
syntax "seg_stepw " term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max
  " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term:max " using " tacticSeq : tactic
macro_rules
  | `(tactic| seg_stepw $bs $pc $lds $ks $kk [$ds,*] [$ps,*] [$es,*] $hc using $tac) => do
      let b ← `(Lean.Parser.Tactic.simpLemma| $bs:term)
      let l1 : Array (Lean.TSyntax ``Lean.Parser.Tactic.simpLemma) := #[b] ++ ds.getElems
      let l2 := l1 ++ ps.getElems
      `(tactic|
        (refine Tom.Machine.seg_at' $bs (pc1 := $pc) $lds $ks $kk ?_ ?_ ?_ ?_
         · tom_facts $hc
           all_goals leaf_auto [$ds,*] [$es,*]
         · seg_nfo [$l1,*]
           try (try val_nf [$es,*]
                exact Tom.Machine.ret_target' _ (by assumption))
         · sub_auto [$l2,*] [$es,*]
           all_goals ($tac)
         · seg_nfo [$l1,*]
           try val_nf [$es,*]
           try regs_close
           all_goals ($tac)))

end Tom.Machine
