import Tom.Machine.Kit.Auto
import Tom.Spec.Div2d

/-!
# Word arithmetic of the bit shifts (`mp_mod_2d`, `mp_mul_2d`)

Normal-form lemmas for the `*w` instructions and masks the two bit-shift
functions use, in the namespace `Tom.Machine.BitW`, and the libgcc results on small
non-negative operands (`sdiv_ofNat`, `srem_ofNat`).
-/

namespace Tom.Machine.BitW

open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- `__divdi3` on non-negative operands below `2^63`. -/
theorem sdiv_ofNat (x y : Nat) (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    (BitVec.ofNat 64 x).sdiv (BitVec.ofNat 64 y) = BitVec.ofNat 64 (x / y) := by
  have hmx : (BitVec.ofNat 64 x).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)]
    simp; omega
  have hmy : (BitVec.ofNat 64 y).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega)]
    simp; omega
  rw [BitVec.sdiv_eq, hmx, hmy]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_udiv, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show x / y < 2 ^ 64 from Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]

/-- `__moddi3` on non-negative operands below `2^63`. -/
theorem srem_ofNat (x y : Nat) (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    (BitVec.ofNat 64 x).srem (BitVec.ofNat 64 y) = BitVec.ofNat 64 (x % y) := by
  have hmx : (BitVec.ofNat 64 x).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)]
    simp; omega
  have hmy : (BitVec.ofNat 64 y).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega)]
    simp; omega
  rw [BitVec.srem_eq, hmx, hmy]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_umod, Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show x % y < 2 ^ 64 from Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega))]


theorem shl_ofNatW {w m : Nat} (x k : Nat) (hk : k < 2 ^ m) :
    Sail.shift_bits_left (BitVec.ofNat w x) (BitVec.ofNat m k) = BitVec.ofNat w (x * 2 ^ k) := by
  unfold Sail.shift_bits_left
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hk]

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

/-- `slliw t,x,3; subw t,t,x; slliw t,t,2`: `t = 28 * x` (`x * MP_DIGIT_BIT`). -/
theorem mul28W (x : Nat) (h : 28 * x < 2 ^ 31) :
    BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.extractLsb 31 0 (BitVec.signExtend 64
      (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.ofNat 32 x) 3#5)) -
        BitVec.ofNat 32 x))) 2#5) = BitVec.ofNat 64 (28 * x) := by
  rw [shl_ofNatW' _ _ 8 (by decide) (by decide), sext_ofNatW (by decide) _ (by omega),
    extractLsb_ofNatW _ (by omega), subw_ofNatW _ _ (by omega) (by omega), sext_ofNatW (by decide) _ (by omega),
    extractLsb_ofNatW _ (by omega), shl_ofNatW' _ _ 4 (by decide) (by decide),
    sext_ofNatW (by decide) _ (by omega)]
  congr 1; omega

/-- `snez` on an `ofNat` value. -/
theorem ite_ofNat_ne_zero {x : Nat} (hx : x < 2 ^ 64) :
    (if BitVec.ofNat 64 x = 0#64 then 0#64 else 1#64) = BitVec.ofNat 64 (if x = 0 then 0 else 1) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 x ≠ 0#64 := fun e => h (by
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
      simpa using this)
    simp [this, h]


/-- `mul28W` with the loaded word as the segment normal form spells it. -/
theorem mul28W' (x : Nat) (h : 28 * x < 2 ^ 31) :
    BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.extractLsb 31 0 (BitVec.signExtend 64
      (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.ofNat 32 (x % 4294967296)) 3#5)) -
        BitVec.ofNat 32 (x % 4294967296)))) 2#5) = BitVec.ofNat 64 (28 * x) := by
  rw [Nat.mod_eq_of_lt (show x < 4294967296 by omega)]; exact mul28W x h

/-- `li t,-1; sllw t,t,d; not t`: the mask `2^d - 1`. -/
theorem mask_ofNat (d : Nat) (hd : d < 32) :
    BitVec.signExtend 64 (Sail.shift_bits_left (4294967295#32) (BitVec.extractLsb 4 0 (BitVec.ofNat 32 (d % 4294967296)))) ^^^
      18446744073709551615#64 = BitVec.ofNat 64 (2 ^ d - 1) := by
  have he : BitVec.extractLsb 4 0 (BitVec.ofNat 32 (d % 4294967296)) = BitVec.ofNat 5 d := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb, BitVec.extractLsb']
  rw [he]
  unfold Sail.shift_bits_left
  rw [BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 5 by omega),
    show (4294967295#32 : BitVec 32) = BitVec.allOnes 32 by decide,
    show (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 by decide]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_signExtend, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_allOnes]
  by_cases h1 : i < d
  · simp [h1, hi, show i < 32 by omega]
  · by_cases h2 : i < 32
    · simp [h1, hi, h2]; omega
    · simp [h1, hi, h2]; omega

/-- The mask applied (`x & ((1 << d) - 1)`). -/
theorem mask_and (y d : Nat) (hd : d < 32) :
    (BitVec.signExtend 64 (Sail.shift_bits_left (4294967295#32) (BitVec.extractLsb 4 0 (BitVec.ofNat 32 (d % 4294967296)))) ^^^
      18446744073709551615#64) &&& BitVec.ofNat 64 y = BitVec.ofNat 64 (y % 2 ^ d) := by
  rw [mask_ofNat d hd]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 2 ^ d - 1 < 2 ^ 64 by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show d ≤ 64 by omega); omega),
    Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (show d ≤ 64 by omega)),
    Nat.mod_eq_of_lt (show y % 2 ^ d < 2 ^ 64 from Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (by omega)))]
open Tom

/-- A 5-bit shift amount from a small word. -/
theorem ext5 (d : Nat) (_hd : d < 32) :
    BitVec.extractLsb 4 0 (BitVec.ofNat 32 (d % 4294967296)) = BitVec.ofNat 5 d := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb, BitVec.extractLsb']

theorem or_mod_two_pow (a b n : Nat) : (a ||| b) % 2 ^ n = a % 2 ^ n ||| b % 2 ^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or]
  cases decide (i < n) <;> simp

/-- `sllw t,e,d; or t,t,r; and t,t,MP_MASK`: `((e << d) | r) & MP_MASK` (`mul2dDigit_c`). -/
theorem shl_or_mask (e r d : Nat) (hd : d < 28) (he : e < radix) (hr : r < 2 ^ d) :
    (BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.ofNat 32 (e % 4294967296))
        (BitVec.extractLsb 4 0 (BitVec.ofNat 32 (d % 4294967296)))) ||| BitVec.ofNat 64 r) &&&
      BitVec.ofNat 64 Layout.mpMask = BitVec.ofNat 64 (shlLo d e + r) := by
  have he' : e < 4294967296 := Nat.lt_trans he (by decide)
  rw [ext5 d (by omega), shl_ofNatW _ _ (show d < 2 ^ 5 by omega), Nat.mod_eq_of_lt he',
    show BitVec.ofNat 64 Layout.mpMask = 268435455#64 from rfl, BitVec.and_or_distrib_right,
    sext_and_mask28W rfl, and_mask28,
    ← mul2dDigit_c e r d 32 (by simp [Layout.digitBits]; omega) (by decide) hr, and_mpMask, radix,
    or_mod_two_pow, digitBits_eq,
    Nat.mod_mod_of_dvd _ (show 2 ^ 28 ∣ 2 ^ 32 from Nat.pow_dvd_pow 2 (by decide))]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show e * 2 ^ d % 268435456 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show r % 268435456 < 2 ^ 64 by omega)]
  have := Nat.or_lt_two_pow (n := 28) (x := e * 2 ^ d % 2 ^ 28) (y := r % 2 ^ 28) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide))
  rw [Nat.mod_eq_of_lt (Nat.lt_trans this (by decide))]

/-- `srlw t,e,28-d; and t,t,2^d-1`: the carry `shlHi d e` (`mul2dCarry_c`). -/
theorem srl_and_mask (e d : Nat) (hd : d ≤ 28) (he : e < radix) :
    BitVec.signExtend 64 (Sail.shift_bits_right (BitVec.ofNat 32 (e % 4294967296))
        (BitVec.extractLsb 4 0 (BitVec.ofNat 32 ((28 - d) % 4294967296)))) &&&
      BitVec.ofNat 64 (2 ^ d - 1) = BitVec.ofNat 64 (shlHi d e) := by
  have he' : e < 4294967296 := Nat.lt_trans he (by decide)
  rw [ext5 _ (by omega), srl32_ofNat _ _ (by omega), Nat.mod_eq_of_lt he', Nat.mod_eq_of_lt he']
  have hq : e / 2 ^ (28 - d) < 2 ^ 31 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_trans he (by decide))
  rw [signExtend_ofNat32 _ hq, show 28 - d = Layout.digitBits - d from rfl, ← shlHi_eq hd]
  have hl := shlHi_lt hd he
  have hp : 2 ^ d ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show shlHi d e < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 2 ^ d - 1 < 2 ^ 64 by omega),
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hl]
end Tom.Machine.BitW

namespace Tom.Machine

/-- `seg_step` with a closer `tac` for the register and log equations that
`sub_auto`/`regs_close` leave (`seg_stepu … using tac`). -/
syntax "seg_stepu " term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max
  " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term:max " using " tacticSeq : tactic
macro_rules
  | `(tactic| seg_stepu $bs $pc $lds $ks $kk [$ds,*] [$ps,*] [$es,*] $hc using $tac) => do
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
