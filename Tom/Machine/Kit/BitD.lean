import Tom.Machine.Kit.BitW

/-!
# The bit loop of `mp_div_2d` on words

`srlw t,e,d; sllw r,r,28-d; or t,t,r` is `e / 2^d + r 2^(28 - d)` (`div2dDigit_c`),
and `and r,e,2^d-1` is `e mod 2^d`, for a digit `e < radix` and a carry `r < 2^d`.
-/

namespace Tom.Machine.BitD

open Tom

/-- `e & (2^d - 1)` on 64-bit words. -/
theorem and_mask (e d : Nat) (hd : d < 64) (he : e < 2 ^ 64) :
    BitVec.ofNat 64 e &&& BitVec.ofNat 64 (2 ^ d - 1) = BitVec.ofNat 64 (e % 2 ^ d) := by
  have hp : 2 ^ d ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt (show 2 ^ d - 1 < 2 ^ 64 by omega), Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hp)]

/-- `srlw t,e,d; sllw r,r,28-d; or t,t,r`: the shifted digit (`div2dDigit_c`). -/
theorem srl_or_sll (e r d : Nat) (hd : d < 28) (he : e < radix) (hr : r < 2 ^ d) :
    BitVec.signExtend 64 (Sail.shift_bits_right (BitVec.ofNat 32 (e % 4294967296))
        (BitVec.extractLsb 4 0 (BitVec.ofNat 32 (d % 4294967296)))) |||
      BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.ofNat 32 (r % 4294967296))
        (BitVec.extractLsb 4 0 (BitVec.ofNat 32 ((28 - d) % 4294967296)))) =
      BitVec.ofNat 64 (e / 2 ^ d + r * 2 ^ (28 - d)) := by
  have he' : e < 4294967296 := Nat.lt_trans he (by decide)
  have hp : 2 ^ d ≤ 2 ^ 28 := Nat.pow_le_pow_right (by decide) (by omega)
  have hr' : r < 4294967296 := by omega
  have hc : 2 ^ d * 2 ^ (28 - d) = 2 ^ 28 := by rw [← Nat.pow_add]; congr 1; omega
  have hq : r * 2 ^ (28 - d) < 2 ^ 28 := by
    have : (r + 1) * 2 ^ (28 - d) ≤ 2 ^ d * 2 ^ (28 - d) := Nat.mul_le_mul_right _ hr
    rw [Nat.succ_mul, hc] at this; have := Nat.two_pow_pos (28 - d); omega
  rw [BitW.ext5 _ (by omega), BitW.ext5 _ (by omega), srl32_ofNat _ _ (by omega), Nat.mod_eq_of_lt he',
    Nat.mod_eq_of_lt he', Nat.mod_eq_of_lt hr', BitW.shl_ofNatW _ _ (show 28 - d < 2 ^ 5 by omega),
    signExtend_ofNat32 _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_trans he (by decide))),
    signExtend_ofNat32 _ (by omega)]
  have ⟨h1, h2⟩ := div2dDigit_c e r d (by simp only [Layout.digitBits]; omega) he hr
  simp only [Layout.digitBits, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq] at h1 h2
  have hl : e / 2 ^ d < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt (show r * 2 ^ (28 - d) < 2 ^ 64 by omega), h1]
  exact (Nat.mod_eq_of_lt (Nat.lt_trans h2 (by decide))).symm

/-- `li t,1; sllw t,t,d`: `2^d`. -/
theorem sll_one (d : Nat) (hd : d < 31) :
    BitVec.signExtend 64 (Sail.shift_bits_left (1#32) (BitVec.extractLsb 4 0 (BitVec.ofNat 32 (d % 4294967296)))) =
      BitVec.ofNat 64 (2 ^ d) := by
  have hp : 2 ^ d < 2 ^ 31 := Nat.pow_lt_pow_right (by decide) hd
  rw [BitW.ext5 _ (by omega), show (1#32 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
    BitW.shl_ofNatW _ _ (show d < 2 ^ 5 by omega), Nat.one_mul, signExtend_ofNat32 _ hp]

/-- `addi t,y,-1` on a positive word. -/
theorem add_m1 (y : Nat) (h1 : 1 ≤ y) (h2 : y < 2 ^ 64) :
    BitVec.ofNat 64 y + 18446744073709551615#64 = BitVec.ofNat 64 (y - 1) := by
  rw [show (18446744073709551615#64 : BitVec 64) = BitVec.ofNat 64 18446744073709551615 from rfl,
    ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show y + 18446744073709551615 = (y - 1) + 2 ^ 64 by omega, Nat.add_mod_right]

/-- `addw t,t,bits; addiw t,t,-1` after `28 x`: the exponent `28 x + bits - 1`. -/
theorem norm_exp (x bits : Nat) (hx : 28 * x + 28 < 2 ^ 31) (hb : bits < 28) (h1 : 1 ≤ 28 * x + bits) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (BitVec.extractLsb 31 0
      (BitVec.ofNat 64 (28 * x)) + BitVec.ofNat 32 (bits % 4294967296)) + 18446744073709551615#64)) =
      BitVec.ofNat 64 (28 * x + bits - 1) := by
  rw [BitW.extractLsb_ofNatW _ (by omega), Nat.mod_eq_of_lt (show bits < 4294967296 by omega)]
  rw [show (BitVec.ofNat (31 - 0 + 1) (28 * x) + BitVec.ofNat 32 bits : BitVec 32) = BitVec.ofNat 32 (28 * x + bits)
    from (BitVec.ofNat_add _ _).symm, signExtend_ofNat32 _ (by omega), add_m1 _ h1 (by omega),
    BitW.extractLsb_ofNatW _ (by omega)]
  exact signExtend_ofNat32 _ (by omega)

/-- `addiw t,bits,-1`: the counter `bits - 1` (`-1` for `bits = 0`). -/
theorem addiw_m1 (bits : Nat) (hb : bits < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 ((bits + 18446744073709551615) % 4294967296)) =
      if bits = 0 then 18446744073709551615#64 else BitVec.ofNat 64 (bits - 1) := by
  split
  · subst_vars
    rw [show (0 + 18446744073709551615) % 4294967296 = 4294967295 by rfl]
    apply BitVec.eq_of_toNat_eq
    simp
  · rw [show (bits + 18446744073709551615) % 4294967296 = bits - 1 by omega]
    exact signExtend_ofNat32 _ (by omega)

end Tom.Machine.BitD
