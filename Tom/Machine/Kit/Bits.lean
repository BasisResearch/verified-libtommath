import Tom.Machine.Kit.Arith

/-!
# Masks, unsigned compares and subtraction in `Nat` form

More of `Kit/Arith.lean`'s conversions from the segment normal form to
`BitVec.ofNat 64` of a `Nat` expression: `andi` with `15` and `-16`, the
unsigned compares `bltu`/`bgeu`, and `sub`.
-/

namespace Tom.Machine

open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- `andi rd, rs, 15`. -/
theorem and15_ofNat (x : Nat) : BitVec.ofNat 64 x &&& 15#64 = BitVec.ofNat 64 (x % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  rw [show (15 : Nat) % 2 ^ 64 = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `andi rd, rs, -16`. -/
theorem andm16_ofNat (x : Nat) : BitVec.ofNat 64 x &&& 18446744073709551600#64 =
    BitVec.ofNat 64 (x % 2 ^ 64 - x % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  have hy : x % 2 ^ 64 - x % 16 = ((x % 2 ^ 64) >>> 4) <<< 4 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; omega
  rw [show (18446744073709551600 : Nat) % 2 ^ 64 = (2 ^ 60 - 1) <<< 4 by decide, hy,
    Nat.mod_eq_of_lt (a := ((x % 2 ^ 64) >>> 4) <<< 4) (by rw [← hy]; omega)]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases h4 : 4 ≤ i
  · rw [show 4 + (i - 4) = i by omega]
    by_cases h64 : i < 64
    · simp [h4, show i - 4 < 60 by omega]
    · have : (x % 2 ^ 64).testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide))
          (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [h4]

/-- `bltu` on `ofNat` values. -/
theorem ltu_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    zopz0zI_u (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp [zopz0zI_u, Sail.BitVec.toNatInt, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- `bgeu` on `ofNat` values. -/
theorem geu_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    zopz0zKzJ_u (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (b ≤ a) := by
  simp [zopz0zKzJ_u, Sail.BitVec.toNatInt, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- `sub` on `ofNat` values without borrow. -/
theorem sub_ofNat (a b : Nat) (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- `bnez` on an `ofNat` value. -/
theorem bne_zero_ofNat (a : Nat) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a != 0#64) = decide (a ≠ 0) := by
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 a ≠ 0#64 := by
      intro e; have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this; simp at this; omega
    simp [this, h]

/-- `zext.b` (`andi rd, rs, 255`) on a byte. -/
theorem and255_ofNat (c : Nat) (hc : c < 256) : BitVec.ofNat 64 c &&& 255#64 = BitVec.ofNat 64 c := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  rw [show (255 : Nat) % 2 ^ 64 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `or` of a value and its disjoint left shift. -/
theorem or_shl_ofNat (a k : Nat) (ha : a < 2 ^ k) (h : a + a * 2 ^ k < 2 ^ 64) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 (a * 2 ^ k) = BitVec.ofNat 64 (a + a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a * 2 ^ k < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt h, Nat.or_comm,
    show a * 2 ^ k = 2 ^ k * a from Nat.mul_comm _ _, ← Nat.two_pow_add_eq_or_of_lt ha]
  omega

end Tom.Machine
