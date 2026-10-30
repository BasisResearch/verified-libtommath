import Tom.Machine.Kit.Arith

/-!
# One-bit shifts of a digit in `Nat` form

The segment normal forms of the digit formulas of `mp_mul_2`
(`slliw`, `or`, `and` with `MP_MASK`) and `mp_div_2` (`srliw`, `slliw` by
`MP_DIGIT_BIT - 1`, `or`, `andi 1`), turned into `BitVec.ofNat 64` of the
`Nat` expressions of `Tom/Spec/Shift.lean`.
-/

namespace Tom.Machine

open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- `slliw` on a 32-bit `ofNat` value (no wrap). -/
theorem shl32_ofNat (x k : Nat) (hk : k < 32) (h : x * 2 ^ k < 2 ^ 32) :
    Sail.shift_bits_left (BitVec.ofNat 32 x) (BitVec.ofNat 5 k) = BitVec.ofNat 32 (x * 2 ^ k) := by
  unfold Sail.shift_bits_left
  apply BitVec.eq_of_toNat_eq
  have hx : x < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)) h
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show k < 32 by omega),
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt h]

/-- `x ||| r` for a bit `r` below an even `x`. -/
theorem or_bit_ofNat (x r : Nat) (hr : r ≤ 1) (h : 2 * x + r < 2 ^ 64) :
    BitVec.ofNat 64 (2 * x) ||| BitVec.ofNat 64 r = BitVec.ofNat 64 (2 * x + r) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 * x < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt h, show 2 * x = 2 ^ 1 * x by rfl, ← Nat.two_pow_add_eq_or_of_lt (by omega)]

/-- `mp_mul_2`'s digit: `((a[x] << 1) | r) & MP_MASK` (`slliw`, `or`, `and`). -/
theorem mul2_digit (x r : Nat) (hx : x < 268435456) (hr : r ≤ 1) :
    (BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.ofNat 32 (x % 4294967296)) 1#5) |||
        BitVec.ofNat 64 r) &&& 268435455#64 = BitVec.ofNat 64 ((2 * x + r) % 268435456) := by
  rw [Nat.mod_eq_of_lt (show x < 4294967296 by omega),
    show (1#5 : BitVec 5) = BitVec.ofNat 5 1 from rfl, shl32_ofNat x 1 (by decide) (by omega),
    signExtend_ofNat32 _ (by omega), show x * 2 ^ 1 = 2 * x by omega, or_bit_ofNat x r hr (by omega),
    and_mask28]

/-- `andi rd, rs, 1`. -/
theorem and1_ofNat (d : Nat) : BitVec.ofNat 64 d &&& 1#64 = BitVec.ofNat 64 (d % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (1 : Nat) % 2 ^ 64 = 2 ^ 1 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `x ||| 2^27 r` for `x < 2^27` and a bit `r`. -/
theorem or_top_ofNat (x r : Nat) (hx : x < 134217728) (hr : r ≤ 1) :
    BitVec.ofNat 64 x ||| BitVec.ofNat 64 (134217728 * r) = BitVec.ofNat 64 (x + 134217728 * r) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 134217728 * r < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show x + 134217728 * r < 2 ^ 64 by omega), Nat.or_comm,
    show (134217728 : Nat) = 2 ^ 27 by rfl, ← Nat.two_pow_add_eq_or_of_lt hx]
  omega

/-- `mp_div_2`'s digit: `(a[x] >> 1) | (r << (MP_DIGIT_BIT - 1))` (`srliw`, `slliw`, `or`). -/
theorem div2_digit (d r : Nat) (hd : d < 268435456) (hr : r ≤ 1) :
    BitVec.ofNat 64 (d % 4294967296 % 4294967296 / 2 % 4294967296) |||
        BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.ofNat 32 (r % 4294967296)) 27#5) =
      BitVec.ofNat 64 (d / 2 + 134217728 * r) := by
  rw [show d % 4294967296 % 4294967296 / 2 % 4294967296 = d / 2 by omega,
    Nat.mod_eq_of_lt (show r < 4294967296 by omega),
    show (27#5 : BitVec 5) = BitVec.ofNat 5 27 from rfl, shl32_ofNat r 27 (by decide) (by omega),
    Nat.mul_comm r, signExtend_ofNat32 _ (by omega)]
  exact or_top_ofNat _ _ (by omega) hr

end Tom.Machine
