import Tom.Machine.Kit.Gen
import Tom.Machine.Kit.BitD

/-! `mp_montgomery_calc_normalization`'s values: the exponent `28 (b->used - 1) + bits - 1`
(`58f0`–`590c`, `BitW.mul28W'`, `BitD.norm_exp`) and the loop counter `s2 = xw k` (the C's `x = k - 1`
as a 64-bit word): its `addiw s2, s2, 1` (`xw_inc`, `xw_add1`) and its start values. -/

namespace Tom.Machine.Fn.MontNormG

@[seg_val] theorem exp_val (ub r : Nat) (h1 : 1 < ub) (h2 : 28 * ub < 2 ^ 31) (h3 : r < 28) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (BitVec.extractLsb 31 0
      (BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.extractLsb 31 0 (BitVec.signExtend 64
        (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (Sail.shift_bits_left
          (BitVec.ofNat 32 ((ub + 18446744073709551615) % 4294967296)) 3#5)) -
          BitVec.ofNat 32 ((ub + 18446744073709551615) % 4294967296)))) 2#5)) +
        BitVec.ofNat 32 (r % 4294967296)) + 18446744073709551615#64)) =
      BitVec.ofNat 64 (28 * (ub - 1) + r - 1) := by
  rw [show (ub + 18446744073709551615) % 4294967296 = (ub - 1) % 4294967296 by omega,
    BitW.mul28W' _ (by omega), BitD.norm_exp _ _ (by omega) h3 (by omega)]

/-- The loop counter `x = k - 1` as a 64-bit word (`xw 0 = -1`). -/
def xw (k : Nat) : BitVec 64 := BitVec.ofNat 64 (k + 18446744073709551615)

@[seg_val] theorem xw_add1 (k : Nat) : xw (k + 1) = BitVec.ofNat 64 k := by
  unfold xw; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [show k + 1 + 18446744073709551615 = k + 2 ^ 64 by omega, Nat.add_mod_right]

theorem xw_succ (k : Nat) : xw k + 1#64 = BitVec.ofNat 64 k := by
  unfold xw; rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add,
    show k + 18446744073709551615 + 1 = k + 1 + 18446744073709551615 by omega]
  exact xw_add1 k

@[seg_val] theorem xw_inc (k : Nat) (h : k < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.extractLsb 31 0 (xw k + 1#64)) = BitVec.ofNat 64 k := by
  rw [xw_succ, BitW.extractLsb_ofNatW _ (by omega)]; exact signExtend_ofNat32 _ h

end Tom.Machine.Fn.MontNormG
