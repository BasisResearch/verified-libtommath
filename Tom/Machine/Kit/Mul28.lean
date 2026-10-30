import Tom.Machine.Kit.GenX_seg5a

/-!
# `MP_DIGIT_BIT * k` as the compiler computes it: a value lemma for the segment rows

`slliw a, k, 3`, `subw a, a, k`, `slliw a, a, 2` (`28 k = (8 k - k) 4`, `mp_reduce`'s
`mp_mod_2d(x, MP_DIGIT_BIT * (um + 1), x)` at `62ac`): `BitVec.ofNat 64 (28 k)` for `28 k < 2^31`.
-/

namespace Tom.Machine

open LeanRV64DExecutable LeanRV64DExecutable.Functions

@[seg_val] theorem mul28_slliw (u : Nat) (hu : 28 * u < 2 ^ 31) :
    BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.extractLsb 31 0 (BitVec.signExtend 64
      (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.ofNat 32 (u % 4294967296)) 3#5)) -
        BitVec.ofNat 32 (u % 4294967296)))) 2#5) = BitVec.ofNat 64 (28 * u) := by
  have h1 : Sail.shift_bits_left (BitVec.ofNat 32 (u % 4294967296)) 3#5 = BitVec.ofNat 32 (8 * u) := by
    unfold Sail.shift_bits_left; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod]; omega
  rw [h1, signExtend_ofNat32 _ (by omega), extractLsb_ofNat32 _ (by omega)]
  have h2 : BitVec.ofNat 32 (8 * u) - BitVec.ofNat 32 (u % 4294967296) = BitVec.ofNat 32 (7 * u) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [h2, signExtend_ofNat32 _ (by omega), extractLsb_ofNat32 _ (by omega)]
  have h3 : Sail.shift_bits_left (BitVec.ofNat 32 (7 * u)) 2#5 = BitVec.ofNat 32 (28 * u) := by
    unfold Sail.shift_bits_left; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod]; omega
  rw [h3, signExtend_ofNat32 _ (by omega)]

end Tom.Machine
