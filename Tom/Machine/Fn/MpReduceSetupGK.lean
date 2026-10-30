import Tom.Machine.Kit.Gen
import Tom.Machine.Kit.BitW

/-! `mp_reduce_setup`'s exponent (`63b8`–`63c0`: `slliw a1,a5,3; subw a1,a1,a5; slliw a1,a1,3`):
`56 b->used` for an `int` product. -/

namespace Tom.Machine.Fn.MpReduceSetupG

@[seg_val] theorem mul56 (u : Nat) (h : 56 * u < 2 ^ 31) :
    BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.extractLsb 31 0 (BitVec.signExtend 64
      (BitVec.extractLsb 31 0 (BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.ofNat 32 (u % 4294967296)) 3#5)) -
        BitVec.ofNat 32 (u % 4294967296)))) 3#5) = BitVec.ofNat 64 (56 * u) := by
  rw [Nat.mod_eq_of_lt (show u < 4294967296 by omega), show (3#5 : BitVec 5) = BitVec.ofNat 5 3 from rfl,
    BitW.shl_ofNatW _ _ (by decide), signExtend_ofNat32 _ (by omega), BitW.extractLsb_ofNatW _ (by omega)]
  rw [show (BitVec.ofNat (31 - 0 + 1) (u * 2 ^ 3) - BitVec.ofNat 32 u : BitVec 32) = BitVec.ofNat 32 (u * 2 ^ 3 - u)
    from BitW.subw_ofNatW _ _ (by omega) (by omega), signExtend_ofNat32 _ (by omega), BitW.extractLsb_ofNatW _ (by omega)]
  rw [show (Sail.shift_bits_left (BitVec.ofNat (31 - 0 + 1) (u * 2 ^ 3 - u)) (BitVec.ofNat 5 3) : BitVec 32) =
    BitVec.ofNat 32 ((u * 2 ^ 3 - u) * 2 ^ 3) from BitW.shl_ofNatW _ _ (by decide), signExtend_ofNat32 _ (by omega)]
  congr 1; omega

end Tom.Machine.Fn.MpReduceSetupG
