import Tom.Machine.Kit.Gen
import Tom.Machine.Kit.BitW

/-! `mp_mod_2d`'s mask `2^d - 1` applied to the loaded digit as `seg_go` leaves it (row `x2`
of `experiments/segs/mmod2dig.rows.json`): `BitW.mask_and` with the digit's `% 2^32`. -/

namespace Tom.Machine.Fn.MpMod2dIG

open LeanRV64DExecutable LeanRV64DExecutable.Functions

theorem mask_and_nf (y d : Nat) (hd : d < 32) (hy : y < 4294967296) :
    (BitVec.signExtend 64 (Sail.shift_bits_left (4294967295#32) (BitVec.extractLsb 4 0
      (BitVec.ofNat 32 (d % 4294967296)))) ^^^ 18446744073709551615#64) &&& BitVec.ofNat 64 (y % 4294967296) =
      BitVec.ofNat 64 (y % 2 ^ d) := by
  rw [Nat.mod_eq_of_lt hy]; exact BitW.mask_and y d hd

end Tom.Machine.Fn.MpMod2dIG
