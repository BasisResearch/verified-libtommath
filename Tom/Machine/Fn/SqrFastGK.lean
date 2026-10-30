import Tom.Machine.Kit.Shift
import Tom.Machine.Kit.Gen

/-!
# `s_mp_sqr_fast`'s segment rows: value lemmas

The column parity test `andi a5, s2, 1` at `70a8` (`ix & 1`): `Kit/Shift.lean`'s `and1_ofNat` as a
`seg_val` lemma, so the branch leaf is a compare of `ofNat`s; `slliw … 1` of a small `ofNat`.
-/

namespace Tom.Machine

attribute [seg_val] and1_ofNat

/-- `slliw rd, rs, 1` on a small `ofNat` (`pa = a->used + a->used` at `7058`, `7160`). -/
@[seg_val] theorem slliw1_ofNat (x : Nat) (h : x < 2 ^ 30) :
    BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.ofNat 32 (x % 4294967296)) 1#5) = BitVec.ofNat 64 (2 * x) := by
  rw [Nat.mod_eq_of_lt (show x < 4294967296 by omega),
    show (1#5 : BitVec 5) = BitVec.ofNat 5 1 from rfl, shl32_ofNat x 1 (by decide) (by omega),
    signExtend_ofNat32 _ (by omega), show x * 2 ^ 1 = 2 * x by omega]

end Tom.Machine
