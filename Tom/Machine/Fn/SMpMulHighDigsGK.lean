import Tom.Machine.Kit.Gen

/-! `s_mp_mul_high_digs`'s `subw s8, s3, s8` (`digs - a->used`, `69e0 + 0xc4`): a word
difference that may be `-1` (`a->used = digs + 1`), as the 64-bit value
`digs + 2^64 - a->used` (its residue is `digs - a->used` or `2^64 - 1`). -/

namespace Tom.Machine.Fn.SMpMulHighDigsG

@[seg_val] theorem sext_sub32 (a b : Nat) (ha : a < 2 ^ 31) (hb : b ≤ a + 1) (hb' : b < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (4294967296 - b % 4294967296 + a % 4294967296)) =
      BitVec.ofNat 64 (a + 18446744073709551616 - b) := by
  have e : BitVec.ofNat 32 (4294967296 - b % 4294967296 + a % 4294967296) =
      BitVec.ofNat 32 ((a + 18446744073709551616 - b) % 4294967296) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  rw [e, sext_ofNat_mod]
  omega

end Tom.Machine.Fn.SMpMulHighDigsG
