import Tom.Machine.Kit.GenX_seg5a
import Tom.Machine.Kit.MulCall

/-!
# Value lemmas for `seg_go` (the growing reductions)

* `subw` of two small words, its sign-extended result as one `ofNat` (`olduse -= ix` in
  `s_mp_montgomery_reduce_fast`, negative when `olduse ≤ n->used`);
* `blez` (`bge zero, rs`) on any `ofNat`: taken iff zero or the sign bit is set.
-/

namespace Tom.Machine

open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- `subw rd, a, b` on small words, as a 64-bit two's complement `ofNat`. -/
@[seg_val] theorem subw_ofNat (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (4294967296 - b % 4294967296 + a % 4294967296)) =
      BitVec.ofNat 64 ((a + 18446744073709551616 - b) % 18446744073709551616) := by
  rw [sext_ofNatW_div rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show a < 4294967296 by omega), Nat.mod_eq_of_lt (show b < 4294967296 by omega)]
  by_cases h : b ≤ a
  · have e : (4294967296 - b + a) % 4294967296 = a - b := by omega
    rw [e, Nat.div_eq_of_lt (show a - b < 2147483648 by omega)]; omega
  · have e : (4294967296 - b + a) % 4294967296 = 4294967296 - b + a := by omega
    rw [e, show (4294967296 - b + a) / 2147483648 = 1 by omega]; omega

/-- `blez rs` on an `ofNat`: taken iff it is zero or negative. -/
@[seg_val] theorem bge_zero_ofNat' (d : Nat) :
    zopz0zKzJ_s (0#64) (BitVec.ofNat 64 d) = decide (d % 2 ^ 64 = 0 ∨ 2 ^ 63 ≤ d % 2 ^ 64) := by
  unfold zopz0zKzJ_s
  rw [toInt_ofNat_cond 64 d]
  simp only [BitVec.toInt_zero, Nat.add_one_sub_one]
  by_cases h : 2 ^ 63 ≤ d % 2 ^ 64 <;> simp [h] <;> omega

end Tom.Machine
