import Tom.Machine.Kit.Gen

/-!
# Value lemmas for `seg_go` (`s_mp_mul_digs`, `mp_reduce_2k*`)

Signed compares the compare lemmas of `Kit/Arith.lean` lack, in `decide` form
(`@[seg_val]`; `seg_guard`'s `seg_cmp` then turns the `decide` into a `Prop`
for `omega`):
* `bltz` on a negative `ofNat` (`digs < 0`);
* `bge` of a small `ofNat` against a sign-extended word of either sign
  (`MP_MIN(b->used, digs - ix)` with `digs - ix ≤ 0`).
-/

namespace Tom.Machine

open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- `toInt` of an `ofNat`, by its sign bit. -/
theorem toInt_ofNat_cond (n x : Nat) :
    (BitVec.ofNat n x).toInt =
      if 2 ^ (n - 1) ≤ x % 2 ^ n then ((x % 2 ^ n : Nat) : Int) - 2 ^ n else ((x % 2 ^ n : Nat) : Int) := by
  rw [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide, BitVec.toNat_ofNat]
  by_cases h : 2 ^ (n - 1) ≤ x % 2 ^ n <;> simp [h]

/-- `bltz rs` on an `ofNat`: taken iff the sign bit is set. -/
@[seg_val] theorem blt_ofNat_zero (x : Nat) :
    zopz0zI_s (BitVec.ofNat 64 x) 0#64 = decide (2 ^ 63 ≤ x % 2 ^ 64) := by
  unfold zopz0zI_s
  rw [toInt_ofNat_cond 64 x]
  simp only [BitVec.toInt_zero, Nat.add_one_sub_one]
  by_cases h : 2 ^ 63 ≤ x % 2 ^ 64 <;> simp [h] <;> omega

/-- `bge` of a small `ofNat` against a sign-extended word of either sign. -/
@[seg_val] theorem bge_ofNat_sextW {w : Nat} (hw : w = 32) (x d : Nat) (hx : x < 2 ^ 63) :
    zopz0zKzJ_s (BitVec.ofNat 64 x) (BitVec.signExtend 64 (BitVec.ofNat w d)) =
      decide (2 ^ 31 ≤ d % 4294967296 ∨ d % 4294967296 ≤ x) := by
  subst hw
  unfold zopz0zKzJ_s
  rw [BitVec.toInt_signExtend_of_le (by decide), toInt_ofNat_cond 32 d, toInt_ofNat_cond 64 x]
  simp only [Nat.reducePow, Nat.reduceSub, Nat.mod_eq_of_lt (show x < 18446744073709551616 by omega)]
  by_cases h : 2147483648 ≤ d % 4294967296 <;> simp [h] <;> omega

end Tom.Machine
