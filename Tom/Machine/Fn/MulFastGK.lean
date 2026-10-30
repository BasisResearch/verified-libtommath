import Tom.Machine.Kit.GenX_seg5a

/-!
# `s_mp_mul_digs_fast`'s segment rows: value lemmas

* `bge s6, s0` at `44b4` with `s6 = b->used - 1` and `b->used = 0` (`s6 = -1`): `Kit/Arith.lean`'s
  compares cover small operands only; here the left operand has its sign bit set;
* the doubleword `1 - b->used` the set-up stores at `438c` (`subw`);
* a `seg_leaf_ext` closer: the value normal form alone.
-/

namespace Tom.Machine

open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- `bge` of a negative `ofNat` (`s6 = b->used - 1 = -1`) against a nonnegative one: not taken. -/
@[seg_val] theorem bge_neg_ofNat (x y : Nat) (hx : 2 ^ 63 ≤ x % 2 ^ 64) (hy : y % 2 ^ 64 < 2 ^ 63) :
    zopz0zKzJ_s (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = false := by
  unfold zopz0zKzJ_s
  rw [toInt_ofNat_cond 64 x, toInt_ofNat_cond 64 y]
  have hx' : 9223372036854775808 ≤ x % 18446744073709551616 := hx
  have hy' : ¬ 9223372036854775808 ≤ y % 18446744073709551616 := by
    have : y % 18446744073709551616 < 9223372036854775808 := hy
    omega
  simp only [Nat.add_one_sub_one, Nat.reducePow, hx', hy', ite_true, ite_false]
  simp only [decide_eq_false_iff_not]
  omega

/-- `subw a5, 1, b->used` stored as a doubleword (`438c`): `1 - b->used` modulo `2 ^ 64`. -/
@[seg_val] theorem sext_one_sub (u : Nat) (hu : u < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (4294967296 - u % 4294967296 + 1)) =
      BitVec.ofNat 64 ((18446744073709551617 - u) % 18446744073709551616) := by
  have e : BitVec.ofNat 32 (4294967296 - u % 4294967296 + 1) =
      BitVec.ofNat 32 ((18446744073709551617 - u) % 4294967296) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  rw [e, sext_ofNat_mod _ (by omega)]
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

/-- A leaf that the value normal form alone closes (`oc2z`'s guard after `bge_neg_ofNat`): `seg_leaf`'s
last alternative runs `seg_vnf` and then fails even when no goal is left (as `Fn/MpSqrGK.lean`). -/
macro_rules | `(tactic| seg_leaf_ext [$ds,*]) => `(tactic| ((first | gleaf_nf [$ds,*] | skip); (try seg_vnf []); done))

end Tom.Machine
