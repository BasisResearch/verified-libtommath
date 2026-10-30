import Tom.Machine.Kit.Gen
import Tom.Machine.Kit.BitW
import Tom.Machine.Kit.Shift

/-!
# Word idioms of the segment rows: value lemmas in sets an annotation enables

`seg_go`'s leaves and values are closed by the global `@[seg_val]` set (Kit/Gen.lean); growing it
slows every row (a row ran out of memory). The idioms below were per-function lemma files
(`Fn/MpDivDGK.lean`, `Fn/ToomSqrGK.lean`, `Fn/ToomMulGK.lean`, `Fn/MpMulGK.lean`); here they are
generic, each family a *scoped* `seg_val` set that a rows annotation enables by its `"opens"`
(scripts/gen_rows.py):

* `WV.Mask`: the power-of-two test `(b - 1) & b == 0` (`addiw`, `and`, `beqz`), `sllw 1, ix`, the mask
  `x & ~(-1 << ix)` (`sllw`, `not`, `and`) and `(w << 28) | x` (`mp_div_d`, `mdivdg.rows.json`);
* `WV.Sext`: the word negations `B − 4B = −3B` and back (`subw`, `negw`) and a small `addw`, sign-
  extended (`s_mp_toom_sqr`, `s_mp_toom_mul`);
* `WV` (no attribute, used by name): the sign arithmetic of `mp_mul` (`sub` of two signs, `sgtz; and`),
  `slliw 1`, `addw; addiw 1`, `slti; beqz` of small values (`mmulg.rows.json`, `Fn/MpMulGK.lean`'s
  `seg_leaf_ext` closer).
-/

namespace Tom.Machine.WV

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim

theorem sub01 (x y : Nat) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y =
      BitVec.ofNat 64 ((x + 18446744073709551615 * y) % 18446744073709551616) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem sgn01 (ne cu : Nat) :
    BitVec.ofNat 64 ne &&& zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) (BitVec.ofNat 64 (cu % 4294967296)))) =
      BitVec.ofNat 64 (min (ne % 2) (cu % 4294967296)) := by
  rw [show (0#64) = BitVec.ofNat 64 0 from rfl,
    Tom.Machine.blt_ofNat 0 (cu % 4294967296) (by decide) (by omega)]
  by_cases h : 0 < cu % 4294967296
  · simp only [h, decide_true]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    show BitVec.toNat (BitVec.ofNat 64 ne) &&& 1 = _
    rw [Nat.and_one_is_mod]; simp only [BitVec.toNat_ofNat]; omega
  · simp only [h, decide_false]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    show BitVec.toNat (BitVec.ofNat 64 ne) &&& 0 = _
    simp only [Nat.and_zero, BitVec.toNat_ofNat]; omega

/-- `slliw a4, a5, 1` of a small value. -/
theorem sllw1 (x : Nat) (hx : x < 2 ^ 30) :
    BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.ofNat 32 (x % 4294967296)) 1#5) = BitVec.ofNat 64 (2 * x) := by
  rw [Nat.mod_eq_of_lt (show x < 4294967296 by omega),
    show (1#5 : BitVec 5) = BitVec.ofNat 5 1 from rfl, Tom.Machine.shl32_ofNat x 1 (by decide) (by omega),
    Tom.Machine.signExtend_ofNat32 _ (by omega), Nat.mul_comm, Nat.pow_one]

/-- `addw a3, a3, a4; addiw a3, a3, 1` of two small values. -/
theorem addw3 (x y : Nat) (hx : x < 2 ^ 30) (hy : y < 2 ^ 30) :
    ((y % 4294967296 + x % 4294967296) % 4294967296 + 1) % 4294967296 = x + y + 1 := by
  omega

/-- `slti a4, a3, k; beqz a4`: `k ≤ x`. -/
theorem slti_beqz (x k : Nat) (hx : x < 2 ^ 63) (hk : k < 2 ^ 63) :
    (BitVec.ofNat 64 (bool_to_bit (zopz0zI_s (BitVec.ofNat 64 x) (BitVec.ofNat 64 k))).toNat == 0#64) =
      decide (k ≤ x) := by
  rw [Tom.Machine.blt_ofNat x k hx hk]
  by_cases h : x < k
  · simp only [h, decide_true, show ¬ k ≤ x by omega, decide_false]; rfl
  · simp only [h, decide_false, show k ≤ x by omega, decide_true]; rfl

end Tom.Machine.WV

namespace Tom.Machine.WV.Mask

theorem extract5_ofNat (k : Nat) (hk : k < 32) :
    BitVec.extractLsb 4 0 (BitVec.ofNat 32 (k % 4294967296)) = BitVec.ofNat (4 - 0 + 1) k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb]

/-- The power-of-two test: `addiw a2, b, -1; and a2, a2, b; beqz a2`. -/
@[scoped seg_val] theorem andm1_beq (b : Nat) (h1 : 0 < b) (h2 : b < 4294967296) :
    (BitVec.ofNat 64 ((b + 18446744073709551615) % 4294967296) &&& BitVec.ofNat 64 b == 0#64) =
      decide ((b - 1) &&& b = 0) := by
  rw [show (b + 18446744073709551615) % 4294967296 = b - 1 by omega, ← BitVec.ofNat_and]
  have hl : (b - 1) &&& b < 2 ^ 64 := Nat.lt_of_le_of_lt Nat.and_le_right (by omega)
  rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, Tom.Machine.ofNat_beq']
  simp only [Nat.mod_eq_of_lt hl, Nat.zero_mod]

/-- `sllw rd, 1, ix`: `1 << ix`. -/
@[scoped seg_val] theorem sllw_one (k : Nat) (hk : k < 31) :
    BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.ofNat 32 (1 % 4294967296))
      (BitVec.extractLsb 4 0 (BitVec.ofNat 32 (k % 4294967296)))) = BitVec.ofNat 64 (2 ^ k) := by
  rw [extract5_ofNat k (by omega), Tom.Machine.BitW.shl_ofNatW _ _ (by simp; omega)]
  have : 2 ^ k < 2 ^ 31 := Nat.pow_lt_pow_right (by decide) hk
  rw [Nat.one_mod, Nat.one_mul]
  exact Tom.Machine.signExtend_ofNat32 _ this

/-- The scan's test `bne (1 << ix), b`. -/
@[scoped seg_val] theorem bne_two_pow (k b : Nat) (hk : 2 ^ k < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 (2 ^ k) != BitVec.ofNat 64 b) = !decide (2 ^ k = b) := by
  rw [bne, Tom.Machine.ofNat_beq', Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hb]

theorem sllw_m1_0 : ∀ k, k < 32 →
    BitVec.signExtend 64 (Sail.shift_bits_left (4294967295#32) (BitVec.ofNat (4 - 0 + 1) k)) =
      BitVec.ofNat 64 (18446744073709551616 - 2 ^ k) := by
  decide +kernel

/-- `li a4, -1; sllw a4, a4, ix`: `-(1 << ix)`. -/
@[scoped seg_val] theorem sllw_m1 (k : Nat) (hk : k < 32) :
    BitVec.signExtend 64 (Sail.shift_bits_left (4294967295#32)
      (BitVec.extractLsb 4 0 (BitVec.ofNat 32 (k % 4294967296)))) =
      BitVec.ofNat 64 (18446744073709551616 - 2 ^ k) := by
  rw [extract5_ofNat k hk]; exact sllw_m1_0 k hk

theorem not_mask0 : ∀ k, k < 32 →
    BitVec.ofNat 64 (18446744073709551616 - 2 ^ k) ^^^ 18446744073709551615#64 = BitVec.ofNat 64 (2 ^ k - 1) := by
  decide +kernel

/-- `not a4; and a4, a2, a4`: `*d = a->dp[0] & ((1 << ix) - 1)`. -/
theorem and_not_mask (x k : Nat) (hx : x < 4294967296) (hk : k < 32) :
    BitVec.ofNat 64 (x % 4294967296) &&& (BitVec.ofNat 64 (18446744073709551616 - 2 ^ k) ^^^ 18446744073709551615#64) =
      BitVec.ofNat 64 (x % 2 ^ k) := by
  rw [not_mask0 k hk, ← BitVec.ofNat_and, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]

/-- `slli a4, a4, 28; or a4, a0, a4`: `w * 2^28 + a->dp[ix]`. -/
@[scoped seg_val] theorem or_shl28 (x w : Nat) (hx : x < 268435456) :
    BitVec.ofNat 64 (x % 4294967296) ||| BitVec.ofNat 64 (w * 268435456) = BitVec.ofNat 64 (w * 268435456 + x) := by
  rw [Nat.mod_eq_of_lt (by omega : x < 4294967296), ← BitVec.ofNat_or, Nat.or_comm,
    show w * 268435456 = w <<< 28 by rw [Nat.shiftLeft_eq], ← Nat.shiftLeft_add_eq_or_of_lt (by simpa using hx)]

/-- `not a4` of `-(1 << ix)`. -/
@[scoped seg_val] theorem not_mask (k : Nat) (hk : k < 32) :
    BitVec.ofNat 64 (18446744073709551616 - 2 ^ k) ^^^ 18446744073709551615#64 = BitVec.ofNat 64 (2 ^ k - 1) :=
  not_mask0 k hk

/-- `and a4, a2, a4` with the low mask. -/
@[scoped seg_val] theorem and_low (x k : Nat) : BitVec.ofNat 64 x &&& BitVec.ofNat 64 (2 ^ k - 1) = BitVec.ofNat 64 (x % 2 ^ k) := by
  rw [← BitVec.ofNat_and, Nat.and_two_pow_sub_one_eq_mod]

end Tom.Machine.WV.Mask

namespace Tom.Machine.WV.Sext

open LeanRV64DExecutable LeanRV64DExecutable.Functions

theorem sext_neg3' (nb : Nat) (h : nb < 2 ^ 29) (hp : 0 < nb) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (4294967296 - 3 * nb)) = BitVec.ofNat 64 (18446744073709551616 - 3 * nb) := by
  have e1 : (4294967296 - 3 * nb) % 4294967296 = 4294967296 - 3 * nb := Nat.mod_eq_of_lt (by omega)
  have e2 : (18446744073709551616 - 3 * nb) % 18446744073709551616 = 18446744073709551616 - 3 * nb :=
    Nat.mod_eq_of_lt (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [sext_toNatW rfl, BitVec.toNat_ofNat]
  have hm : (BitVec.ofNat 32 (4294967296 - 3 * nb)).msb = true := by
    rw [BitVec.msb_eq_decide]
    simp only [BitVec.toNat_ofNat, decide_eq_true_eq, Nat.reducePow, Nat.reduceSub]
    rw [e1]; omega
  rw [hm, if_pos rfl, e1]
  simp only [Nat.reducePow]
  rw [e2]; omega

@[scoped seg_val] theorem sext_neg3 (nb : Nat) (h : nb < 2 ^ 29) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (4294967296 - 4 * nb % 4294967296 + nb % 4294967296)) =
      BitVec.ofNat 64 (18446744073709551616 - 3 * nb) := by
  rw [Nat.mod_eq_of_lt (show 4 * nb < 4294967296 by omega), Nat.mod_eq_of_lt (show nb < 4294967296 by omega)]
  rcases Nat.eq_zero_or_pos nb with rfl | hp
  · decide
  · rw [show 4294967296 - 4 * nb + nb = 4294967296 - 3 * nb by omega]
    exact sext_neg3' nb h hp

@[scoped seg_val] theorem sext_pos3 (nb : Nat) (h : nb < 2 ^ 29) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (4294967296 - (18446744073709551616 - 3 * nb) % 4294967296 + 0)) =
      BitVec.ofNat 64 (3 * nb) := by
  rcases Nat.eq_zero_or_pos nb with rfl | hp
  · decide
  · rw [show 4294967296 - (18446744073709551616 - 3 * nb) % 4294967296 + 0 = 3 * nb by omega]
    exact signExtend_ofNat32 _ (by omega)

@[scoped seg_val] theorem sext_addw (x y : Nat) (h : x + y < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (x % 4294967296 + y % 4294967296)) = BitVec.ofNat 64 (x + y) := by
  rw [Nat.mod_eq_of_lt (show x < 4294967296 by omega), Nat.mod_eq_of_lt (show y < 4294967296 by omega)]
  exact signExtend_ofNat32 _ (by omega)

end Tom.Machine.WV.Sext
