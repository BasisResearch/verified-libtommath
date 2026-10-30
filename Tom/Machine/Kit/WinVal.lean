import Tom.Machine.Kit.WordVal
import Tom.Machine.Kit.MulCall

/-!
# Word idioms of `s_mp_exptmod`'s window: a scoped `seg_val` set

Enabled by a rows annotation's `"opens": ["Tom.Machine.WV.Win"]` (`Kit/WordVal.lean`'s convention):

* `sllw rd, 1, w` and `sllw rd, 1, w - 1` (`addiw a5, s3, -1` first): `2^w`, `2^(w-1)` (the window
  size's powers);
* `slli rd, rs, k` on an `ofNat` value without wrap.
-/

namespace Tom.Machine.WV.Win

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim

/-- `sllw rd, 1, k` (`li s0, 1`: the literal `1#32`). -/
@[scoped seg_val] theorem sllw_one' (k : Nat) (hk : k < 31) :
    BitVec.signExtend 64 (Sail.shift_bits_left (1#32)
      (BitVec.extractLsb 4 0 (BitVec.ofNat 32 (k % 4294967296)))) = BitVec.ofNat 64 (2 ^ k) := by
  have := Tom.Machine.WV.Mask.sllw_one k hk
  rwa [show (1 % 4294967296 : Nat) = 1 from rfl] at this

/-- `addiw a5, s3, -1; sllw s2, s0, a5`: `1 << (k - 1)`. -/
@[scoped seg_val] theorem sllw_one_pred (k : Nat) (h1 : 1 ≤ k) (hk : k < 32) :
    BitVec.signExtend 64 (Sail.shift_bits_left (1#32)
      (BitVec.extractLsb 4 0 (BitVec.ofNat 32 ((k + 18446744073709551615) % 4294967296)))) =
      BitVec.ofNat 64 (2 ^ (k - 1)) := by
  rw [show (k + 18446744073709551615) % 4294967296 = (k - 1) % 4294967296 by omega]
  exact sllw_one' (k - 1) (by omega)

/-- `slli rd, rs, k` on an `ofNat` value. -/
@[scoped seg_val] theorem slli_ofNat (x k : Nat) (hk : k < 64) :
    Sail.shift_bits_left (BitVec.ofNat 64 x) (BitVec.ofNat 6 k) = BitVec.ofNat 64 (x * 2 ^ k) :=
  Tom.Machine.BitW.shl_ofNatW x k (by simp; omega)

/-- `bge`, `blt` on small non-negative values. -/
@[scoped seg_val] theorem bge_ofNat' (x y : Nat) (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    zopz0zKzJ_s (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x ≥ y) := Tom.Machine.bge_ofNat x y hx hy

@[scoped seg_val] theorem blt_ofNat' (x y : Nat) (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    zopz0zI_s (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x < y) := Tom.Machine.blt_ofNat x y hx hy

/-- `bne`/`beq` of two pointers (the table's loops compare `&M[y]` with an end pointer). -/
@[scoped seg_val] theorem bne_ofNat' (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = !decide (x = y) := by
  rw [bne, Tom.Machine.ofNat_beq', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

@[scoped seg_val] theorem beq_ofNat' (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
  rw [Tom.Machine.ofNat_beq', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-- A 32-bit word sign-extended to 64 bits, as a number (`slliw`'s result). -/
def sx (b : Nat) : Nat := if b < 2 ^ 31 then b else b + 18446744069414584320

theorem sx_mod (b : Nat) (hb : b < 2 ^ 32) : sx b % 4294967296 = b := by
  unfold sx; split <;> omega

theorem sx_lt (b : Nat) (hb : b < 2 ^ 32) : sx b < 2 ^ 64 := by
  unfold sx; split <;> omega

/-- `slliw rd, rs, k`: the low word shifted, sign-extended. -/
@[scoped seg_val] theorem slliw_sx (x k : Nat) (hk : k < 32) :
    BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.ofNat 32 (x % 4294967296)) (BitVec.ofNat 5 k)) =
      BitVec.ofNat 64 (sx (x * 2 ^ k % 4294967296)) := by
  rw [Tom.Machine.BitW.shl_ofNatW _ _ (by simp; omega), Tom.Machine.sext_ofNatW_div rfl]
  have h32 : x % 4294967296 * 2 ^ k % 4294967296 = x * 2 ^ k % 4294967296 := by
    rw [Nat.mod_mul_mod]
  rw [h32]
  congr 1
  have hlt : x * 2 ^ k % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  unfold sx; split <;> omega

/-- `or`, `and` of two `ofNat` words. -/
@[scoped seg_val] theorem or_ofNat (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x ||| BitVec.ofNat 64 y = BitVec.ofNat 64 (x ||| y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or]; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow hx hy)).symm

@[scoped seg_val] theorem and_ofNat (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x &&& BitVec.ofNat 64 y = BitVec.ofNat 64 (x &&& y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hx)).symm

/-- `sx` of a word below `2^31` (a positive `slliw` result). -/
@[scoped seg_val] theorem sx_of_lt (b : Nat) (h : b < 2 ^ 31) : sx b = b := by
  unfold sx; simp [h]

/-- `sll rd, rs, rk` with `rk` an `ofNat` amount below 64: the amount's low six bits. -/
@[scoped seg_val] theorem extract6_ofNat (k : Nat) (hk : k < 64) :
    BitVec.extractLsb 5 0 (BitVec.ofNat 64 k) = BitVec.ofNat 6 k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]

/-- `bge` with a sign-extended word on the left. -/
@[scoped seg_val] theorem bge_sext_ofNat (d x : Nat) (hd : d % 4294967296 < 2 ^ 31) (hx : x < 2 ^ 63) :
    zopz0zKzJ_s (BitVec.signExtend 64 (BitVec.ofNat 32 d)) (BitVec.ofNat 64 x) = decide (d % 4294967296 ≥ x) := by
  rw [Tom.Machine.signExtend_ofNatW rfl d hd]
  exact Tom.Machine.bge_ofNat _ _ (by omega) hx

/-- `sllw rd, rs, rk`: a small word shifted by a small amount. -/
theorem sllw_ofNat (x k : Nat) (hk : k < 32) (h : x * 2 ^ k < 2 ^ 31) :
    BitVec.signExtend 64 (Sail.shift_bits_left (BitVec.ofNat 32 (x % 4294967296))
      (BitVec.extractLsb 4 0 (BitVec.ofNat 32 k))) = BitVec.ofNat 64 (x * 2 ^ k) := by
  have hx : x < 2 ^ 31 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)) h
  rw [show BitVec.ofNat 32 k = BitVec.ofNat 32 (k % 4294967296) by rw [Nat.mod_eq_of_lt (by omega)],
    Tom.Machine.WV.Mask.extract5_ofNat k hk, Tom.Machine.BitW.shl_ofNatW _ _ (by simp; omega),
    Nat.mod_eq_of_lt (show x < 4294967296 by omega)]
  exact Tom.Machine.signExtend_ofNat32 _ h

end Tom.Machine.WV.Win
