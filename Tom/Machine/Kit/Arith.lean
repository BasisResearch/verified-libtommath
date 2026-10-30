import Tom.Machine.Kit.At
import Vsa.Sim.Muldi3Spec

/-!
# Register arithmetic in `Nat` form

The segment normal form states register values as BitVec terms over the
entry values (`x + sign_extend imm`, `sign_extend (extractLsb … 31 0)`, a
sign-extended load). The function proofs state them as `BitVec.ofNat 64 n`
of a `Nat` expression. These lemmas convert, each one side condition (the
range) for `omega`.
-/

namespace Tom.Machine

open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- Sign extension of a non-negative 32-bit value. -/
theorem signExtend_ofNat32 (d : Nat) (h : d < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 d) = BitVec.ofNat 64 d := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)
  · simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 32 by omega)]
    simp; omega

/-- The low 32 bits of an `ofNat` value below `2^32`. -/
theorem extractLsb_ofNat32 (x : Nat) (h : x < 2 ^ 32) :
    (BitVec.ofNat 64 x).extractLsb 31 0 = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega), Nat.mod_eq_of_lt h]

/-- `addiw rd, rs, imm` on a non-negative 32-bit `ofNat` value whose result is
non-negative: `sign_extend (extractLsb (x + imm) 31 0)`. -/
theorem addiw_ofNat (x y r : Nat) (hr : (x + y) % 2 ^ 64 = r) (hr' : r < 2 ^ 31) :
    BitVec.signExtend 64 ((BitVec.ofNat 64 x + BitVec.ofNat 64 y).extractLsb 31 0) =
      BitVec.ofNat 64 r := by
  rw [ofNat_add_ofNat, ofNat_eq_ofNat (y := r) (by omega), extractLsb_ofNat32 _ (by omega),
    signExtend_ofNat32 _ hr']

/-- `ret`'s target in the segment normal form (`Vsa.Sim.ret_tgt` with the
zero immediate folded). -/
theorem ret_target (r : BitVec 64) (h : r.toNat % 4 = 0) :
    Sail.BitVec.update (r + 0#64) 0 0#1 = r := by
  have := Vsa.Sim.ret_tgt r h
  rwa [Vsa.Sim.sext_zero] at this

/-- `toInt` of a small non-negative value. -/
theorem toInt_ofNat_small (u : Nat) (h : u < 2 ^ 63) : (BitVec.ofNat 64 u).toInt = u := by
  rw [BitVec.toInt_eq_toNat_of_lt (by simp [Nat.mod_eq_of_lt (show u < 2 ^ 64 by omega)]; omega)]
  simp [Nat.mod_eq_of_lt (show u < 2 ^ 64 by omega)]

/-- `bge x0, rs` (`blez rs`) on a small non-negative value: taken iff it is zero. -/
theorem bge_zero_ofNat (u : Nat) (h : u < 2 ^ 63) :
    zopz0zKzJ_s (0#64) (BitVec.ofNat 64 u) = decide (u = 0) := by
  unfold zopz0zKzJ_s
  rw [toInt_ofNat_small u h]
  simp only [BitVec.toInt_zero]
  by_cases hu : u = 0 <;> simp [hu] <;> omega

/-- `slli rd, rs, k` on an `ofNat` value. -/
theorem shl_ofNat (u k : Nat) (hk : k < 64) :
    Sail.shift_bits_left (BitVec.ofNat 64 u) (BitVec.ofNat 6 k) = BitVec.ofNat 64 (u * 2 ^ k) := by
  unfold Sail.shift_bits_left
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show k < 64 from hk)]

/-- `blt` on small non-negative values. -/
theorem blt_ofNat (x y : Nat) (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    zopz0zI_s (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x < y) := by
  unfold zopz0zI_s; rw [toInt_ofNat_small x hx, toInt_ofNat_small y hy]; simp

/-- `bge` on small non-negative values. -/
theorem bge_ofNat (x y : Nat) (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    zopz0zKzJ_s (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x ≥ y) := by
  unfold zopz0zKzJ_s; rw [toInt_ofNat_small x hx, toInt_ofNat_small y hy]; simp

/-- `blez` on a sign-extended word with its sign bit set. -/
theorem bge_zero_sext_neg (d : Nat) (h : 2 ^ 31 ≤ d % 4294967296) :
    zopz0zKzJ_s (0#64) (BitVec.signExtend 64 (BitVec.ofNat (31 - 0 + 1) d)) = true := by
  unfold zopz0zKzJ_s
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  have hneg : (BitVec.ofNat (31 - 0 + 1) d).toInt < 0 := by
    rw [BitVec.toInt_neg_iff]; simp; omega
  simp only [BitVec.toInt_zero, decide_eq_true_eq]; omega

/-- `bltu`/`bgeu` on values below `2^64`. -/
theorem bltu_ofNat (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    zopz0zI_u (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x < y) := by
  unfold zopz0zI_u; simp [Sail.BitVec.toNatInt, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem bgeu_ofNat (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    zopz0zKzJ_u (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x ≥ y) := by
  unfold zopz0zKzJ_u; simp [Sail.BitVec.toNatInt, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-- `sub` without borrow. -/
theorem ofNat_sub_ofNat (x y : Nat) (hy : y ≤ x) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y = BitVec.ofNat 64 (x - y) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega)]
  omega

/-- `beq`/`bne` on values below `2^64`. -/
theorem ofNat_beq (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := by
      intro he; have := congrArg BitVec.toNat he
      simp [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this; exact h this
    simp [h, this]

/-- The modulus forms (no range side condition), for `leaf_auto`. -/
theorem ofNat_beq' (x y : Nat) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) =
      decide (x % 18446744073709551616 = y % 18446744073709551616) := by
  rw [← ofNat_beq (x % 18446744073709551616) (y % 18446744073709551616) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide))]
  congr 1 <;> exact ofNat_eq_ofNat (by simp)

theorem bltu_ofNat' (x y : Nat) :
    zopz0zI_u (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) =
      decide (x % 18446744073709551616 < y % 18446744073709551616) := by
  unfold zopz0zI_u; simp [Sail.BitVec.toNatInt]; omega

theorem bgeu_ofNat' (x y : Nat) :
    zopz0zKzJ_u (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) =
      decide (x % 18446744073709551616 ≥ y % 18446744073709551616) := by
  unfold zopz0zKzJ_u; simp [Sail.BitVec.toNatInt]; omega

theorem ret_target' (r : BitVec 64) (h : r.toNat % 4 = 0) : Sail.BitVec.update r 0 0#1 = r := by
  have := ret_target r h
  rwa [BitVec.add_zero] at this

theorem toNat_add' (x y : BitVec 64) : (x + y).toNat = (x.toNat + y.toNat) % 18446744073709551616 :=
  BitVec.toNat_add x y

theorem toNat_sub' (x y : BitVec 64) :
    (x - y).toNat = (18446744073709551616 - y.toNat + x.toNat) % 18446744073709551616 :=
  BitVec.toNat_sub x y

/-! ## 32-bit values (`lw`, `addw`, `srliw`) and masks -/

theorem ofNat_add_ofNat32 (x y : Nat) :
    BitVec.ofNat 32 x + BitVec.ofNat 32 y = BitVec.ofNat 32 (x + y) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.add_mod]

/-- The width-polymorphic `ofNat` add (the widths `extractLsb` produces, such
as `31 - 0 + 1`, are not syntactically `32`). -/
theorem ofNat_add_ofNatW {w : Nat} (x y : Nat) :
    BitVec.ofNat w x + BitVec.ofNat w y = BitVec.ofNat w (x + y) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.add_mod]

/-- The low word of an `ofNat` value, at the width `extractLsb 31 0` has. -/
theorem extractLsb_ofNat32' (x : Nat) :
    (BitVec.ofNat 64 x).extractLsb 31 0 = BitVec.ofNat (31 - 0 + 1) (x % 4294967296) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ (31 - 0 + 1) ∣ 2 ^ 64)]
  simp

theorem signExtend_ofNat32' (d : Nat) (h : d % 4294967296 < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat (31 - 0 + 1) d) = BitVec.ofNat 64 (d % 4294967296) := by
  rw [← signExtend_ofNat32 _ h]; congr 1; apply BitVec.eq_of_toNat_eq; simp

theorem and_mask28 (s : Nat) :
    BitVec.ofNat 64 s &&& 268435455#64 = BitVec.ofNat 64 (s % 268435456) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (268435455 : Nat) % 2 ^ 64 = 2 ^ 28 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 28 ∣ 2 ^ 64)]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm

theorem srl32_ofNat (s k : Nat) (hk : k < 32) :
    Sail.shift_bits_right (BitVec.ofNat 32 s) (BitVec.ofNat 5 k) = BitVec.ofNat 32 (s % 4294967296 / 2 ^ k) := by
  unfold Sail.shift_bits_right
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show k < 32 from hk)]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide)))]

theorem srl32_ofNat' (s k : Nat) (hk : k < 32) :
    Sail.shift_bits_right (BitVec.ofNat (31 - 0 + 1) s) (BitVec.ofNat 5 k) =
      BitVec.ofNat (31 - 0 + 1) (s % 4294967296 / 2 ^ k) :=
  srl32_ofNat s k hk

/-- `srli`/`srl` on an `ofNat` value. -/
theorem srl64_ofNat (x k : Nat) (hk : k < 64) :
    Sail.shift_bits_right (BitVec.ofNat 64 x) (BitVec.ofNat 6 k) =
      BitVec.ofNat 64 (x % 18446744073709551616 / 2 ^ k) := by
  unfold Sail.shift_bits_right
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show k < 64 from hk)]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide)))]

/-- The width-polymorphic `ofNat` subtraction (`subw` works at width `31 - 0 + 1`). -/
theorem ofNat_sub_ofNatW {w : Nat} (x y : Nat) :
    BitVec.ofNat w x - BitVec.ofNat w y = BitVec.ofNat w (2 ^ w - y % 2 ^ w + x) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, Nat.add_mod]

/-- `slli` with the shift as a 6-bit literal (`shl_ofNat` with `2^k` evaluated by `omega`). -/
theorem shl_ofNat' (u k : Nat) (hk : k < 64) :
    Sail.shift_bits_left (BitVec.ofNat 64 u) (BitVec.ofNat 6 k) = BitVec.ofNat 64 (u * 2 ^ k) :=
  shl_ofNat u k hk

/-- `signExtend_ofNat32'`/`bge_zero_sext_neg` for any spelling `w` of the width
32 (`31 - 0 + 1` from `extractLsb`, `32` once `Nat.reduceSub` has run); the
side condition `w = 32` is for `omega`. -/
theorem signExtend_ofNatW {w : Nat} (hw : w = 32) (d : Nat) (h : d % 4294967296 < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat w d) = BitVec.ofNat 64 (d % 4294967296) := by
  subst hw; exact signExtend_ofNat32' d h

theorem bge_zero_sext_negW {w : Nat} (hw : w = 32) (d : Nat) (h : 2 ^ 31 ≤ d % 4294967296) :
    zopz0zKzJ_s (0#64) (BitVec.signExtend 64 (BitVec.ofNat w d)) = true := by
  subst hw; exact bge_zero_sext_neg d h

theorem srl32_ofNatW {w : Nat} (hw : w = 32) (s k : Nat) (hk : k < 32) :
    Sail.shift_bits_right (BitVec.ofNat w s) (BitVec.ofNat 5 k) =
      BitVec.ofNat w (s % 4294967296 / 2 ^ k) := by
  subst hw; exact srl32_ofNat s k hk

/-- `blez` on a sign-extended word, unconditionally. -/
theorem bge_zero_sextW {w : Nat} (hw : w = 32) (d : Nat) :
    zopz0zKzJ_s (0#64) (BitVec.signExtend 64 (BitVec.ofNat w d)) =
      decide (d % 4294967296 = 0 ∨ 2 ^ 31 ≤ d % 4294967296) := by
  by_cases h : d % 4294967296 < 2 ^ 31
  · rw [signExtend_ofNatW hw d h, bge_zero_ofNat _ (by omega)]
    simp only [decide_eq_decide]; omega
  · rw [bge_zero_sext_negW hw d (by omega)]; simp; omega

/-- A sign-extended word, negative or not (`subw`): its value, its low 28 bits
(`& MP_MASK`) and its low word (`srliw`). -/
theorem sext_toNatW {w : Nat} (hw : w = 32) (d : Nat) :
    (BitVec.signExtend 64 (BitVec.ofNat w d)).toNat =
      d % 4294967296 + (if (BitVec.ofNat w d).msb = true then 18446744069414584320 else 0) := by
  subst hw
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.reduceSub]
  rw [Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide) : d % 4294967296 < 18446744073709551616)]

theorem sext_and_mask28W {w : Nat} (hw : w = 32) (d : Nat) :
    BitVec.signExtend 64 (BitVec.ofNat w d) &&& 268435455#64 = BitVec.ofNat 64 (d % 268435456) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, sext_toNatW hw, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (268435455 : Nat) % 2 ^ 64 = 2 ^ 28 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.reducePow]
  split <;> omega

theorem extractLsb_sextW {w : Nat} (hw : w = 32) (d : Nat) :
    (BitVec.signExtend 64 (BitVec.ofNat w d)).extractLsb 31 0 = BitVec.ofNat (31 - 0 + 1) (d % 4294967296) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb_toNat, sext_toNatW hw, BitVec.toNat_ofNat]
  simp only [Nat.shiftRight_zero, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd]
  split <;> omega

/-- Close a register equation `BitVec.ofNat`-arithmetic `= BitVec.ofNat 64 n`
by `toNat` and `omega` (shifts rewritten to products first). The modulus is
the literal `2^64`: `BitVec.toNat_add`/`BitVec.toNat_ofNat` (`2 ^ 64`) make
`simp` run away. -/
macro "bv_nat" : tactic => `(tactic|
  (apply BitVec.eq_of_toNat_eq
   simp only [Tom.Machine.toNat_add', Tom.Machine.toNat_sub', Tom.Machine.toNat_ofNat']
   omega))

/-- Split a conjunction of register equations; close each by `trivial` or
`bv_nat`. -/
macro "regs_close" : tactic => `(tactic|
  (repeat' (apply And.intro)
   all_goals first | exact True.intro | omega | bv_nat))

end Tom.Machine
