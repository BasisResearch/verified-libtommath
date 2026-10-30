import Tom.Spec.Algo

/-!
# `mp_cmp_d` and `mp_cmp`: signed comparisons

`mp_cmp_d(a, b)` (`vendor/libtommath/bn_mp_cmp_d.c`) compares `a` with one
digit `b`: `MP_LT` when `a` is negative, `MP_GT` when it has more than one
digit, otherwise the comparison of `dp[0]` with `b`. `mp_cmp(a, b)`
(`bn_mp_cmp.c`) compares by sign, then by magnitude (`mp_cmp_mag`), the
operands swapped when both are negative.

`cmpD` and `cmpS` are these case splits as the C states them; `cmpD_spec`
and `cmpS_spec` say they are `compare` on the values.
-/

namespace Tom

open MpInt

/-- `mp_cmp_d(a, b)` as the C states it. -/
def cmpD (a : MpInt) (b : Nat) : Ordering :=
  if a.sign = Layout.mpNeg then .lt
  else if 1 < a.used then .gt
  else compare (a.digit 0) b

/-- `mp_cmp(a, b)` as the C states it. -/
def cmpS (a b : MpInt) : Ordering :=
  if a.sign ≠ b.sign then (if a.sign = Layout.mpNeg then .lt else .gt)
  else if a.sign = Layout.mpNeg then cmpMag b a else cmpMag a b

theorem int_compare_ofNat (x y : Nat) : compare (x : Int) (y : Int) = compare x y := by
  simp only [compare, compareOfLessAndEq]
  by_cases h1 : x < y
  · simp [h1, Int.ofNat_lt.2 h1]
  · by_cases h2 : x = y
    · subst h2; simp
    · have h3 : ¬ (x : Int) < y := fun h => h1 (Int.ofNat_lt.1 h)
      have h4 : (x : Int) ≠ y := fun h => h2 (Int.ofNat.inj h)
      simp [h1, h2, h3, h4]

theorem int_compare_neg (x y : Nat) : compare (-(x : Int)) (-(y : Int)) = compare y x := by
  rw [← int_compare_ofNat]
  simp only [compare, compareOfLessAndEq]
  by_cases h1 : (y : Int) < x
  · simp [h1, show -(x : Int) < -(y : Int) by omega]
  · by_cases h2 : (y : Int) = x
    · simp [h2]
    · simp [h1, h2, show ¬ -(x : Int) < -(y : Int) by omega, show -(x : Int) ≠ -(y : Int) by omega]

theorem int_compare_lt {x y : Int} (h : x < y) : compare x y = .lt := by
  simp [compare, compareOfLessAndEq, h]

theorem int_compare_gt {x y : Int} (h : y < x) : compare x y = .gt := by
  simp [compare, compareOfLessAndEq, show ¬ x < y by omega, show x ≠ y by omega]

/-- A negative valid `mp_int` is nonzero. -/
theorem MpInt.Valid.mag_pos_of_neg {a : MpInt} (ha : a.Valid) (hn : a.sign = Layout.mpNeg) :
    0 < a.mag := by
  have hu : 0 < a.used := by
    rcases Nat.eq_zero_or_pos a.used with h | h
    · have := ha.zero_pos h; rw [hn] at this; simp [Layout.mpNeg, Layout.mpZpos] at this
    · exact h
  have := MpInt.mag_ge ha hu
  have : 0 < radix ^ (a.used - 1) := Nat.pow_pos radix_pos
  omega

/-- The magnitude of an `mp_int` with at most one digit is `dp[0]`. -/
theorem MpInt.mag_le_one {a : MpInt} (ha : a.Shape) (hu : a.used ≤ 1) : a.mag = a.digit 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu with h | h
  · rw [MpInt.mag, h, ha.high_zero 0 (by omega)]; rfl
  · rw [MpInt.mag, h]; simp [natUpTo]

/-- **`mp_cmp_d` compares values.** -/
theorem cmpD_spec {a : MpInt} (ha : a.Valid) {b : Nat} (hb : b < radix) :
    cmpD a b = compare a.val (b : Int) := by
  unfold cmpD MpInt.val
  by_cases hn : a.sign = Layout.mpNeg
  · have := ha.mag_pos_of_neg hn
    simp only [hn, ↓reduceIte]
    exact (int_compare_lt (by omega)).symm
  · simp only [hn, ↓reduceIte]
    by_cases hu : 1 < a.used
    · have h1 := MpInt.mag_ge ha (by omega)
      have h2 : radix ^ 1 ≤ radix ^ (a.used - 1) := Nat.pow_le_pow_right radix_pos (by omega)
      simp only [hu, ↓reduceIte]
      exact (int_compare_gt (by simp only [Nat.pow_one] at h2; omega)).symm
    · simp only [hu, ↓reduceIte]
      rw [MpInt.mag_le_one ha.toShape (by omega), int_compare_ofNat]

/-- **`mp_cmp` compares values.** -/
theorem cmpS_spec {a b : MpInt} (ha : a.Valid) (hb : b.Valid) : cmpS a b = compare a.val b.val := by
  unfold cmpS MpInt.val
  have hsa := ha.sign_ok; have hsb := hb.sign_ok
  simp only [Layout.mpZpos, Layout.mpNeg] at hsa hsb
  by_cases he : a.sign = b.sign
  · simp only [he, ne_eq, not_true_eq_false, ↓reduceIte]
    by_cases hn : b.sign = Layout.mpNeg
    · simp only [hn, ↓reduceIte, int_compare_neg, cmpMag_eq hb ha]
    · simp only [hn, ↓reduceIte, int_compare_ofNat, cmpMag_eq ha hb]
  · simp only [ne_eq, he, not_false_eq_true, ↓reduceIte]
    by_cases hn : a.sign = Layout.mpNeg
    · have := ha.mag_pos_of_neg hn
      have hbn : ¬ b.sign = Layout.mpNeg := by simp only [Layout.mpNeg] at hn ⊢; omega
      simp only [hn, hbn, ↓reduceIte]
      exact (int_compare_lt (by omega)).symm
    · have hbn : b.sign = Layout.mpNeg := by simp only [Layout.mpNeg] at hn ⊢; omega
      have := hb.mag_pos_of_neg hbn
      simp only [hn, hbn, ↓reduceIte]
      exact (int_compare_gt (by omega)).symm

end Tom
