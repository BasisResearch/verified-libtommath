import Tom.Spec.MulAlgo
import Tom.Spec.Algo

/-!
# `s_mp_karatsuba_mul`: the model steps

The split of an operand at `B` digits and the final recomposition, at the level the
assembly sees them (digit functions and magnitudes):

* `lowOf a B`, `highOf a B`: the digits the copy loops write into `x0`/`y0` (the low `B`)
  and `x1`/`y1` (the rest, shifted down); `mag_low`, `mag_high`: `|a| mod R` and `|a| / R`
  for `R = radix ^ B` (`natUpTo_split`).
* `highOf_top`: the high half of a valid `a` with `B < a.used` has a nonzero top digit
  (no clamp needed, as the C's comment says).
* `kara_recompose`: the products and sums the C forms give `|a| |b|` (`karatsuba_val`).
-/

namespace Tom

open MpInt

/-- The low `B` digits (`x0.dp[i] = a->dp[i]`, `i < B`). -/
def lowOf (a : MpInt) (B : Nat) : Nat → Nat := fun i => if i < B then a.digit i else 0

/-- The digits from `B` on, shifted down (`x1.dp[k] = a->dp[B + k]`). -/
def highOf (a : MpInt) (B : Nat) : Nat → Nat := fun k => a.digit (B + k)

theorem natUpTo_lowOf (a : MpInt) (B : Nat) : natUpTo (lowOf a B) B = natUpTo a.digit B :=
  natUpTo_congr B fun i hi => by simp [lowOf, hi]

/-- `|a| = |x1| R + |x0|`. -/
theorem mag_split {a : MpInt} {B : Nat} (hB : B ≤ a.used) :
    a.mag = radix ^ B * natUpTo (highOf a B) (a.used - B) + natUpTo (lowOf a B) B := by
  unfold MpInt.mag
  rw [show a.used = B + (a.used - B) by omega, natUpTo_split, natUpTo_lowOf,
    show B + (a.used - B) - B = a.used - B by omega]
  unfold highOf
  omega

theorem low_lt (a : MpInt) (ha : a.Shape) (B : Nat) : natUpTo (lowOf a B) B < radix ^ B :=
  natUpTo_lt _ (fun i => by unfold lowOf; split <;> first | exact ha.digit_lt i | exact radix_pos) B

/-- `|x0| = |a| mod R`. -/
theorem mag_low {a : MpInt} (ha : a.Shape) {B : Nat} (hB : B ≤ a.used) :
    natUpTo (lowOf a B) B = a.mag % radix ^ B := by
  rw [mag_split hB, Nat.mul_add_mod, Nat.mod_eq_of_lt (low_lt a ha B)]

/-- `|x1| = |a| / R`. -/
theorem mag_high {a : MpInt} (ha : a.Shape) {B : Nat} (hB : B ≤ a.used) :
    natUpTo (highOf a B) (a.used - B) = a.mag / radix ^ B := by
  rw [mag_split hB, Nat.mul_add_div (Nat.pow_pos radix_pos), Nat.div_eq_of_lt (low_lt a ha B),
    Nat.add_zero]

/-- The high half of a valid operand is clamped: its top digit is `a`'s. -/
theorem highOf_top {a : MpInt} (ha : a.Valid) {B : Nat} (hB : B < a.used) :
    highOf a B (a.used - B - 1) ≠ 0 := by
  have := ha.top (by omega)
  simp only [highOf, show B + (a.used - B - 1) = a.used - 1 by omega]
  exact this

/-- **The recomposition**: with `X0 = |a| mod R`, `X1 = |a| / R` (and `Y0`, `Y1` for `b`),
`x0y0 + ((x1 + x0)(y1 + y0) − (x0y0 + x1y1)) R + x1y1 R² = |a| |b|`. -/
theorem kara_recompose (A B' R : Nat) :
    A % R * (B' % R) + ((A / R + A % R) * (B' / R + B' % R) - (A % R * (B' % R) + A / R * (B' / R))) * R +
      A / R * (B' / R) * (R * R) = A * B' := by
  have hA : A = A / R * R + A % R := (Nat.div_add_mod' A R).symm
  have hB : B' = B' / R * R + B' % R := (Nat.div_add_mod' B' R).symm
  have := karatsuba_val (A % R) (A / R) (B' % R) (B' / R) R
  rw [← hA, ← hB] at this
  exact this.symm

/-- `t1 − x0` in `s_mp_sub(&t1, &x0, &t1)` is defined: `x0y0 + x1y1 ≤ (x1 + x0)(y1 + y0)`. -/
theorem kara_sub_ok (A B' R : Nat) :
    A % R * (B' % R) + A / R * (B' / R) ≤ (A / R + A % R) * (B' / R + B' % R) :=
  karatsuba_ge _ _ _ _

end Tom
