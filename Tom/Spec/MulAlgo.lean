import Tom.Spec.Mul

/-!
# Karatsuba, Toom-3 and the `mp_mul` dispatcher: the value identities

`s_mp_karatsuba_mul(a, b, c)` splits both operands at `B = min(a->used, b->used) / 2`
digits (`R = radix ^ B`): `a = x1·R + x0`, `b = y1·R + y0`. It computes `x0y0`, `x1y1`,
`t1 = (x1 + x0)(y1 + y0)` (by `s_mp_add` then `mp_mul`), `x0 := x0y0 + x1y1`,
`t1 := t1 − x0` (`s_mp_sub`: needs `t1 ≥ x0`, `karatsuba_ge`), shifts and adds:
`c = x0y0 + t1·R + x1y1·R²` (`karatsuba_val`).

`s_mp_toom_mul(a, b, c)` splits at `B = min(a->used, b->used) / 3` into three parts
each and evaluates at `1, 2, −1, ∞, 0` (`S1`, `S2`, `a1`, `b1`, `a0` in the C), then
interpolates (Bodrato's sequence, as `bn_s_mp_toom_mul.c` writes it). `toom3_*`: each
intermediate the C computes is a fixed integer combination of the product's
coefficients `p0 … p4`, the two divisions (by 3, then by 2, twice) are exact on
non-negative values, and the recomposition is the product.

The split itself is `natUpTo_split` (Tom/Spec/Mul.lean).
-/

namespace Tom

/-! ## Karatsuba -/

/-- The middle term is at least the two outer products. -/
theorem karatsuba_ge (x0 x1 y0 y1 : Nat) : x0 * y0 + x1 * y1 ≤ (x1 + x0) * (y1 + y0) := by
  have : (x1 + x0) * (y1 + y0) = x0 * y0 + x1 * y1 + (x0 * y1 + x1 * y0) := by grind
  omega

/-- **Karatsuba.** -/
theorem karatsuba_val (x0 x1 y0 y1 R : Nat) :
    (x1 * R + x0) * (y1 * R + y0) =
      x0 * y0 + ((x1 + x0) * (y1 + y0) - (x0 * y0 + x1 * y1)) * R + x1 * y1 * (R * R) := by
  have h : (x1 + x0) * (y1 + y0) - (x0 * y0 + x1 * y1) = x0 * y1 + x1 * y0 := by
    have : (x1 + x0) * (y1 + y0) = x0 * y0 + x1 * y1 + (x0 * y1 + x1 * y0) := by grind
    omega
  rw [h]; grind

/-- Karatsuba squaring (`s_mp_karatsuba_sqr`): `t1 = (x1 + x0)²`, `t1 − (x0² + x1²) = 2·x0·x1`. -/
theorem karatsuba_sqr_val (x0 x1 R : Nat) :
    (x1 * R + x0) * (x1 * R + x0) =
      x0 * x0 + ((x1 + x0) * (x1 + x0) - (x0 * x0 + x1 * x1)) * R + x1 * x1 * (R * R) :=
  karatsuba_val x0 x1 x0 x1 R

/-! ## Toom-3 -/

section toom
variable (a0 a1 a2 b0 b1 b2 : Int)

/-- The product's coefficients. -/
def tp0 : Int := a0 * b0
def tp1 : Int := a0 * b1 + a1 * b0
def tp2 : Int := a0 * b2 + a1 * b1 + a2 * b0
def tp3 : Int := a1 * b2 + a2 * b1
def tp4 : Int := a2 * b2

/-- `S1 = (a2 + a1 + a0)(b2 + b1 + b0)`: the value at 1. -/
theorem toom3_at1 : (a2 + a1 + a0) * (b2 + b1 + b0) =
    tp0 a0 b0 + tp1 a0 a1 b0 b1 + tp2 a0 a1 a2 b0 b1 b2 + tp3 a1 a2 b1 b2 + tp4 a2 b2 := by
  unfold tp0 tp1 tp2 tp3 tp4; grind

/-- `S2 = (4 a2 + 2 a1 + a0)(4 b2 + 2 b1 + b0)`, as the C builds it (`((a2 + a1) + a2)·2 + a0`). -/
theorem toom3_at2 : (((a2 + a1) + a2) * 2 + a0) * (((b2 + b1) + b2) * 2 + b0) =
    tp0 a0 b0 + 2 * tp1 a0 a1 b0 b1 + 4 * tp2 a0 a1 a2 b0 b1 b2 + 8 * tp3 a1 a2 b1 b2 + 16 * tp4 a2 b2 := by
  unfold tp0 tp1 tp2 tp3 tp4; grind

/-- `a1 := (a2 − a1 + a0)(b2 − b1 + b0)`: the value at −1. -/
theorem toom3_atm1 : (a2 - a1 + a0) * (b2 - b1 + b0) =
    tp0 a0 b0 - tp1 a0 a1 b0 b1 + tp2 a0 a1 a2 b0 b1 b2 - tp3 a1 a2 b1 b2 + tp4 a2 b2 := by
  unfold tp0 tp1 tp2 tp3 tp4; grind

end toom

/-- **The interpolation**, step by step as `bn_s_mp_toom_mul.c` writes it, from the five
point values `w1 = S1`, `w2 = S2`, `wm = a1 (value at −1)`, `w∞ = b1 = p4`, `w0 = a0 = p0`.
Each `exact` division is stated as a product. -/
structure Toom3Interp (p0 p1 p2 p3 p4 : Int) : Prop where
  /-- `S2 − a1 = 3·(p1 + p2 + 3p3 + 5p4)`: the division by 3 is exact. -/
  d3 : (p0 + 2 * p1 + 4 * p2 + 8 * p3 + 16 * p4) - (p0 - p1 + p2 - p3 + p4) =
    3 * (p1 + p2 + 3 * p3 + 5 * p4)
  /-- `S1 − a1 = 2·(p1 + p3)`: the first halving is exact. -/
  h1 : (p0 + p1 + p2 + p3 + p4) - (p0 - p1 + p2 - p3 + p4) = 2 * (p1 + p3)
  /-- `S1 − a0 = p1 + p2 + p3 + p4`. -/
  s1 : (p0 + p1 + p2 + p3 + p4) - p0 = p1 + p2 + p3 + p4
  /-- `S2 − S1 = 2·(p3 + 2p4)`: the second halving is exact. -/
  h2 : (p1 + p2 + 3 * p3 + 5 * p4) - (p1 + p2 + p3 + p4) = 2 * (p3 + 2 * p4)
  /-- `S1 − a1 − b1 = p2`. -/
  c2 : (p1 + p2 + p3 + p4) - (p1 + p3) - p4 = p2
  /-- `S2 − 2·b1 = p3`. -/
  c3 : (p3 + 2 * p4) - 2 * p4 = p3
  /-- `a1 − S2 = p1`. -/
  c1 : (p1 + p3) - p3 = p1

theorem toom3_interp (p0 p1 p2 p3 p4 : Int) : Toom3Interp p0 p1 p2 p3 p4 :=
  ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **Toom-3 recomposition**: `b1·x⁴ + S2·x³ + S1·x² + a1·x + a0` with the interpolated
coefficients is the product (`x = radix ^ B`). -/
theorem toom3_val (a0 a1 a2 b0 b1 b2 x : Int) :
    (a2 * x ^ 2 + a1 * x + a0) * (b2 * x ^ 2 + b1 * x + b0) =
      tp4 a2 b2 * x ^ 4 + tp3 a1 a2 b1 b2 * x ^ 3 + tp2 a0 a1 a2 b0 b1 b2 * x ^ 2 +
        tp1 a0 a1 b0 b1 * x + tp0 a0 b0 := by
  unfold tp0 tp1 tp2 tp3 tp4; grind

/-- The coefficients are non-negative for non-negative parts (the halvings and the division by
3 act on non-negative values, so truncation is exact). -/
theorem tp_nonneg {a0 a1 a2 b0 b1 b2 : Int} (h0 : 0 ≤ a0) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2)
    (k0 : 0 ≤ b0) (k1 : 0 ≤ b1) (k2 : 0 ≤ b2) :
    0 ≤ tp0 a0 b0 ∧ 0 ≤ tp1 a0 a1 b0 b1 ∧ 0 ≤ tp2 a0 a1 a2 b0 b1 b2 ∧ 0 ≤ tp3 a1 a2 b1 b2 ∧
      0 ≤ tp4 a2 b2 := by
  unfold tp0 tp1 tp2 tp3 tp4
  refine ⟨Int.mul_nonneg h0 k0, ?_, ?_, ?_, Int.mul_nonneg h2 k2⟩
  · exact Int.add_nonneg (Int.mul_nonneg h0 k1) (Int.mul_nonneg h1 k0)
  · exact Int.add_nonneg (Int.add_nonneg (Int.mul_nonneg h0 k2) (Int.mul_nonneg h1 k1)) (Int.mul_nonneg h2 k0)
  · exact Int.add_nonneg (Int.mul_nonneg h1 k2) (Int.mul_nonneg h2 k1)

/-! ## `mp_mul` -/

/-- What `mp_mul(a, b, c)` leaves in `c` (whichever algorithm the cut-offs choose): `c` valid
holding `a·b`; the C sets `c->sign := (c->used > 0) ? neg : MP_ZPOS`. -/
structure MulPost (a b c' : MpInt) : Prop where
  valid : c'.Valid
  val : c'.val = a.val * b.val

/-- `mp_sqr(a, b)`: `b = a²`, valid. -/
structure SqrPost (a b' : MpInt) : Prop where
  valid : b'.Valid
  val : b'.val = a.val * a.val

end Tom
