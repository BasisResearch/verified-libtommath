import Tom.Spec.Algo

/-!
# `mp_int`s with stale digits above `used`

`s_mp_balance_mul` multiplies a left-over slice whose digits at and above `used` are the previous
slice's, so the multiplication group's operands
are only `ValidU`: `Valid` without `Shape.high_zero`. Every algorithm `mp_mul` dispatches to reads
`a.dp[i]` only for `i < a.used`, and `mag` is a sum over those digits, so the model steps of the
group hold for `ShapeU` / `ValidU` operands (their hypotheses are these structures).

A caller with the full invariant converts it explicitly (`Shape.toShapeU`, `Valid.toShapeU`,
`Valid.toU`).
-/

namespace Tom.MpInt

/-- `Shape` without `high_zero`. -/
structure ShapeU (a : MpInt) : Prop where
  len : a.digits.length = a.alloc
  used_le : a.used ≤ a.alloc
  alloc_lt : a.alloc < 2 ^ 31
  digit_lt : ∀ i, a.digit i < radix

/-- `Valid` without `high_zero`: the digits at and above `used` arbitrary (below `radix`). -/
structure ValidU (a : MpInt) : Prop extends ShapeU a where
  top : 0 < a.used → a.digit (a.used - 1) ≠ 0
  sign_ok : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg
  zero_pos : a.used = 0 → a.sign = Layout.mpZpos

theorem Shape.toU {a : MpInt} (h : a.Shape) : a.ShapeU := ⟨h.len, h.used_le, h.alloc_lt, h.digit_lt⟩

theorem Valid.toU {a : MpInt} (h : a.Valid) : a.ValidU := ⟨h.toShape.toU, h.top, h.sign_ok, h.zero_pos⟩

theorem Valid.toShapeU {a : MpInt} (h : a.Valid) : a.ShapeU := h.toShape.toU

/-- Uniform spellings: `h.toShapeU` for a `Shape`, `Valid` or `ValidU` fact, `h.toU` for a `Valid` or
`ValidU` one (an annotation shared by a `Valid` and a `ValidU` variant reads both). -/
theorem Shape.toShapeU {a : MpInt} (h : a.Shape) : a.ShapeU := h.toU

theorem ValidU.toU {a : MpInt} (h : a.ValidU) : a.ValidU := h

theorem ShapeU.toShapeU {a : MpInt} (h : a.ShapeU) : a.ShapeU := h

theorem ShapeU.mag_lt {a : MpInt} (h : a.ShapeU) : a.mag < radix ^ a.used := natUpTo_lt _ h.digit_lt _

theorem ValidU.mag_ge {a : MpInt} (h : a.ValidU) (hu : 0 < a.used) : radix ^ (a.used - 1) ≤ a.mag := by
  have := natUpTo_ge_top a.digit (a.used - 1) (h.top hu)
  rwa [Nat.sub_add_cancel hu] at this

end Tom.MpInt
