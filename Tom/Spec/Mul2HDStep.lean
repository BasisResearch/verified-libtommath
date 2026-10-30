import Tom.Spec.Mul2GStep

/-!
# `mp_mul_2(a, b)` with growth, `b` distinct: the model steps

`Tom/Spec/Mul2GStep.lean` with the destination `b`: `mp_mul_2` grows `b` to `a->used + 1` digits
when `b->alloc ≤ a->used` (`m2InD a b`, grown from `b`), doubles `a` into `b`'s array (the loop's
digits `m2g a`, the carry digit), zeroes `b`'s old digits above (`memset`) and sets
`b->sign = a->sign` last. `m2outD a A n`: `b`'s array with the digits of `a + a`, `n` used, `A`'s
sign (before the sign store); with the sign `a->sign` it is `m2out a A n`, whose `Mul2Post` gives
the value `2 a`.
-/

namespace Tom

open MpInt

/-- The destination `mp_mul_2(a, b)` writes: `b` grown to `a->used + 1` when short. -/
def m2InD (a b : MpInt) : MpInt := if b.alloc < a.used + 1 then b.growTo (a.used + 1) else b

theorem m2InD_grown {a b : MpInt} (hb : b.Shape) (h31 : a.used + 1 < 2 ^ 31) : GrownOf b (m2InD a b) :=
  GrownOf.ite hb id h31

theorem m2InD_room (a b : MpInt) : a.used + 1 ≤ (m2InD a b).alloc := by
  unfold m2InD; split
  · simp [MpInt.growTo, MpInt.ofDigits]
  · omega

/-- `b`'s struct before the sign store: the digits of `a + a` over `A`'s array, `A`'s sign. -/
def m2outD (a A : MpInt) (n : Nat) : MpInt := MpInt.ofDigits n A.alloc A.sign (addDigits a a)

/-- **`mp_mul_2(a, b)` with growth computes `2 a`** (after the sign store `b->sign = a->sign`),
leaves `b` valid and only grows it. -/
theorem m2outD_spec {a b A : MpInt} (ha : a.Valid) (hg : GrownOf b A) (hroom : a.used + 1 ≤ A.alloc) :
    (m2out a A (a.used + addCarryAt a a a.used)).Valid ∧
      (m2out a A (a.used + addCarryAt a a a.used)).val = 2 * a.val ∧
      b.alloc ≤ (m2out a A (a.used + addCarryAt a a a.used)).alloc := by
  obtain ⟨hv, -, hval⟩ := Mul2Post.spec ha hroom hg.shape.alloc_lt (m2out_post ha.toShape hroom)
  exact ⟨hv, hval, hg.alloc⟩

/-- The digits from `n = a->used + carry` on are zero. -/
theorem m2d_high {a : MpInt} (ha : a.Shape) {n j : Nat} (hn : n = a.used + addCarryAt a a a.used)
    (hj : n ≤ j) : addDigits a a j = 0 :=
  addDigits_self_high ha j (by omega)

end Tom
