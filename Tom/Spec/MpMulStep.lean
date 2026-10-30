import Tom.Spec.MulAlgo
import Tom.Spec.Algo

/-!
# `mp_mul`: the model step

`mp_mul` ends with `c->sign := neg ∧ c->used > 0` where `neg = (a->sign != b->sign)`, computed
as `snez(a->sign - b->sign)` (`ngOf`) and stored as `sgtz(c->used) & neg` (`signOf`): from any
callee result holding `|a| |b|`, clamped, this is `MulPost`. `mag_full`: the truncation at
`digs = a->used + b->used + 1` of `s_mp_mul_digs(_fast)` is the whole product.
-/

namespace Tom

open MpInt

/-- `neg = (a->sign != b->sign)` (the code's `snez(a->sign - b->sign)`, `Fn/MpMulGK.lean` `ng_eq`). -/
def ngOf (sa sb : Nat) : Nat := if sa = sb then 0 else 1

/-- The stored sign word: `sgtz(c->used) & neg`. -/
def signOf (u ne : Nat) : Nat := min (ne % 2) (u % 4294967296)

/-- `c'` with `mp_mul`'s sign. -/
def withSign (a b c' : MpInt) : MpInt := { c' with sign := signOf c'.used (ngOf a.sign b.sign) }

theorem withSign_shape {a b c' : MpInt} (h : c'.Shape) : (withSign a b c').Shape :=
  { len := h.len, used_le := h.used_le, alloc_lt := h.alloc_lt, digit_lt := h.digit_lt
    high_zero := h.high_zero }

theorem withSign_sign (a b c' : MpInt) :
    (withSign a b c').sign = Layout.mpZpos ∨ (withSign a b c').sign = Layout.mpNeg := by
  simp only [withSign, signOf, Layout.mpZpos, Layout.mpNeg]
  have : ngOf a.sign b.sign % 2 < 2 := Nat.mod_lt _ (by decide)
  rcases (show min (ngOf a.sign b.sign % 2) (c'.used % 4294967296) = 0 ∨
      min (ngOf a.sign b.sign % 2) (c'.used % 4294967296) = 1 by omega) with h | h <;> simp [h]

/-- The product's digits fill at most `a->used + b->used` places. -/
theorem mag_full {a b : MpInt} (ha : a.ShapeU) (hb : b.ShapeU) :
    (a.mag * b.mag) % radix ^ (a.used + b.used + 1) = a.mag * b.mag := by
  apply Nat.mod_eq_of_lt
  have h1 := ha.mag_lt
  have h2 := hb.mag_lt
  have h3 : a.mag * b.mag < radix ^ a.used * radix ^ b.used :=
    Nat.mul_lt_mul_of_lt_of_le h1 (Nat.le_of_lt h2) (Nat.pow_pos radix_pos)
  rw [← Nat.pow_add] at h3
  exact Nat.lt_of_lt_of_le h3 (Nat.pow_le_pow_right radix_pos (by omega))

theorem mag_zero_iff {a : MpInt} (ht : 0 < a.used → a.digit (a.used - 1) ≠ 0) :
    a.mag = 0 ↔ a.used = 0 := by
  constructor
  · intro h
    refine Classical.byContradiction fun hu => ?_
    have hlt : a.digit (a.used - 1) * radix ^ (a.used - 1) ≤ a.mag := by
      unfold MpInt.mag
      have e : a.used = (a.used - 1) + 1 := by omega
      rw [e, natUpTo]
      simp only [show a.used - 1 + 1 - 1 = a.used - 1 by omega]
      rw [Nat.mul_comm]; omega
    have := ht (by omega)
    have : 0 < a.digit (a.used - 1) * radix ^ (a.used - 1) :=
      Nat.mul_pos (Nat.pos_of_ne_zero this) (Nat.pow_pos radix_pos)
    omega
  · intro h; unfold MpInt.mag; rw [h]; rfl

/-- **`mp_mul`'s post** from a callee's clamped product. -/
theorem mul_post {a b c' : MpInt} (ha : a.ValidU) (hb : b.ValidU) (hs : c'.Shape)
    (ht : 0 < c'.used → c'.digit (c'.used - 1) ≠ 0) (hm : c'.mag = a.mag * b.mag) :
    MulPost a b (withSign a b c') := by
  have hu : c'.used < 4294967296 := by have := hs.used_le; have := hs.alloc_lt; omega
  have hz := mag_zero_iff ht
  refine ⟨{ withSign_shape hs with top := ht, sign_ok := withSign_sign a b c', zero_pos := ?_ }, ?_⟩
  · intro h0; simp only [withSign] at h0; simp [withSign, signOf, h0, Layout.mpZpos]
  · have hva : a.sign = 0 ∨ a.sign = 1 := ha.sign_ok
    have hvb : b.sign = 0 ∨ b.sign = 1 := hb.sign_ok
    have hsg : (withSign a b c').sign = if c'.used = 0 then 0 else if a.sign = b.sign then 0 else 1 := by
      simp only [withSign, signOf, ngOf, Nat.mod_eq_of_lt hu]
      by_cases h0 : c'.used = 0
      · simp [h0]
      · by_cases he : a.sign = b.sign <;> simp [h0, he] <;> omega
    have hmg : (withSign a b c').mag = a.mag * b.mag := hm
    simp only [MpInt.val, hsg, hmg, Layout.mpNeg]
    by_cases h0 : c'.used = 0
    · have : a.mag * b.mag = 0 := hm ▸ hz.2 h0
      rcases Nat.mul_eq_zero.1 this with h | h <;> simp [h, h0]
    · rcases hva with h1 | h1 <;> rcases hvb with h2 | h2 <;> simp [h0, h1, h2, Int.neg_mul, Int.mul_neg]

end Tom
