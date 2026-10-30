import Tom.Spec.MulAlgo
import Tom.Spec.Mul
import Tom.Spec.Signed

/-!
# `mp_sqr`'s model steps

`mp_sqr` ends with `b->sign := MP_ZPOS` after whichever algorithm ran: a valid result of
magnitude `|a|²` is then `SqrPost a b'` (`val = a.val²`, the sign of a square being `+`).
-/

namespace Tom

/-- The result with its sign word cleared. -/
abbrev MpInt.zpos (b : MpInt) : MpInt := { b with sign := Layout.mpZpos }

theorem MpInt.zpos_shape {b : MpInt} (h : b.Shape) : b.zpos.Shape :=
  ⟨h.len, h.used_le, h.alloc_lt, h.digit_lt, h.high_zero⟩

/-- **The square, signed**: `b'` valid with `|b'| = |a|²` gives `SqrPost a b'.zpos`. -/
theorem sqrPost_zpos {a b' : MpInt} (hv : b'.Valid) (hm : b'.mag = a.mag * a.mag) :
    SqrPost a b'.zpos where
  valid := { toShape := MpInt.zpos_shape hv.toShape, top := hv.top, sign_ok := .inl rfl, zero_pos := fun _ => rfl }
  val := by
    have hmz : b'.zpos.mag = b'.mag := rfl
    unfold MpInt.val
    rw [ite_eq_right_of_eq_false _ _ (by simp [Layout.mpZpos, Layout.mpNeg]), hmz, hm]
    split
    · push_cast; rw [Int.neg_mul_neg]
    · push_cast; rfl

/-- `s_mp_sqr_fast`'s result, signed. -/
theorem sqrFast_zpos {a b b' : MpInt} (ha : a.Shape) (hroom : 2 * a.used ≤ b.alloc) (hb : b.Shape)
    (hsign : b.sign = Layout.mpZpos ∨ b.sign = Layout.mpNeg) (h : SqrFastPost a b b') :
    SqrPost a b'.zpos := by
  have := SqrFastPost.spec ha (by omega) hb.alloc_lt hsign h
  exact sqrPost_zpos this.1 this.2

/-- `mp_add` keeps the destination's allocation (every branch's `…Post` does). -/
theorem addPost_alloc {a b c c' : MpInt} (h : AddPost a b c c') : c'.alloc = c.alloc := by
  by_cases hs : a.sign = b.sign
  · exact (h.same hs).alloc
  · by_cases hl : cmpMag a b = .lt
    · exact (h.lt hs hl).alloc
    · exact (h.ge hs hl).alloc

end Tom
