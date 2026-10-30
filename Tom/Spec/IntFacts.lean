import Tom.Spec.DivD
import Tom.Spec.Init
import Tom.Spec.MpMulStep

/-!
# Small `mp_int` facts annotation texts use

They were per-function helpers of the assemblies (`Fn/MpDivG5K.lean`: `sign_zpos_of`, `setSign_valid`,
`ip_pos`; `Fn/ToomMulG5K.lean`: `div3_pos`, `upos`; `Fn/MpMulGK.lean`: `ng_eq`), used by several annotations.
-/

namespace Tom

/-- A valid integer whose sign is not `MP_NEG` is `MP_ZPOS`. -/
theorem sign_zpos_of {x : MpInt} (hv : x.Valid) (h : ¬ x.sign = 1) : x.sign = Layout.mpZpos := by
  rcases hv.sign_ok with h1 | h1
  · exact h1
  · exact absurd h1 h

/-- A valid integer with a new sign (`MP_NEG` only when nonzero) is valid. -/
theorem setSign_valid {x : MpInt} (hx : x.Valid) {s : Nat} (hs : s = 0 ∨ s = 1) (hz : x.used = 0 → s = 0) :
    ({ x with sign := s } : MpInt).Valid :=
  { hx.toShape with top := hx.top, sign_ok := hs, zero_pos := hz }

/-- `mp_init_size`'s digit count is positive. -/
theorem ip_pos (n : Nat) : 0 < initPrec n := by unfold initPrec minPrec; simp only [Layout.digitBits]; omega

/-- `s_mp_div_3`'s quotient has a live array (`max 3 a->used` digits). -/
theorem div3_pos {a c' : MpInt} (h : Div3Quot a c') : 0 < c'.alloc := by
  unfold Div3Quot DivLongQuot at h; rw [h.alloc]; omega

/-- A nonzero valid integer has a digit. -/
theorem upos {x : MpInt} (hv : x.Valid) (h : x.val ≠ 0) : 0 < x.used := by
  rcases Nat.eq_zero_or_pos x.used with h0 | h0
  · exfalso; apply h; rw [MpInt.val_eq, MpInt.mag_used_zero h0]; split <;> rfl
  · exact h0

/-- `snez(a->sign - b->sign)` is `ngOf` (`mp_mul`'s new sign). -/
theorem ng_eq {sa sb : Nat} (h1 : sa < 2) (h2 : sb < 2) :
    (if (sa + 18446744073709551615 * sb) % 18446744073709551616 = 0 then 0 else 1) = Tom.ngOf sa sb := by
  unfold Tom.ngOf; split <;> split <;> omega

end Tom
