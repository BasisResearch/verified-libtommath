import Tom.Spec.Reduce
import Tom.Spec.Bits
import Tom.Spec.Expt2
import Tom.Spec.Sub
import Tom.Spec.Init

/-!
# `mp_reduce_2k_setup(_l)`: the model steps

`mp_init(&tmp)` gives `MP_PREC` zero digits; `mp_2expt(&tmp, p)` with `p = mp_count_bits(a)`
leaves `2^p` (`Pw2`: valid, `MP_PREC` digits, at least `a`'s digit count, at least `|a|`);
`s_mp_sub(&tmp, a, ·)` leaves `2^p - |a|`, whose low digit is `mp_reduce_2k_setup`'s `d`
(`setup_fin`) and whose whole is `mp_reduce_2k_setup_l`'s (`setupL_fin`).
-/

namespace Tom.Reduce2kSetupStep

open MpInt Mont Reduce

/-- `mp_count_bits(a) / MP_DIGIT_BIT + 1` digits cover `a`'s. -/
theorem used_le_cb (a : MpInt) : a.used ≤ countBits a / Layout.digitBits + 1 := by
  have e : Layout.digitBits = 28 := rfl
  unfold countBits; rw [e]; split
  · omega
  · omega

/-- `tmp` after `mp_2expt(&tmp, mp_count_bits(a))`. -/
structure Pw2 (a t : MpInt) : Prop where
  valid : t.Valid
  mag : t.mag = 2 ^ nbits a.mag
  alloc : t.alloc = defPrec
  used : a.used ≤ t.used
  tused : t.used = countBits a / Layout.digitBits + 1
  ge : a.mag ≤ t.mag

theorem pow_of {a t : MpInt} (ha : a.Valid) (hroom : countBits a / Layout.digitBits + 1 ≤ defPrec)
    (h : Expt2Post (MpInt.zeroN defPrec) (countBits a) t) : Pw2 a t :=
  have hs := Expt2Post.spec (a := MpInt.zeroN defPrec) hroom (by decide) h
  { valid := hs.1
    mag := by rw [hs.2.1, countBits_spec ha]; rfl
    alloc := h.alloc
    used := by rw [h.used]; exact used_le_cb a
    tused := h.used
    ge := by rw [hs.2.1, countBits_spec ha]; exact Nat.le_of_lt (lt_two_pow_bitLen _) }

/-- `2^p - |a|` (`s_mp_sub(&tmp, a, c)`). -/
theorem sub_of {a t c c' : MpInt} (ha : a.Valid) (hp : Pw2 a t) (hroom : t.used ≤ c.alloc) (hc : c.alloc < 2 ^ 31)
    (hsign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg) (h : SSubPost t a c c') :
    c'.Valid ∧ c'.mag = 2 ^ nbits a.mag - a.mag := by
  have hs := SSubPost.spec hp.valid.toShape ha.toShape hp.ge hroom hc hsign h
  exact ⟨hs.1, by rw [hs.2, hp.mag]⟩

/-- A shaped `mp_int`'s digit 0 is its magnitude mod the radix. -/
theorem digit_zero {x : MpInt} (hx : x.Shape) : x.digit 0 = x.mag % radix := by
  by_cases hu : x.used = 0
  · rw [hx.high_zero 0 (by omega)]; simp [MpInt.mag, hu, natUpTo]
  · unfold MpInt.mag; rw [natUpTo_mod_radix _ (hx.digit_lt 0) _ (by omega)]

/-- **`mp_reduce_2k_setup`'s digit**: `tmp.dp[0]` after `s_mp_sub(&tmp, a, &tmp)`. -/
theorem setup_fin {a t t' : MpInt} (ha : a.Valid) (hp : Pw2 a t) (h : SSubPost t a t t') :
    Setup2kPost a (t'.digit 0) ∧ t'.alloc = defPrec := by
  have hs := sub_of ha hp hp.valid.used_le hp.valid.alloc_lt hp.valid.sign_ok h
  refine ⟨⟨?_⟩, h.alloc.trans hp.alloc⟩
  rw [digit_zero hs.1.toShape, hs.2]

/-- **`mp_reduce_2k_setup_l`'s `d`**: after `s_mp_sub(&tmp, a, d)` (`d`'s digits kept in place). -/
theorem setupL_fin {a t d d' : MpInt} (ha : a.Valid) (hp : Pw2 a t) (hroom : t.used ≤ d.alloc) (hd : d.alloc < 2 ^ 31)
    (hsign : d.sign = Layout.mpZpos ∨ d.sign = Layout.mpNeg) (h : SSubPost t a d d') :
    Setup2kLPost a d' ∧ d'.alloc = d.alloc :=
  have hs := sub_of ha hp hroom hd hsign h
  ⟨⟨hs.1, hs.2⟩, h.alloc⟩

end Tom.Reduce2kSetupStep
