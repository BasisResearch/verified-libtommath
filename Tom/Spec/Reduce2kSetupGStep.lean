import Tom.Spec.Reduce2kSetupStep
import Tom.Spec.Expt2G
import Tom.Spec.SSubGStep

/-!
# `mp_reduce_2k_setup_l` growing: the model steps

`Reduce2kSetupStep`'s with growth: `mp_2expt(&tmp, p)` grows `tmp` past `MP_PREC` digits when it must
(`Expt2Post (expt2In (zeroN MP_PREC) p)`, `Pw2G`: `Pw2` without the allocation), and
`s_mp_sub(&tmp, a, d)` grows `d` (`SSubPost tmp a (sSubIn tmp d)`, `setupL_finG`).
-/

namespace Tom.Reduce2kSetupStep

open MpInt Mont Reduce

/-- `tmp` after the growing `mp_2expt(&tmp, mp_count_bits(a))`. -/
structure Pw2G (a t : MpInt) : Prop where
  valid : t.Valid
  mag : t.mag = 2 ^ nbits a.mag
  used : a.used ≤ t.used
  tused : t.used = countBits a / Layout.digitBits + 1
  ge : a.mag ≤ t.mag

theorem pow_ofG {a t : MpInt} (ha : a.Valid) (hb : countBits a < 2 ^ 31)
    (h : Expt2Post (expt2In (MpInt.zeroN defPrec) (countBits a)) (countBits a) t) : Pw2G a t :=
  have hs := Expt2Post.specG (a := MpInt.zeroN defPrec) (by decide) hb h
  { valid := hs.1
    mag := by rw [hs.2.1, countBits_spec ha]; rfl
    used := by rw [h.used]; exact used_le_cb a
    tused := h.used
    ge := by rw [hs.2.1, countBits_spec ha]; exact Nat.le_of_lt (lt_two_pow_bitLen _) }

/-- **`mp_reduce_2k_setup_l`'s `d`**, grown by `s_mp_sub(&tmp, a, d)` when short. -/
theorem setupL_finG {a t d d' : MpInt} (ha : a.Valid) (hp : Pw2G a t) (hd : d.Shape) (h31 : t.used < 2 ^ 31)
    (hsign : d.sign = Layout.mpZpos ∨ d.sign = Layout.mpNeg) (h : SSubPost t a (sSubIn t d) d') :
    Setup2kLPost a d' :=
  have hg := sSubIn_grown hd h31
  have hs := SSubPost.spec hp.valid.toShape ha.toShape hp.ge (sSubIn_room t d) hg.shape.alloc_lt
    (by rw [hg.sign]; exact hsign) h
  ⟨hs.1, by rw [hs.2, hp.mag]⟩

end Tom.Reduce2kSetupStep
