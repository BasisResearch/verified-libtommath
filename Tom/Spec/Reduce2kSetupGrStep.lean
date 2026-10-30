import Tom.Spec.Reduce2kSetupGStep

/-!
# `mp_reduce_2k_setup` growing `tmp`: the model step

`Reduce2kSetupStep.setup_fin` over the growing `mp_2expt(&tmp, p)` (`Pw2G`: `tmp` past `MP_PREC` digits
when it must): `s_mp_sub(&tmp, a, &tmp)` writes into `tmp`'s own block (it has `tmp->used` digits, the
larger operand), and its low digit is the setup's `d`.
-/

namespace Tom.Reduce2kSetupStep

open MpInt Mont Reduce

/-- **`mp_reduce_2k_setup`'s digit** after the growing `mp_2expt`. -/
theorem setup_finG {a t t' : MpInt} (ha : a.Valid) (hp : Pw2G a t) (h : SSubPost t a t t') :
    Setup2kPost a (t'.digit 0) ∧ t'.alloc = t.alloc := by
  have hs := SSubPost.spec hp.valid.toShape ha.toShape hp.ge hp.valid.used_le hp.valid.alloc_lt
    hp.valid.sign_ok h
  refine ⟨⟨?_⟩, h.alloc⟩
  rw [digit_zero hs.1.toShape, hs.2, hp.mag]

end Tom.Reduce2kSetupStep
