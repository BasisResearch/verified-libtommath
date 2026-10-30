import Tom.Spec.MpReduce2kLGStep
import Tom.Spec.Grow6Step

/-!
# `mp_reduce_2k` with `a` and `q` growing: the model steps

`mp_reduce_2k(a, n, d)` is `mp_reduce_2k_l` with an `mp_digit` `d` and `mp_mul_d(&q, d, &q)` (skipped
for `d = 1`) in place of `mp_mul(&q, d, &q)`. `S1G.mulD` is the in-place growing `mp_mul_d`
(`Api/MulDGA.lean`), `S1G.one` the skipped multiplication.
-/

namespace Tom.MpReduce2kLStep

open MpInt Ledger Reduce

/-- The digit `d` as an `mp_int`. -/
def dI (d : Nat) : MpInt := ⟨if d = 0 then 0 else 1, 1, Layout.mpZpos, [d]⟩

theorem dI_digit (d i : Nat) : (dI d).digit i = if i = 0 then d else 0 := by
  rcases i with _ | i <;> simp [dI, MpInt.digit]

theorem dI_valid {d : Nat} (hd : d < radix) : (dI d).Valid where
  len := rfl
  used_le := by simp only [dI]; split <;> omega
  alloc_lt := by show 1 < 2 ^ 31; decide
  digit_lt := fun i => by rw [dI_digit]; split; exact hd; exact radix_pos
  high_zero := fun i hi => by
    rw [dI_digit]; split
    · subst_vars; simp only [dI] at hi; split at hi <;> simp_all
    · rfl
  top := fun h => by
    have h0 : d ≠ 0 := fun e => by simp [dI, e] at h
    rw [show (dI d).used = 1 by simp [dI, h0], dI_digit]; simpa using h0
  sign_ok := .inl rfl
  zero_pos := fun _ => rfl

theorem dI_mag (d : Nat) : (dI d).mag = d := by
  unfold MpInt.mag; simp only [dI]; split
  · subst_vars; rfl
  · simp [natUpTo, dI_digit, MpInt.digit]

variable {a n a1 a2 q2 q3 : MpInt}

/-- `mp_mul_d(&q, d, &q)`, growing `q`. -/
theorem S1G.mulD (s : S1G a n a1 a2 q2) {d : Nat} (hd : d < radix) (hq : q2.used + 1 < 2 ^ 31)
    (hm : MulDPost q2 d (mulDIn q2 q2) q3) : S2 n (dI d) a1 q3 := by
  have hg := mulDIn_grown (a := q2) s.quo.valid.toShape hq
  obtain ⟨hv, hmag, -⟩ := MulDPost.spec s.quo.valid hd (mulDIn_room q2 q2) hg.shape.alloc_lt hm
  exact ⟨hv, by rw [hmag, s.quo.mag, dI_mag]⟩

/-- `d = 1`: no multiplication. -/
theorem S1G.one (s : S1G a n a1 a2 q2) : S2 n (dI 1) a1 q2 :=
  ⟨s.quo.valid, by rw [s.quo.mag, dI_mag, Nat.mul_one]⟩

end Tom.MpReduce2kLStep
