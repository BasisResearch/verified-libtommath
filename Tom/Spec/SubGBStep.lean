import Tom.Spec.SubGStep

/-!
# `mp_sub(a, b, b)` with growth: the value

`SubG.spec` (Tom/Spec/SubGStep.lean) with the destination `b`: `mp_sub` sets `b->sign` first and
tail-calls `s_mp_add(a, b, b)` (unequal signs), `s_mp_sub(b, a, b)` (`|a| < |b|`, the sign the
flip of `b->sign`) or `s_mp_sub(a, b, b)`; each tail callee reads its operand `b` with the new sign
(magnitudes only). `SubG.specB` reads the branch posts as the value `a − b`.
-/

namespace Tom

open MpInt

/-- **`mp_sub(a, b, b)` with growth computes `a − b`**, leaves `b` valid and only grows it. -/
theorem SubG.specB {a b x : MpInt} (ha : a.Valid) (hb : b.Valid)
    (h31 : max a.used b.used + 1 < 2 ^ 31)
    (h : SubG a b (SAddPost a (b.withSign a.sign) (sAddIn a (b.withSign a.sign) (b.withSign a.sign)) x)
      (SSubPost (b.withSign (if b.sign = 0 then 1 else 0)) a
        (sSubIn (b.withSign (if b.sign = 0 then 1 else 0)) (b.withSign (if b.sign = 0 then 1 else 0))) x)
      (SSubPost a (b.withSign b.sign) (sSubIn a (b.withSign b.sign)) x)) :
    x.Valid ∧ x.val = a.val - b.val ∧ b.alloc ≤ x.alloc := by
  have hsa := sign_cases ha.sign_ok
  have hsb := sign_cases hb.sign_ok
  rw [MpInt.val_eq (a := a), MpInt.val_eq (a := b)]
  by_cases hs : a.sign = b.sign
  · by_cases hab : a.mag < b.mag
    · have hp := h.lt hs hab
      have hsg : (if b.sign = 0 then 1 else 0) = Layout.mpZpos ∨ (if b.sign = 0 then 1 else 0) = Layout.mpNeg := by
        simp only [Layout.mpZpos, Layout.mpNeg]; split <;> simp
      have hg := sSubIn_grown (a := b.withSign (if b.sign = 0 then 1 else 0))
        (hb.toShape.withSign (if b.sign = 0 then 1 else 0)) (by simp only [MpInt.withSign]; omega)
      obtain ⟨hv, hm⟩ := SSubPost.spec (hb.toShape.withSign (if b.sign = 0 then 1 else 0)) ha.toShape
        (by rw [MpInt.withSign_mag]; exact Nat.le_of_lt hab) (sSubIn_room _ _) hg.shape.alloc_lt
        (by rw [hg.sign, MpInt.withSign_sign]; exact hsg) hp
      refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
      rw [val_of_post (hg.sign ▸ hp.sign) hm, MpInt.withSign_sign, MpInt.withSign_mag]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega
    · have hp := h.ge hs hab
      rw [MpInt.withSign_self] at hp
      have hg := sSubIn_grown (a := a) hb.toShape (by omega)
      obtain ⟨hv, hm⟩ := SSubPost.spec ha.toShape hb.toShape (Nat.le_of_not_lt hab) (sSubIn_room a _)
        hg.shape.alloc_lt (by rw [hg.sign]; exact hb.sign_ok) hp
      refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
      rw [val_of_post (hg.sign ▸ hp.sign) hm]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega
  · have hp := h.diff hs
    have hg := sAddIn_grown (a := a) (b := b.withSign a.sign) (hb.toShape.withSign a.sign) h31
    obtain ⟨hv, hm⟩ := SAddPost.spec ha.toShape (hb.toShape.withSign a.sign) (sAddIn_room a _ _)
      hg.shape.alloc_lt (by rw [hg.sign, MpInt.withSign_sign]; exact ha.sign_ok) hp
    refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
    rw [val_of_post (hg.sign ▸ hp.sign) hm, MpInt.withSign_sign, MpInt.withSign_mag]
    simp only [Layout.mpNeg] at *
    rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega

end Tom
