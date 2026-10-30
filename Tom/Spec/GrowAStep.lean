import Tom.Spec.GrowHStep

/-!
# The growing in-place `mp_add` posts read as values

The `mp_add(a, b, a)` and `mp_add(a, b, b)` (`Api/MpAddGA.lean`, `Api/MpAddGB.lean`)
state the branch posts over the destination as the code leaves it before the tail call: its
sign set to `addSign a b` (so the operand it aliases has that sign in the tail callee).
-/

namespace Tom

open MpInt

theorem MpInt.withSign_self (a : MpInt) : a.withSign a.sign = a := rfl

theorem MpInt.withSign_mag (a : MpInt) (s : Nat) : (a.withSign s).mag = a.mag := rfl

theorem MpInt.withSign_used (a : MpInt) (s : Nat) : (a.withSign s).used = a.used := rfl

/-- **`mp_add(a, b, a)` with growth computes `a + b`**, leaves `a` valid and only grows it. -/
theorem AddG.specA {a b x : MpInt} (ha : a.Valid) (hb : b.Valid)
    (h31 : max a.used b.used + 1 < 2 ^ 31)
    (h : AddG a b (SAddPost (a.withSign a.sign) b (sAddIn (a.withSign a.sign) b (a.withSign a.sign)) x)
      (SSubPost b (a.withSign b.sign) (sSubIn b (a.withSign b.sign)) x)
      (SSubPost (a.withSign a.sign) b (sSubIn (a.withSign a.sign) (a.withSign a.sign)) x)) :
    x.Valid ∧ x.val = a.val + b.val ∧ a.alloc ≤ x.alloc := by
  have hsa := sign_cases ha.sign_ok
  have hsb := sign_cases hb.sign_ok
  rw [MpInt.val_eq (a := a), MpInt.val_eq (a := b)]
  by_cases hs : a.sign = b.sign
  · have hp := h.same hs
    rw [MpInt.withSign_self] at hp
    have hg := sAddIn_grown (a := a) (b := b) ha.toShape h31
    obtain ⟨hv, hm⟩ := SAddPost.spec ha.toShape hb.toShape (sAddIn_room a b _) hg.shape.alloc_lt
      (by rw [hg.sign]; exact ha.sign_ok) hp
    refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
    rw [val_of_post (hg.sign ▸ hp.sign) hm, ← hs]
    simp only [Layout.mpNeg] at *
    rcases hsa with h0 | h0 <;> simp [h0] <;> omega
  · by_cases hab : a.mag < b.mag
    · have hp := h.lt hs hab
      have hg := sSubIn_grown (a := b) (ha.toShape.withSign b.sign) (by omega)
      obtain ⟨hv, hm⟩ := SSubPost.spec hb.toShape (ha.toShape.withSign b.sign) (Nat.le_of_lt hab)
        (sSubIn_room b _) hg.shape.alloc_lt (by rw [hg.sign]; exact hb.sign_ok) hp
      refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
      rw [val_of_post (hg.sign ▸ hp.sign) hm, MpInt.withSign_sign, MpInt.withSign_mag]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega
    · have hp := h.ge hs hab
      rw [MpInt.withSign_self] at hp
      have hg := sSubIn_grown (a := a) ha.toShape (by omega)
      obtain ⟨hv, hm⟩ := SSubPost.spec ha.toShape hb.toShape (Nat.le_of_not_lt hab) (sSubIn_room a _)
        hg.shape.alloc_lt (by rw [hg.sign]; exact ha.sign_ok) hp
      refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
      rw [val_of_post (hg.sign ▸ hp.sign) hm]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega

/-- **`mp_add(a, b, b)` with growth computes `a + b`**, leaves `b` valid and only grows it. -/
theorem AddG.specB {a b x : MpInt} (ha : a.Valid) (hb : b.Valid)
    (h31 : max a.used b.used + 1 < 2 ^ 31)
    (h : AddG a b (SAddPost a (b.withSign a.sign) (sAddIn a (b.withSign a.sign) (b.withSign a.sign)) x)
      (SSubPost (b.withSign b.sign) a (sSubIn (b.withSign b.sign) (b.withSign b.sign)) x)
      (SSubPost a (b.withSign a.sign) (sSubIn a (b.withSign a.sign)) x)) :
    x.Valid ∧ x.val = a.val + b.val ∧ b.alloc ≤ x.alloc := by
  have hsa := sign_cases ha.sign_ok
  have hsb := sign_cases hb.sign_ok
  rw [MpInt.val_eq (a := a), MpInt.val_eq (a := b)]
  by_cases hs : a.sign = b.sign
  · have hp := h.same hs
    have hg := sAddIn_grown (a := a) (b := b.withSign a.sign) (hb.toShape.withSign a.sign) h31
    obtain ⟨hv, hm⟩ := SAddPost.spec ha.toShape (hb.toShape.withSign a.sign) (sAddIn_room a _ _)
      hg.shape.alloc_lt (by rw [hg.sign, MpInt.withSign_sign]; exact ha.sign_ok) hp
    refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
    rw [val_of_post (hg.sign ▸ hp.sign) hm, MpInt.withSign_sign, MpInt.withSign_mag, ← hs]
    simp only [Layout.mpNeg] at *
    rcases hsa with h0 | h0 <;> simp [h0] <;> omega
  · by_cases hab : a.mag < b.mag
    · have hp := h.lt hs hab
      rw [MpInt.withSign_self] at hp
      have hg := sSubIn_grown (a := b) hb.toShape (by omega)
      obtain ⟨hv, hm⟩ := SSubPost.spec hb.toShape ha.toShape (Nat.le_of_lt hab)
        (sSubIn_room b _) hg.shape.alloc_lt (by rw [hg.sign]; exact hb.sign_ok) hp
      refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
      rw [val_of_post (hg.sign ▸ hp.sign) hm]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega
    · have hp := h.ge hs hab
      have hg := sSubIn_grown (a := a) (hb.toShape.withSign a.sign) (by omega)
      obtain ⟨hv, hm⟩ := SSubPost.spec ha.toShape (hb.toShape.withSign a.sign) (Nat.le_of_not_lt hab)
        (sSubIn_room a _) hg.shape.alloc_lt (by rw [hg.sign, MpInt.withSign_sign]; exact ha.sign_ok) hp
      refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
      rw [val_of_post (hg.sign ▸ hp.sign) hm, MpInt.withSign_mag]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega

end Tom
