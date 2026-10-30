import Tom.Spec.GrowAStep

/-!
# `mp_sub(a, b, c)` with growth: the branch's sign and size, the value

`mp_sub` stores `c->sign` (`subSign`: `a->sign` for unequal signs; for equal signs `b->sign`
when `|a| ≥ |b|`, else its flip by `seqz`) and tail-calls `s_mp_add(a, b, c)` (unequal signs),
`s_mp_sub(b, a, c)` (`|a| < |b|`) or `s_mp_sub(a, b, c)`, which grow the destination to
`subSize` when short. `SubG a b D L G`: what holds in each branch, each the tail callee's post;
`SubG.spec` reads it as the value `a − b` (as `AddG.spec`, `Tom/Spec/GrowHStep.lean`).
-/

namespace Tom

open MpInt

/-- The sign `mp_sub(a, b, c)` gives `c` before its tail call. -/
def subSign (a b : MpInt) : Nat :=
  if a.sign = b.sign then (if a.mag < b.mag then (if b.sign = 0 then 1 else 0) else b.sign) else a.sign

/-- The size the tail callee grows `c` to (when `c->alloc` is less). -/
def subSize (a b : MpInt) : Nat :=
  if a.sign = b.sign then (if a.mag < b.mag then b.used else a.used) else max a.used b.used + 1

/-- What `mp_sub` leaves, by branch. -/
structure SubG (a b : MpInt) (D L G : Prop) : Prop where
  diff : a.sign ≠ b.sign → D
  lt : a.sign = b.sign → a.mag < b.mag → L
  ge : a.sign = b.sign → ¬ a.mag < b.mag → G

theorem subSign_diff {a b : MpInt} (h : a.sign ≠ b.sign) : subSign a b = a.sign := by simp [subSign, h]
theorem subSign_lt {a b : MpInt} (h : a.sign = b.sign) (hl : a.mag < b.mag) :
    subSign a b = if b.sign = 0 then 1 else 0 := by simp [subSign, h, hl]
theorem subSign_ge {a b : MpInt} (h : a.sign = b.sign) (hl : ¬ a.mag < b.mag) : subSign a b = b.sign := by
  simp [subSign, h, hl]
theorem subSize_diff {a b : MpInt} (h : a.sign ≠ b.sign) : subSize a b = max a.used b.used + 1 := by
  simp [subSize, h]
theorem subSize_lt {a b : MpInt} (h : a.sign = b.sign) (hl : a.mag < b.mag) : subSize a b = b.used := by
  simp [subSize, h, hl]
theorem subSize_ge {a b : MpInt} (h : a.sign = b.sign) (hl : ¬ a.mag < b.mag) : subSize a b = a.used := by
  simp [subSize, h, hl]

/-- **`mp_sub(a, b, c)` with growth computes `a − b`**, leaves `c` valid and only grows it. -/
theorem SubG.spec {a b c x : MpInt} (ha : a.Valid) (hb : b.Valid) (hc : c.Shape)
    (h31 : max a.used b.used + 1 < 2 ^ 31)
    (h : SubG a b (SAddPost a b (sAddIn a b (c.withSign a.sign)) x)
      (SSubPost b a (sSubIn b (c.withSign (if b.sign = 0 then 1 else 0))) x)
      (SSubPost a b (sSubIn a (c.withSign b.sign)) x)) :
    x.Valid ∧ x.val = a.val - b.val ∧ c.alloc ≤ x.alloc := by
  have hsa := sign_cases ha.sign_ok
  have hsb := sign_cases hb.sign_ok
  rw [MpInt.val_eq (a := a), MpInt.val_eq (a := b)]
  by_cases hs : a.sign = b.sign
  · by_cases hab : a.mag < b.mag
    · have hp := h.lt hs hab
      have hg := sSubIn_grown (a := b) (hc.withSign (if b.sign = 0 then 1 else 0)) (by omega)
      have hsg : (if b.sign = 0 then 1 else 0) = Layout.mpZpos ∨ (if b.sign = 0 then 1 else 0) = Layout.mpNeg := by
        simp only [Layout.mpZpos, Layout.mpNeg]; split <;> simp
      obtain ⟨hv, hm⟩ := SSubPost.spec hb.toShape ha.toShape (Nat.le_of_lt hab) (sSubIn_room b _)
        hg.shape.alloc_lt (by rw [hg.sign]; exact hsg) hp
      refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
      rw [val_of_post (hg.sign ▸ hp.sign) hm, MpInt.withSign_sign]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega
    · have hp := h.ge hs hab
      have hg := sSubIn_grown (a := a) (hc.withSign b.sign) (by omega)
      obtain ⟨hv, hm⟩ := SSubPost.spec ha.toShape hb.toShape (Nat.le_of_not_lt hab) (sSubIn_room a _)
        hg.shape.alloc_lt (by rw [hg.sign]; exact hb.sign_ok) hp
      refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
      rw [val_of_post (hg.sign ▸ hp.sign) hm, MpInt.withSign_sign]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega
  · have hp := h.diff hs
    have hg := sAddIn_grown (a := a) (b := b) (hc.withSign a.sign) h31
    obtain ⟨hv, hm⟩ := SAddPost.spec ha.toShape hb.toShape (sAddIn_room a b _) hg.shape.alloc_lt
      (by rw [hg.sign]; exact ha.sign_ok) hp
    refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
    rw [val_of_post (hg.sign ▸ hp.sign) hm, MpInt.withSign_sign]
    simp only [Layout.mpNeg] at *
    rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega

/-- **`mp_sub(a, b, a)` with growth computes `a − b`**, leaves `a` valid and only grows it. -/
theorem SubG.specA {a b x : MpInt} (ha : a.Valid) (hb : b.Valid)
    (h31 : max a.used b.used + 1 < 2 ^ 31)
    (h : SubG a b (SAddPost (a.withSign a.sign) b (sAddIn (a.withSign a.sign) b (a.withSign a.sign)) x)
      (SSubPost b (a.withSign (if b.sign = 0 then 1 else 0)) (sSubIn b (a.withSign (if b.sign = 0 then 1 else 0))) x)
      (SSubPost (a.withSign b.sign) b (sSubIn (a.withSign b.sign) (a.withSign b.sign)) x)) :
    x.Valid ∧ x.val = a.val - b.val ∧ a.alloc ≤ x.alloc := by
  have hsa := sign_cases ha.sign_ok
  have hsb := sign_cases hb.sign_ok
  rw [MpInt.val_eq (a := a), MpInt.val_eq (a := b)]
  by_cases hs : a.sign = b.sign
  · by_cases hab : a.mag < b.mag
    · have hp := h.lt hs hab
      have hg := sSubIn_grown (a := b) (ha.toShape.withSign (if b.sign = 0 then 1 else 0)) (by omega)
      have hsg : (if b.sign = 0 then 1 else 0) = Layout.mpZpos ∨ (if b.sign = 0 then 1 else 0) = Layout.mpNeg := by
        simp only [Layout.mpZpos, Layout.mpNeg]; split <;> simp
      obtain ⟨hv, hm⟩ := SSubPost.spec hb.toShape (ha.toShape.withSign (if b.sign = 0 then 1 else 0)) (Nat.le_of_lt hab)
        (sSubIn_room b _) hg.shape.alloc_lt (by rw [hg.sign]; exact hsg) hp
      refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
      rw [val_of_post (hg.sign ▸ hp.sign) hm, MpInt.withSign_sign, MpInt.withSign_mag]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega
    · have hp := h.ge hs hab
      rw [← hs, MpInt.withSign_self] at hp
      have hg := sSubIn_grown (a := a) ha.toShape (by omega)
      obtain ⟨hv, hm⟩ := SSubPost.spec ha.toShape hb.toShape (Nat.le_of_not_lt hab) (sSubIn_room a _)
        hg.shape.alloc_lt (by rw [hg.sign]; exact ha.sign_ok) hp
      refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
      rw [val_of_post (hg.sign ▸ hp.sign) hm]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega
  · have hp := h.diff hs
    rw [MpInt.withSign_self] at hp
    have hg := sAddIn_grown (a := a) (b := b) ha.toShape h31
    obtain ⟨hv, hm⟩ := SAddPost.spec ha.toShape hb.toShape (sAddIn_room a b _) hg.shape.alloc_lt
      (by rw [hg.sign]; exact ha.sign_ok) hp
    refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
    rw [val_of_post (hg.sign ▸ hp.sign) hm]
    simp only [Layout.mpNeg] at *
    rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega

end Tom
