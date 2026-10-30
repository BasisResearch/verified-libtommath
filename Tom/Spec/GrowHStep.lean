import Tom.Spec.AddGStep
import Tom.Spec.Grow6Step
import Tom.Spec.Signed

/-!
# The growing `mp_add` / `mp_lshd` posts read as values

The growing contracts state what the code leaves branch by branch, from the grown
input (`AddG` over `sAddIn`/`sSubIn`, `LshdPost (lshdIn a k) k`). Their callers (karatsuba's
named premises `Api/MpAddH.lean`, `Api/MpLshdH.lean`) want the value: `AddG.spec` (valid,
`a + b`, grown only) and `LshdPost.grown_spec` (valid, `|a| radix^k`, the sign kept, grown only).
-/

namespace Tom

open MpInt

theorem MpInt.mag_congr {a A : MpInt} (hu : A.used = a.used) (hd : A.digit = a.digit) : A.mag = a.mag := by
  unfold MpInt.mag; rw [hu, hd]

theorem GrownOf.valid {a A : MpInt} (ha : a.Valid) (h : GrownOf a A) : A.Valid :=
  { h.shape with
    top := fun hu => by rw [h.digit, h.used]; exact ha.top (h.used ▸ hu)
    sign_ok := h.sign ▸ ha.sign_ok
    zero_pos := fun hu => by rw [h.sign]; exact ha.zero_pos (h.used ▸ hu) }

/-- **`mp_add(a, b, c)` with growth computes `a + b`**, leaves `c` valid and only grows it. -/
theorem AddG.spec {a b c x : MpInt} (ha : a.Valid) (hb : b.Valid) (hc : c.Shape)
    (h31 : max a.used b.used + 1 < 2 ^ 31)
    (h : AddG a b (SAddPost a b (sAddIn a b (c.withSign a.sign)) x)
      (SSubPost b a (sSubIn b (c.withSign b.sign)) x) (SSubPost a b (sSubIn a (c.withSign a.sign)) x)) :
    x.Valid ∧ x.val = a.val + b.val ∧ c.alloc ≤ x.alloc := by
  have hsa := sign_cases ha.sign_ok
  have hsb := sign_cases hb.sign_ok
  rw [MpInt.val_eq (a := a), MpInt.val_eq (a := b)]
  by_cases hs : a.sign = b.sign
  · have hp := h.same hs
    have hg := sAddIn_grown (a := a) (b := b) (hc.withSign a.sign) h31
    obtain ⟨hv, hm⟩ := SAddPost.spec ha.toShape hb.toShape (sAddIn_room a b _) hg.shape.alloc_lt
      (by rw [hg.sign]; exact ha.sign_ok) hp
    refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
    rw [val_of_post (hg.sign ▸ hp.sign) hm, MpInt.withSign_sign, ← hs]
    simp only [Layout.mpNeg] at *
    rcases hsa with h0 | h0 <;> simp [h0] <;> omega
  · by_cases hab : a.mag < b.mag
    · have hp := h.lt hs hab
      have hg := sSubIn_grown (a := b) (hc.withSign b.sign) (by omega)
      obtain ⟨hv, hm⟩ := SSubPost.spec hb.toShape ha.toShape (Nat.le_of_lt hab) (sSubIn_room b _)
        hg.shape.alloc_lt (by rw [hg.sign]; exact hb.sign_ok) hp
      refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
      rw [val_of_post (hg.sign ▸ hp.sign) hm, MpInt.withSign_sign]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega
    · have hp := h.ge hs hab
      have hg := sSubIn_grown (a := a) (hc.withSign a.sign) (by omega)
      obtain ⟨hv, hm⟩ := SSubPost.spec ha.toShape hb.toShape (Nat.le_of_not_lt hab) (sSubIn_room a _)
        hg.shape.alloc_lt (by rw [hg.sign]; exact ha.sign_ok) hp
      refine ⟨hv, ?_, by rw [hp.alloc]; exact hg.alloc⟩
      rw [val_of_post (hg.sign ▸ hp.sign) hm, MpInt.withSign_sign]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega

/-- **`mp_lshd(a, k)` with growth multiplies by `radix^k`**, keeps the sign, only grows `a`. -/
theorem LshdPost.grown_spec {a a' : MpInt} {k : Nat} (ha : a.Valid) (h31 : a.used + k < 2 ^ 31)
    (h : LshdPost (lshdIn a k) k a') :
    a'.Valid ∧ a'.mag = a.mag * radix ^ k ∧ a'.sign = a.sign ∧ a.alloc ≤ a'.alloc := by
  have hg := lshdIn_grown ha.toShape h31
  have hv := hg.valid ha
  have hm := MpInt.mag_congr hg.used hg.digit
  by_cases h0 : k = 0 ∨ (lshdIn a k).used = 0
  · have e := h.noop h0
    subst e
    refine ⟨hv, ?_, hg.sign, hg.alloc⟩
    rcases h0 with h0 | h0
    · rw [hm, h0]; simp
    · rw [MpInt.mag_used_zero h0, MpInt.mag_used_zero (hg.used ▸ h0)]; simp
  · have hk : 0 < k := by omega
    have hu : 0 < (lshdIn a k).used := by omega
    have hsh := h.shift hk hu
    obtain ⟨hv', hm'⟩ := hsh.spec hv (lshdIn_room a hk (hg.used ▸ hu)) hu
    exact ⟨hv', by rw [hm', hm], by rw [hsh.sign, hg.sign], by rw [hsh.alloc]; exact hg.alloc⟩

end Tom
