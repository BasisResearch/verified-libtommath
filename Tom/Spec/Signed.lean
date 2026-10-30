import Tom.Spec.Sub

/-!
# `mp_add` and `mp_sub`: the signed operations

`mp_add(a, b, c)` (`vendor/libtommath/bn_mp_add.c`) and `mp_sub(a, b, c)`
(`bn_mp_sub.c`) set `c->sign` and then call `s_mp_add` or `s_mp_sub` on the
magnitudes:

| call | signs | `mp_cmp_mag(a, b)` | `c->sign :=` | then |
|---|---|---|---|---|
| `mp_add` | `sa = sb` | — | `sa` | `s_mp_add(a, b, c)` |
| `mp_add` | `sa ≠ sb` | `MP_LT` | `sb` | `s_mp_sub(b, a, c)` |
| `mp_add` | `sa ≠ sb` | not `MP_LT` | `sa` | `s_mp_sub(a, b, c)` |
| `mp_sub` | `sa ≠ sb` | — | `sa` | `s_mp_add(a, b, c)` |
| `mp_sub` | `sa = sb` | not `MP_LT` | `sa` | `s_mp_sub(a, b, c)` |
| `mp_sub` | `sa = sb` | `MP_LT` | `sa == MP_ZPOS ? MP_NEG : MP_ZPOS` | `s_mp_sub(b, a, c)` |

The contracts below say, for each branch, that `c'` is what the low-level
routine leaves when started from `c` with the sign the branch sets (each
field is an implication from the branch condition, so exactly one applies).
A zero result is not a special case in the C: the low-level routine's
`mp_clamp` resets the sign to `MP_ZPOS` (e.g. `mp_add(-5, 5)` takes the
third row with `c->sign = MP_NEG`, and `mp_clamp` makes it `MP_ZPOS`).
-/

namespace Tom

open MpInt

/-- `c` with its sign field overwritten (`c->sign = s`). -/
def MpInt.withSign (c : MpInt) (s : Nat) : MpInt := { c with sign := s }

@[simp] theorem MpInt.withSign_sign (c : MpInt) (s : Nat) : (c.withSign s).sign = s := rfl
@[simp] theorem MpInt.withSign_alloc (c : MpInt) (s : Nat) : (c.withSign s).alloc = c.alloc := rfl

/-! ## Contracts -/

/-- What `mp_add(a, b, c)` leaves in `c`, by the branch it takes. -/
structure AddPost (a b c c' : MpInt) : Prop where
  same : a.sign = b.sign → SAddPost a b (c.withSign a.sign) c'
  lt : a.sign ≠ b.sign → cmpMag a b = .lt → SSubPost b a (c.withSign b.sign) c'
  ge : a.sign ≠ b.sign → cmpMag a b ≠ .lt → SSubPost a b (c.withSign a.sign) c'

/-- What `mp_sub(a, b, c)` leaves in `c`, by the branch it takes. -/
structure SubPost (a b c c' : MpInt) : Prop where
  diff : a.sign ≠ b.sign → SAddPost a b (c.withSign a.sign) c'
  ge : a.sign = b.sign → cmpMag a b ≠ .lt → SSubPost a b (c.withSign a.sign) c'
  lt : a.sign = b.sign → cmpMag a b = .lt →
    SSubPost b a (c.withSign (if a.sign = Layout.mpZpos then Layout.mpNeg else Layout.mpZpos)) c'

/-! ## Signs -/

theorem MpInt.mag_used_zero {x : MpInt} (h : x.used = 0) : x.mag = 0 := by
  simp [MpInt.mag, h, natUpTo]

/-- A result whose sign was set to `s` and then reset by `mp_clamp` when
zero has the value `±mag` with the sign `s`. -/
theorem MpInt.val_of_sign {x : MpInt} {s : Nat}
    (h : x.sign = if x.used = 0 then Layout.mpZpos else s) :
    x.val = if s = Layout.mpNeg then -(x.mag : Int) else x.mag := by
  unfold MpInt.val
  by_cases hu : x.used = 0
  · simp [h, hu, MpInt.mag_used_zero hu, Layout.mpZpos, Layout.mpNeg]
  · simp [h, hu]

theorem sign_cases {s : Nat} (h : s = Layout.mpZpos ∨ s = Layout.mpNeg) : s = 0 ∨ s = 1 := by
  simpa [Layout.mpZpos, Layout.mpNeg] using h

/-- The value of `c'` from a `s_mp_add` or `s_mp_sub` contract, given its
magnitude. -/
theorem val_of_post {c' : MpInt} {s : Nat} {m : Nat}
    (hsign : c'.sign = if c'.used = 0 then Layout.mpZpos else s) (hmag : c'.mag = m) :
    c'.val = if s = Layout.mpNeg then -(m : Int) else m := by
  rw [MpInt.val_of_sign hsign, hmag]

theorem MpInt.val_eq {a : MpInt} : a.val = if a.sign = Layout.mpNeg then -(a.mag : Int) else a.mag := rfl

/-! ## `mp_add` -/

/-- `mp_add` computes `c = a + b` and leaves `c` valid. -/
theorem AddPost.spec {a b c c' : MpInt} (ha : a.Valid) (hb : b.Valid)
    (hroom : max a.used b.used + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (h : AddPost a b c c') :
    c'.Valid ∧ c'.val = a.val + b.val := by
  have hsa := sign_cases ha.sign_ok
  have hsb := sign_cases hb.sign_ok
  rw [MpInt.val_eq (a := a), MpInt.val_eq (a := b)]
  by_cases hs : a.sign = b.sign
  · have hp := h.same hs
    obtain ⟨hv, hm⟩ := SAddPost.spec (c := c.withSign a.sign) ha.toShape hb.toShape hroom hc
      ha.sign_ok hp
    refine ⟨hv, ?_⟩
    rw [val_of_post hp.sign hm, ← hs]
    simp only [Layout.mpNeg] at *
    rcases hsa with h0 | h0 <;> simp [h0] <;> omega
  · have hcmp := cmpMag_eq ha hb
    by_cases hlt : cmpMag a b = .lt
    · have hp := h.lt hs hlt
      have hab : a.mag < b.mag := Nat.compare_eq_lt.1 (hcmp ▸ hlt)
      obtain ⟨hv, hm⟩ := SSubPost.spec (c := c.withSign b.sign) hb.toShape ha.toShape (Nat.le_of_lt hab)
        (by simp only [MpInt.withSign_alloc]; omega) hc hb.sign_ok hp
      refine ⟨hv, ?_⟩
      rw [val_of_post hp.sign hm]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega
    · have hp := h.ge hs hlt
      have hab : b.mag ≤ a.mag := by
        rcases Nat.lt_or_ge a.mag b.mag with h' | h'
        · exact absurd (hcmp ▸ Nat.compare_eq_lt.2 h') hlt
        · exact h'
      obtain ⟨hv, hm⟩ := SSubPost.spec (c := c.withSign a.sign) ha.toShape hb.toShape hab
        (by simp only [MpInt.withSign_alloc]; omega)
        hc ha.sign_ok hp
      refine ⟨hv, ?_⟩
      rw [val_of_post hp.sign hm]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega

/-! ## `mp_sub` -/

/-- `mp_sub` computes `c = a - b` and leaves `c` valid. -/
theorem SubPost.spec {a b c c' : MpInt} (ha : a.Valid) (hb : b.Valid)
    (hroom : max a.used b.used + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (h : SubPost a b c c') :
    c'.Valid ∧ c'.val = a.val - b.val := by
  have hsa := sign_cases ha.sign_ok
  have hsb := sign_cases hb.sign_ok
  rw [MpInt.val_eq (a := a), MpInt.val_eq (a := b)]
  by_cases hs : a.sign = b.sign
  · have hcmp := cmpMag_eq ha hb
    by_cases hlt : cmpMag a b = .lt
    · have hp := h.lt hs hlt
      have hab : a.mag < b.mag := Nat.compare_eq_lt.1 (hcmp ▸ hlt)
      have hsn : (if a.sign = Layout.mpZpos then Layout.mpNeg else Layout.mpZpos) = Layout.mpZpos ∨
          (if a.sign = Layout.mpZpos then Layout.mpNeg else Layout.mpZpos) = Layout.mpNeg := by
        split
        · exact Or.inr rfl
        · exact Or.inl rfl
      obtain ⟨hv, hm⟩ := SSubPost.spec
        (c := c.withSign (if a.sign = Layout.mpZpos then Layout.mpNeg else Layout.mpZpos))
        hb.toShape ha.toShape (Nat.le_of_lt hab) (by simp only [MpInt.withSign_alloc]; omega) hc hsn hp
      refine ⟨hv, ?_⟩
      rw [val_of_post hp.sign hm, ← hs]
      simp only [Layout.mpNeg, Layout.mpZpos] at *
      rcases hsa with h0 | h0 <;> simp [h0] <;> omega
    · have hp := h.ge hs hlt
      have hab : b.mag ≤ a.mag := by
        rcases Nat.lt_or_ge a.mag b.mag with h' | h'
        · exact absurd (hcmp ▸ Nat.compare_eq_lt.2 h') hlt
        · exact h'
      obtain ⟨hv, hm⟩ := SSubPost.spec (c := c.withSign a.sign) ha.toShape hb.toShape hab
        (by simp only [MpInt.withSign_alloc]; omega)
        hc ha.sign_ok hp
      refine ⟨hv, ?_⟩
      rw [val_of_post hp.sign hm, ← hs]
      simp only [Layout.mpNeg] at *
      rcases hsa with h0 | h0 <;> simp [h0] <;> omega
  · have hp := h.diff hs
    obtain ⟨hv, hm⟩ := SAddPost.spec (c := c.withSign a.sign) ha.toShape hb.toShape hroom hc
      ha.sign_ok hp
    refine ⟨hv, ?_⟩
    rw [val_of_post hp.sign hm]
    simp only [Layout.mpNeg] at *
    rcases hsa with h0 | h0 <;> rcases hsb with h1 | h1 <;> simp [h0, h1] at hs ⊢ <;> omega

end Tom
