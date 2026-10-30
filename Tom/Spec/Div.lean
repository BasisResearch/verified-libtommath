import Tom.Spec.DivKnuth

/-!
# `mp_div` and `mp_mod`: the contracts

`mp_div(a, b, c, d)` (`bn_mp_div.c`, the normalised long division, `Tom/Spec/DivKnuth.lean`)
with `b ≠ 0`:

* `|a| < |b|` (`mp_cmp_mag(a, b) == MP_LT`): `d = a` (`mp_copy`), `c = 0` (`mp_zero`).
* otherwise: `q` from `mp_init_size(&q, a->used + 2)`, `q.used = a->used + 2`; `x`, `y`
  copies of `a`, `b` with sign `MP_ZPOS`, both shifted by `norm` bits (`mp_mul_2d`);
  the loop leaves `q`'s digits `natDigit (A / B)` and `x = A % B` (`DivInv.finish`);
  then `x.sign = (x.used == 0) ? MP_ZPOS : a->sign`; `c`: `mp_clamp(&q)`,
  `mp_exch(&q, c)`, `c->sign = neg` (`a->sign == b->sign ? MP_ZPOS : MP_NEG`, not reset:
  `q ≠ 0`); `d`: `mp_div_2d(&x, norm, &x, NULL)`, `mp_exch(&x, d)`.

So the quotient truncates toward zero and the remainder has the sign of `a`
(`c = a.tdiv b`, `d = a.tmod b`, `c * b + d = a`, `|d| < |b|`: `div_spec`).

`mp_mod(a, b, c)` (`bn_mp_mod.c`): `t` the remainder of `mp_div(a, b, NULL, &t)`; if `t`
is zero or has the sign of `b`, `c = t` (`mp_exch`), else `c = b + t` (`mp_add`).
This is the floor convention: `c = a.fmod b`, with the sign of `b` (`ModPost.spec`).

As in `DivD.lean`, the quotient and the remainder are separate structures (each
pointer may be `NULL` in the C); the copy/zero cases assume the destination has room
(D5); aliasing is out of scope (D6). The big cases are stated over the values the
callees leave (`DivBigRem.of_div2d`, `DivBigQuot.of_loop` connect them to the loop).
-/

namespace Tom

open MpInt

/-! ## Signs -/

theorem sval_zero (m : Nat) : sval Layout.mpZpos m = m := rfl
theorem sval_neg (m : Nat) : sval Layout.mpNeg m = -(m : Int) := rfl
theorem sval_mag_zero (s : Nat) : sval s 0 = 0 := by unfold sval; split <;> simp

theorem natAbs_sval (s m : Nat) : (sval s m).natAbs = m := by
  unfold sval; split <;> simp

/-- The sign `mp_div` gives the quotient. -/
def divSign (sa sb : Nat) : Nat := if sa = sb then Layout.mpZpos else Layout.mpNeg

theorem sval_tdiv_sval {sa sb : Nat} (ha : sa = Layout.mpZpos ∨ sa = Layout.mpNeg)
    (hb : sb = Layout.mpZpos ∨ sb = Layout.mpNeg) (A B : Nat) :
    (sval sa A).tdiv (sval sb B) = sval (divSign sa sb) (A / B) := by
  unfold divSign
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [sval, Layout.mpZpos, Layout.mpNeg, Int.tdiv_neg, Int.neg_tdiv, ← Int.ofNat_tdiv]

theorem sval_tmod_sval {sa : Nat} (sb : Nat) (A B : Nat) :
    (sval sa A).tmod (sval sb B) = sval sa (A % B) := by
  unfold sval
  split <;> split <;> simp only [Int.tmod_neg, Int.neg_tmod, ← Int.ofNat_tmod]

/-! ## `mp_div` -/

/-- The quotient of the big case: `q` (`a->used + 2` digits from `mp_init_size`, the
digits of `|a| / |b|`), clamped, with the sign `neg` written after `mp_exch`. -/
structure DivBigQuot (a b c' : MpInt) : Prop where
  alloc : c'.alloc = max 3 (a.used + 2)
  len : c'.digits.length = max 3 (a.used + 2)
  digit : c'.digit = natDigit (a.mag / b.mag)
  used : c'.used = clampUsed (natDigit (a.mag / b.mag)) (a.used + 2)
  sign : c'.sign = divSign a.sign b.sign

/-- The remainder of the big case: `x` after `mp_div_2d(&x, norm, &x, NULL)`. -/
structure DivBigRem (a b d' : MpInt) : Prop where
  valid : d'.Valid
  mag : d'.mag = a.mag % b.mag
  sign : d'.sign = if d'.used = 0 then Layout.mpZpos else a.sign

/-- What `mp_div(a, b, c, d)` (`b ≠ 0`) leaves in `c` (non-`NULL`). -/
structure DivQuot (a b c c' : MpInt) : Prop where
  small : a.mag < b.mag → ClampedTo c' c.alloc (fun _ => 0) 0 Layout.mpZpos
  big : b.mag ≤ a.mag → DivBigQuot a b c'

/-- What `mp_div(a, b, c, d)` (`b ≠ 0`) leaves in `d` (non-`NULL`). -/
structure DivRem (a b d d' : MpInt) : Prop where
  small : a.mag < b.mag → ClampedTo d' d.alloc a.digit a.used a.sign
  big : b.mag ≤ a.mag → DivBigRem a b d'

/-- The quotient's digits from the normalised operands are those of `|a| / |b|`. -/
theorem DivBigQuot.of_loop {a b c' : MpInt} {nm : Nat}
    (halloc : c'.alloc = max 3 (a.used + 2)) (hlen : c'.digits.length = max 3 (a.used + 2))
    (hdig : c'.digit = natDigit (a.mag * 2 ^ nm / (b.mag * 2 ^ nm)))
    (hused : c'.used = clampUsed (natDigit (a.mag * 2 ^ nm / (b.mag * 2 ^ nm))) (a.used + 2))
    (hsign : c'.sign = divSign a.sign b.sign) : DivBigQuot a b c' := by
  rw [norm_quot _ _ _ (Nat.two_pow_pos nm)] at hdig hused
  exact ⟨halloc, hlen, hdig, hused, hsign⟩

/-- The remainder from the normalised `x = A % B` (with `x.sign` set to `a`'s unless zero)
after `mp_div_2d(&x, norm, &x, NULL)`. -/
theorem DivBigRem.of_div2d {a b x d' : MpInt} {nm : Nat} (hx : x.Valid)
    (hxm : x.mag = a.mag * 2 ^ nm % (b.mag * 2 ^ nm))
    (hxs : x.sign = if x.used = 0 then Layout.mpZpos else a.sign) (h : Div2dPost x nm x d') :
    DivBigRem a b d' := by
  obtain ⟨hv, hm, _⟩ := Div2dPost.spec hx hx.used_le hx.alloc_lt h
  rw [hxm, norm_rem _ _ _ (Nat.two_pow_pos nm)] at hm
  refine ⟨hv, hm, ?_⟩
  have hs : d'.sign = if d'.used = 0 then Layout.mpZpos else x.sign := h.sign
  rw [hs]
  by_cases hu : d'.used = 0
  · simp [hu]
  · simp only [hu, ite_false]
    have hpos : 0 < d'.mag := Nat.lt_of_lt_of_le (radix_pow_pos _) (MpInt.mag_ge hv (by omega))
    have hxu : x.used ≠ 0 := by
      intro h0
      have h1 := MpInt.mag_used_zero h0
      rw [hxm, Nat.mul_mod_mul_right] at h1
      have h2 : a.mag % b.mag = 0 := by
        rcases Nat.mul_eq_zero.1 h1 with h' | h'
        · exact h'
        · exact absurd h' (Nat.ne_of_gt (Nat.two_pow_pos nm))
      rw [hm, h2] at hpos; exact Nat.lt_irrefl _ hpos
    rw [hxs, if_neg hxu]

theorem natDigit_quot_lt {a b : MpInt} (ha : a.Shape) (hb : 0 < b.mag) (n : Nat) (hn : a.used ≤ n) :
    a.mag / b.mag < radix ^ n :=
  Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
    (Nat.lt_of_lt_of_le (MpInt.mag_lt ha) (Nat.pow_le_pow_right radix_pos hn))

theorem MpInt.Valid.mag_pos {b : MpInt} (hb : b.Valid) (hu : 0 < b.used) : 0 < b.mag :=
  Nat.lt_of_lt_of_le (radix_pow_pos _) (MpInt.mag_ge hb hu)

/-- `mp_div` computes `|c| = |a| / |b|` and `c = a / b` truncated toward zero. -/
theorem DivQuot.spec {a b c c' : MpInt} (ha : a.Valid) (hb : b.Valid) (hb0 : 0 < b.used)
    (hau : a.used + 2 < 2 ^ 31) (hc : c.alloc < 2 ^ 31) (h : DivQuot a b c c') :
    c'.Valid ∧ c'.mag = a.mag / b.mag ∧ c'.val = a.val.tdiv b.val := by
  have hbm := hb.mag_pos hb0
  rw [MpInt.val_sval a, MpInt.val_sval b, sval_tdiv_sval ha.sign_ok hb.sign_ok]
  by_cases hs : a.mag < b.mag
  · obtain ⟨hv, hm, _⟩ := ClampedTo.spec (h.small hs) (fun _ => radix_pos) (fun _ _ => rfl) (Nat.zero_le _) hc
      (Or.inl rfl)
    have hq : a.mag / b.mag = 0 := Nat.div_eq_of_lt hs
    rw [hq, sval_mag_zero]
    refine ⟨hv, by rw [hm]; rfl, ?_⟩
    rw [MpInt.val_sval, hm]; exact sval_mag_zero _
  · have hp := h.big (Nat.le_of_not_lt hs)
    have hQ : 0 < a.mag / b.mag := Nat.div_pos (Nat.le_of_not_lt hs) hbm
    have hlt := natDigit_quot_lt ha.toShape hbm (a.used + 2) (by omega)
    have hu : c'.used ≠ 0 := by
      intro h0
      have := natUpTo_clampUsed (natDigit (a.mag / b.mag)) (a.used + 2)
      rw [← hp.used, h0, natUpTo, natUpTo_natDigit, Nat.mod_eq_of_lt hlt] at this
      omega
    have hsg : divSign a.sign b.sign = Layout.mpZpos ∨ divSign a.sign b.sign = Layout.mpNeg := by
      unfold divSign; split
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hct : ClampedTo c' (max 3 (a.used + 2)) (natDigit (a.mag / b.mag)) (a.used + 2) (divSign a.sign b.sign) :=
      ⟨hp.alloc, hp.len, hp.digit, hp.used, by rw [hp.sign, if_neg hu]⟩
    have hal : max 3 (a.used + 2) < 2 ^ 31 := by omega
    obtain ⟨hv, hm, hval⟩ := hct.spec_natDigit hlt (Nat.le_max_right _ _) hal hsg
    exact ⟨hv, hm, hval⟩

/-- `mp_div` leaves `|d| = |a| mod |b|` with the sign of `a`: `d = a.tmod b`. -/
theorem DivRem.spec {a b d d' : MpInt} (ha : a.Valid) (hb : b.Valid) (hb0 : 0 < b.used)
    (hroom : a.used ≤ d.alloc) (hd : d.alloc < 2 ^ 31) (h : DivRem a b d d') :
    d'.Valid ∧ d'.mag = a.mag % b.mag ∧ d'.val = a.val.tmod b.val := by
  rw [MpInt.val_sval a, MpInt.val_sval b, sval_tmod_sval]
  by_cases hs : a.mag < b.mag
  · obtain ⟨hv, hm, hval⟩ := ClampedTo.spec (h.small hs) ha.digit_lt ha.high_zero hroom hd ha.sign_ok
    have hr : a.mag % b.mag = a.mag := Nat.mod_eq_of_lt hs
    rw [hr]
    exact ⟨hv, hm, hval⟩
  · have hp := h.big (Nat.le_of_not_lt hs)
    refine ⟨hp.valid, hp.mag, ?_⟩
    rw [MpInt.val_of_sign hp.sign, hp.mag]; rfl

/-- **`mp_div`**: `c * b + d = a` and `|d| < |b|`. -/
theorem div_spec {a b c c' d d' : MpInt} (ha : a.Valid) (hb : b.Valid) (hb0 : 0 < b.used)
    (hau : a.used + 2 < 2 ^ 31) (hc : c.alloc < 2 ^ 31) (hroom : a.used ≤ d.alloc) (hd : d.alloc < 2 ^ 31)
    (hq : DivQuot a b c c') (hr : DivRem a b d d') :
    c'.val * b.val + d'.val = a.val ∧ d'.mag < b.mag := by
  obtain ⟨_, _, hcv⟩ := DivQuot.spec ha hb hb0 hau hc hq
  obtain ⟨_, hdm, hdv⟩ := DivRem.spec ha hb hb0 hroom hd hr
  refine ⟨by rw [hcv, hdv]; exact Int.tdiv_mul_add_tmod _ _, ?_⟩
  rw [hdm]; exact Nat.mod_lt _ (hb.mag_pos hb0)

/-! ## `mp_mod` -/

/-- A valid `mp_int` with value `v`. -/
structure HasVal (x : MpInt) (v : Int) : Prop where
  valid : x.Valid
  val : x.val = v

/-- What `mp_mod(a, b, c)` leaves in `c` (`b ≠ 0`): with `t = a.tmod b` (the
remainder `mp_div` leaves, `DivRem.spec`), `t` itself when it is zero or has `b`'s
sign (`a`'s sign when nonzero), else `b + t` (`mp_add`, `AddPost.spec`). -/
structure ModPost (a b c' : MpInt) : Prop where
  keep : (a.mag % b.mag = 0 ∨ a.sign = b.sign) → HasVal c' (a.val.tmod b.val)
  add : ¬ (a.mag % b.mag = 0 ∨ a.sign = b.sign) → HasVal c' (b.val + a.val.tmod b.val)

/-- `mp_mod` computes the floor remainder `c = a.fmod b`. -/
theorem ModPost.spec {a b c' : MpInt} (ha : a.Valid) (hb : b.Valid) (hb0 : 0 < b.used) (h : ModPost a b c') :
    HasVal c' (a.val.fmod b.val) := by
  have hB := hb.mag_pos hb0
  have hdvd : b.val ∣ a.val ↔ a.mag % b.mag = 0 := by
    rw [MpInt.val_sval a, MpInt.val_sval b, ← Int.natAbs_dvd_natAbs, natAbs_sval, natAbs_sval,
      Nat.dvd_iff_mod_eq_zero]
  rw [Int.fmod_eq_tmod]
  by_cases hR : a.mag % b.mag = 0
  · rw [if_pos (hdvd.2 hR), Int.add_zero]; exact h.keep (Or.inl hR)
  · rw [if_neg (fun hh => hR (hdvd.1 hh))]
    have hA : 0 < a.mag := by
      rcases Nat.eq_zero_or_pos a.mag with h0 | h0
      · rw [h0, Nat.zero_mod] at hR; exact absurd rfl hR
      · exact h0
    rcases sign_cases ha.sign_ok with hsa | hsa <;> rcases sign_cases hb.sign_ok with hsb | hsb
    · have := h.keep (Or.inr (by rw [hsa, hsb]))
      rw [MpInt.val_sval a, MpInt.val_sval b, hsa, hsb] at this ⊢
      simp only [show sval 0 a.mag = (a.mag : Int) from rfl, show sval 0 b.mag = (b.mag : Int) from rfl] at this ⊢
      rw [if_pos (by omega), if_pos (by omega), Int.add_zero]; exact this
    · have := h.add (by rw [hsa, hsb]; omega)
      rw [MpInt.val_sval a, MpInt.val_sval b, hsa, hsb] at this ⊢
      simp only [show sval 0 a.mag = (a.mag : Int) from rfl, show sval 1 b.mag = -(b.mag : Int) from rfl] at this ⊢
      rw [if_pos (by omega), if_neg (by omega), Int.add_comm]; exact this
    · have := h.add (by rw [hsa, hsb]; omega)
      rw [MpInt.val_sval a, MpInt.val_sval b, hsa, hsb] at this ⊢
      simp only [show sval 1 a.mag = -(a.mag : Int) from rfl, show sval 0 b.mag = (b.mag : Int) from rfl] at this ⊢
      rw [if_neg (by omega), if_pos (by omega), show ((b.mag : Int)).natAbs = b.mag from rfl, Int.add_comm]; exact this
    · have := h.keep (Or.inr (by rw [hsa, hsb]))
      rw [MpInt.val_sval a, MpInt.val_sval b, hsa, hsb] at this ⊢
      simp only [show sval 1 a.mag = -(a.mag : Int) from rfl, show sval 1 b.mag = -(b.mag : Int) from rfl] at this ⊢
      rw [if_neg (by omega), if_neg (by omega)]
      have h0 : (-(b.mag : Int)).toNat = 0 := by omega
      rw [h0]; simpa using this

/-- `mp_mod`'s result has the sign of `b`: `0 ≤ c < b` for `b > 0`, `b < c ≤ 0` for `b < 0`. -/
theorem fmod_bounds (x y : Int) :
    (0 < y → 0 ≤ x.fmod y ∧ x.fmod y < y) ∧ (y < 0 → y < x.fmod y ∧ x.fmod y ≤ 0) := by
  refine ⟨fun hy => ⟨Int.fmod_nonneg_of_pos _ hy, Int.fmod_lt_of_pos _ hy⟩, fun hy => ?_⟩
  have h1 := Int.fmod_nonneg_of_pos (-x) (Int.neg_pos.2 hy)
  have h2 := Int.fmod_lt_of_pos (-x) (Int.neg_pos.2 hy)
  rw [Int.neg_fmod_neg] at h1 h2
  omega

end Tom
