import Tom.Spec.Indexed
import Tom.Spec.Signed

/-!
# `mp_mul_2` and `mp_div_2`: shifts by one bit

`mp_mul_2(a, b)` (`vendor/libtommath/bn_mp_mul_2.c`) sets `b->used =
a->used` and, for `x < a->used`, `b[x] = ((a[x] << 1) | r) & MP_MASK` with
`r` the bit shifted out of `a[x - 1]` (`a[x - 1] >> (MP_DIGIT_BIT - 1)`,
`0` for `x = 0`); a last carry `r ≠ 0` becomes the digit `b[a->used] = 1`
and `++b->used`. It then zeroes `b[b->used .. oldused)` and copies the sign.
It does not clamp. The carry chain is `s_mp_add`'s for `a + a`
(`addCarryAt a a`: the carry into `x + 1` is the top bit of `a[x]`,
`addCarryAt_self_succ`), so the digits are `addDigits a a` and `b->used` is
`a->used` plus the final carry.

`mp_div_2(a, b)` (`bn_mp_div_2.c`) sets `b->used = a->used` and, from the
top down, `b[x] = (a[x] >> 1) | (r << (MP_DIGIT_BIT - 1))` with `r` the low
bit of `a[x + 1]` (`0` at the top), zeroes `b[a->used .. oldused)`, copies
the sign and clamps: `div2Digits`, then `mp_clamp` (`Div2Post`, the fields of
`ClampPost` of `div2Mid`).
-/

namespace Tom

open MpInt

/-! ## `mp_mul_2` -/

/-- The carry into `x + 1` of `a + a` is the top bit of `a[x]`, the C's
`rr = *tmpa >> (MP_DIGIT_BIT - 1)`. -/
theorem addCarryAt_self_succ {a : MpInt} (ha : a.Shape) (i : Nat) :
    addCarryAt a a (i + 1) = a.digit i / 2 ^ 27 := by
  rw [addCarryAt_succ]
  have h1 := addCarryAt_le_one ha ha i
  have h2 := ha.digit_lt i
  rw [radix_eq] at h2 ⊢
  omega

/-- The C's digit `((a[x] << 1) | r) & MP_MASK` with `r ≤ 1`: the digit of
`a + a` with carry `r`. -/
theorem mul2Digit_c (x r : Nat) (hr : r ≤ 1) :
    (2 * x + r) % radix = (x + x + r) % radix := by
  rw [show 2 * x = x + x by omega]

/-- The digits of `a + a` by index (`addDigits` with `max(used) = a->used`). -/
theorem addDigits_self_lt {a : MpInt} (ha : a.Shape) {i : Nat} (hi : i < a.used) :
    addDigits a a i = (a.digit i + a.digit i + addCarryAt a a i) % radix :=
  addDigits_lt_max ha ha (by rw [Nat.max_self]; exact hi)

theorem addDigits_self_used {a : MpInt} (ha : a.Shape) : addDigits a a a.used = addCarryAt a a a.used := by
  have h := addDigits_max ha ha
  rwa [Nat.max_self] at h

/-- From `a->used` plus the final carry on, the digits of `a + a` are zero. -/
theorem addDigits_self_high {a : MpInt} (ha : a.Shape) (i : Nat) (hi : a.used + addCarryAt a a a.used ≤ i) :
    addDigits a a i = 0 := by
  rcases Nat.lt_or_eq_of_le (show a.used ≤ i by omega) with hlt | heq
  · exact addDigits_gt ha ha (by rw [Nat.max_self]; exact hlt)
  · subst heq; rw [addDigits_self_used ha]; omega

/-- What `mp_mul_2(a, b)` leaves in `b` when `b` has room
(`b->alloc ≥ a->used + 1`, so `mp_grow` is not called): the digits of
`a + a`, `used` the operand's plus the final carry, `a`'s sign. -/
structure Mul2Post (a b b' : MpInt) : Prop where
  alloc : b'.alloc = b.alloc
  len : b'.digits.length = b.alloc
  digit : b'.digit = addDigits a a
  used : b'.used = a.used + addCarryAt a a a.used
  sign : b'.sign = a.sign

/-- `mp_mul_2` computes `b = 2 a` and leaves `b` valid. -/
theorem Mul2Post.spec {a b b' : MpInt} (ha : a.Valid) (hroom : a.used + 1 ≤ b.alloc)
    (hb : b.alloc < 2 ^ 31) (h : Mul2Post a b b') :
    b'.Valid ∧ b'.mag = 2 * a.mag ∧ b'.val = 2 * a.val := by
  have hs := ha.toShape
  have hc := addCarryAt_le_one hs hs a.used
  have hmx : max a.used a.used = a.used := Nat.max_self _
  have hmax := addDigits_max hs hs
  rw [hmx] at hmax
  -- the digit at `a->used` is the final carry, and digits above it are zero
  have hz : ∀ i, b'.used ≤ i → addDigits a a i = 0 := fun i hi =>
    addDigits_self_high hs i (by rw [h.used] at hi; exact hi)
  have hmag : b'.mag = 2 * a.mag := by
    unfold MpInt.mag
    rw [h.digit, ← natUpTo_zeros (addDigits a a) b'.used (a.used + 1) (by rw [h.used]; omega)
      (fun i h1 _ => hz i h1)]
    have := natUpTo_addDigits hs hs
    rw [hmx] at this; rw [this]; unfold MpInt.mag; omega
  refine ⟨{ len := ?_, used_le := ?_, alloc_lt := ?_, digit_lt := ?_, high_zero := ?_,
            top := ?_, sign_ok := ?_, zero_pos := ?_ }, hmag, ?_⟩
  · rw [h.len, h.alloc]
  · rw [h.used, h.alloc]; omega
  · rw [h.alloc]; exact hb
  · rw [h.digit]; exact addDigits_lt hs hs
  · intro i hi; rw [h.digit]; exact hz i hi
  · intro hu
    rw [h.digit]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc with h0 | h1
    · -- no carry out: the top digit is `2 a[used - 1] + r < radix`, nonzero
      have hu' : b'.used = a.used := by rw [h.used, h0, Nat.add_zero]
      rw [hu'] at hu ⊢
      have ht := ha.top hu
      have hlt : a.used - 1 < max a.used a.used := by rw [hmx]; omega
      rw [addDigits_lt_max hs hs hlt]
      have hsucc := addCarryAt_succ a a (a.used - 1)
      rw [Nat.sub_add_cancel (by omega), h0] at hsucc
      have hd := ha.digit_lt (a.used - 1)
      rw [radix_eq] at hsucc hd ⊢
      omega
    · have hu' : b'.used - 1 = a.used := by rw [h.used, h1]; omega
      rw [hu', hmax, h1]; omega
  · rw [h.sign]; exact ha.sign_ok
  · intro hu; rw [h.sign]; exact ha.zero_pos (by rw [h.used] at hu; omega)
  · rw [MpInt.val_eq, MpInt.val_eq, hmag, h.sign]
    split <;> omega

/-! ## `mp_div_2` -/

/-- The C's digit `x` of `mp_div_2`: `a[x] >> 1` with the low bit of
`a[x + 1]` as its top bit (`r << (MP_DIGIT_BIT - 1)`). -/
def div2Digits (a : MpInt) (i : Nat) : Nat := a.digit i / 2 + 2 ^ 27 * (a.digit (i + 1) % 2)

/-- `b` as `mp_div_2` hands it to `mp_clamp`: `used = a->used`, `a`'s sign,
the shifted digits. -/
def div2Mid (a b : MpInt) : MpInt :=
  { used := a.used, alloc := b.alloc, sign := a.sign, digits := (List.range b.alloc).map (div2Digits a) }

/-- What `mp_div_2(a, b)` leaves in `b` when `b` has room
(`b->alloc ≥ a->used`, so `mp_grow` is not called): the shifted digits,
`used` clamped from `a->used`, `a`'s sign reset if the result is zero. -/
structure Div2Post (a b b' : MpInt) : Prop where
  alloc : b'.alloc = b.alloc
  len : b'.digits.length = b.alloc
  digit : b'.digit = div2Digits a
  used : b'.used = clampUsed (div2Digits a) a.used
  sign : b'.sign = if b'.used = 0 then Layout.mpZpos else a.sign

theorem div2Digits_lt {a : MpInt} (ha : a.Shape) (i : Nat) : div2Digits a i < radix := by
  unfold div2Digits
  have := ha.digit_lt i
  rw [radix_eq] at *
  omega

theorem div2Digits_high {a : MpInt} (ha : a.Shape) (i : Nat) (hi : a.used ≤ i) : div2Digits a i = 0 := by
  unfold div2Digits
  rw [ha.high_zero i hi, ha.high_zero (i + 1) (by omega)]

theorem div2Mid_digit {a b : MpInt} (ha : a.Shape) (hroom : a.used ≤ b.alloc) :
    (div2Mid a b).digit = div2Digits a := by
  funext i
  unfold MpInt.digit div2Mid
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < b.alloc
  · rw [List.getElem?_range h, Option.map_some, Option.getD_some]
  · rw [List.getElem?_eq_none (by rw [List.length_range]; omega), Option.map_none, Option.getD_none,
      div2Digits_high ha i (by omega)]

/-- `2 Σ_{i<n} d'_i R^i + a[0] mod 2 = Σ_{i<n} a[i] R^i + (a[n] mod 2) R^n`. -/
theorem natUpTo_div2 (a : MpInt) : ∀ n,
    2 * natUpTo (div2Digits a) n + a.digit 0 % 2 = natUpTo a.digit n + a.digit n % 2 * radix ^ n
  | 0 => by simp [natUpTo]
  | n + 1 => by
    have ih := natUpTo_div2 a n
    simp only [natUpTo]
    rw [div2Digits]; simp only [Nat.reducePow]
    have hR : radix ^ (n + 1) = radix ^ n * 268435456 := by rw [Nat.pow_succ, radix_eq]
    rw [hR]
    generalize radix ^ n = P at ih ⊢
    generalize natUpTo (div2Digits a) n = D at ih ⊢
    generalize natUpTo a.digit n = A at ih ⊢
    generalize a.digit n = x at ih ⊢
    generalize a.digit (n + 1) % 2 = t
    have f1 : P * x = P * (x % 2) + 2 * (P * (x / 2)) := by
      conv => lhs; rw [← Nat.mod_add_div x 2]
      rw [Nat.mul_add, Nat.mul_left_comm]
    have f2 : P * (x / 2 + 134217728 * t) = P * (x / 2) + 134217728 * (P * t) := by
      rw [Nat.mul_add, Nat.mul_left_comm]
    have f3 : t * (P * 268435456) = 268435456 * (P * t) := by
      rw [Nat.mul_left_comm, Nat.mul_comm t, Nat.mul_left_comm]
    have f4 : x % 2 * P = P * (x % 2) := Nat.mul_comm _ _
    rw [f2, f3]
    omega

theorem natUpTo_div2Digits {a : MpInt} (ha : a.Shape) : natUpTo (div2Digits a) a.used = a.mag / 2 := by
  have h := natUpTo_div2 a a.used
  rw [ha.high_zero a.used (Nat.le_refl _)] at h
  unfold MpInt.mag
  omega

/-- `mp_div_2` computes `b = a / 2` (the magnitude halved, rounding toward
zero) and leaves `b` valid. -/
theorem Div2Post.spec {a b b' : MpInt} (ha : a.Valid) (hroom : a.used ≤ b.alloc)
    (hb : b.alloc < 2 ^ 31) (h : Div2Post a b b') :
    b'.Valid ∧ b'.mag = a.mag / 2 ∧ b'.val = a.val.tdiv 2 := by
  have hs := ha.toShape
  have hle := clampUsed_le (div2Digits a) a.used
  have hmag : b'.mag = a.mag / 2 := by
    unfold MpInt.mag; rw [h.digit, h.used, natUpTo_clampUsed]; exact natUpTo_div2Digits hs
  refine ⟨{ len := ?_, used_le := ?_, alloc_lt := ?_, digit_lt := ?_, high_zero := ?_,
            top := ?_, sign_ok := ?_, zero_pos := ?_ }, hmag, ?_⟩
  · rw [h.len, h.alloc]
  · rw [h.used, h.alloc]; omega
  · rw [h.alloc]; exact hb
  · rw [h.digit]; exact div2Digits_lt hs
  · intro i hi
    rw [h.digit]
    by_cases hlt : i < a.used
    · exact clampUsed_zero _ _ i (h.used ▸ hi) hlt
    · exact div2Digits_high hs i (by omega)
  · intro hu; rw [h.digit, h.used]; exact clampUsed_top _ _ (h.used ▸ hu)
  · rw [h.sign]; split
    · exact Or.inl rfl
    · exact ha.sign_ok
  · intro hu; rw [h.sign, ite_eq_left_iff.2 (fun h => absurd hu h)]
  · rw [MpInt.val_of_sign h.sign, hmag, MpInt.val_eq]
    split
    · rw [Int.neg_tdiv, Int.ofNat_tdiv]; rfl
    · rw [Int.ofNat_tdiv]; rfl

end Tom
