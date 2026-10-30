import Tom.Spec.Signed

/-!
# `mp_zero`, `mp_set`, `mp_copy`, `mp_abs`: stores of a whole `mp_int`

What each C function leaves (`vendor/libtommath/bn_mp_{zero,set,copy,abs}.c`),
as a named-field structure over the `MpInt` before and after, and its meaning
(`….spec`): the result is valid and has the expected magnitude and value.

* `mp_zero(a)`: `sign := MP_ZPOS`, `used := 0`, all `alloc` digits zeroed.
* `mp_set(a, b)`: `dp[0] := b & MP_MASK`, `sign := MP_ZPOS`,
  `used := (dp[0] != 0)`, the digits from `used` to `alloc` zeroed.
* `mp_copy(a, b)` (`a->used ≤ b->alloc`, so no `mp_grow`, D5): `a`'s used
  digits copied, `b`'s digits from `a->used` to the old `b->used` zeroed, the
  rest of `b`'s array untouched; `used` and `sign` from `a`.
* `mp_abs(a, b)`: `mp_copy(a, b)`, then `sign := MP_ZPOS`.

`MpInt.ofDigits u al s f` is the `mp_int` with those fields and the digit
function `f` on `[0, al)`, the form the machine proofs build their results in.
-/

namespace Tom

open MpInt

/-- The `mp_int` with `used = u`, `alloc = al`, `sign = s` and digits `f` on `[0, al)`. -/
def MpInt.ofDigits (u al s : Nat) (f : Nat → Nat) : MpInt :=
  { used := u, alloc := al, sign := s, digits := (List.range al).map f }

theorem MpInt.ofDigits_digit (u al s : Nat) (f : Nat → Nat) (i : Nat) :
    (MpInt.ofDigits u al s f).digit i = if i < al then f i else 0 := by
  simp only [MpInt.ofDigits, MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < al <;> simp [h]

theorem MpInt.ofDigits_len (u al s : Nat) (f : Nat → Nat) : (MpInt.ofDigits u al s f).digits.length = al := by
  simp [MpInt.ofDigits]

/-! ## `mp_zero` -/

/-- What `mp_zero(a)` leaves. -/
structure ZeroPost (a a' : MpInt) : Prop where
  used : a'.used = 0
  alloc : a'.alloc = a.alloc
  sign : a'.sign = Layout.mpZpos
  len : a'.digits.length = a.alloc
  digit : ∀ i, a'.digit i = 0

/-- `a` zeroed. -/
def MpInt.zeroed (a : MpInt) : MpInt := MpInt.ofDigits 0 a.alloc Layout.mpZpos fun _ => 0

theorem ZeroPost.zeroed (a : MpInt) : ZeroPost a a.zeroed :=
  { used := rfl, alloc := rfl, sign := rfl, len := MpInt.ofDigits_len _ _ _ _
    digit := fun i => by simp [MpInt.zeroed, MpInt.ofDigits_digit] }

/-- `mp_zero` leaves a valid zero. -/
theorem ZeroPost.spec {a a' : MpInt} (ha : a.Shape) (h : ZeroPost a a') :
    a'.Valid ∧ a'.mag = 0 ∧ a'.val = 0 := by
  have hm : a'.mag = 0 := MpInt.mag_used_zero h.used
  refine ⟨{ len := by rw [h.len, h.alloc], used_le := by rw [h.used]; exact Nat.zero_le _
            alloc_lt := by rw [h.alloc]; exact ha.alloc_lt
            digit_lt := fun i => by rw [h.digit]; exact radix_pos
            high_zero := fun i _ => h.digit i
            top := fun hu => by rw [h.used] at hu; exact absurd hu (Nat.lt_irrefl 0)
            sign_ok := Or.inl h.sign, zero_pos := fun _ => h.sign }, hm, ?_⟩
  simp [MpInt.val, h.sign, hm, Layout.mpZpos, Layout.mpNeg]

/-! ## `mp_set` -/

/-- What `mp_set(a, b)` leaves, `d = b & MP_MASK` (`a->alloc ≥ 1`). -/
structure SetPost (a : MpInt) (d : Nat) (a' : MpInt) : Prop where
  used : a'.used = if d = 0 then 0 else 1
  alloc : a'.alloc = a.alloc
  sign : a'.sign = Layout.mpZpos
  len : a'.digits.length = a.alloc
  digit : ∀ i, a'.digit i = if i = 0 then d else 0

/-- `a` set to the digit `d`. -/
def MpInt.setTo (a : MpInt) (d : Nat) : MpInt :=
  MpInt.ofDigits (if d = 0 then 0 else 1) a.alloc Layout.mpZpos fun i => if i = 0 then d else 0

theorem SetPost.setTo {a : MpInt} (d : Nat) (hal : 0 < a.alloc) : SetPost a d (a.setTo d) :=
  { used := rfl, alloc := rfl, sign := rfl, len := MpInt.ofDigits_len _ _ _ _
    digit := fun i => by
      simp only [MpInt.setTo, MpInt.ofDigits_digit]
      by_cases hi : i < a.alloc
      · simp [hi]
      · simp [hi, show i ≠ 0 by omega] }

/-- `mp_set(a, b)` leaves a valid `mp_int` of value `b & MP_MASK`. -/
theorem SetPost.spec {a a' : MpInt} {d : Nat} (ha : a.Shape) (hal : 0 < a.alloc) (hd : d < radix)
    (h : SetPost a d a') : a'.Valid ∧ a'.mag = d ∧ a'.val = d := by
  have hm : a'.mag = d := by
    unfold MpInt.mag; rw [h.used]
    by_cases h0 : d = 0
    · simp [h0, natUpTo]
    · simp [h0, natUpTo, h.digit]
  refine ⟨{ len := by rw [h.len, h.alloc]
            used_le := by rw [h.used, h.alloc]; split <;> omega
            alloc_lt := by rw [h.alloc]; exact ha.alloc_lt
            digit_lt := fun i => by rw [h.digit]; split; exact hd; exact radix_pos
            high_zero := fun i hi => by
              rw [h.digit]; rw [h.used] at hi
              split
              · rename_i hi0; subst hi0; split at hi; assumption; omega
              · rfl
            top := fun hu => by
              rw [h.used] at hu ⊢; split at hu
              · omega
              · rename_i h0; simp [h.digit, h0]
            sign_ok := Or.inl h.sign, zero_pos := fun _ => h.sign }, hm, ?_⟩
  simp [MpInt.val, h.sign, hm, Layout.mpZpos, Layout.mpNeg]

/-! ## `mp_copy` -/

/-- What `mp_copy(a, b)` leaves in `b` (distinct operands, `a->used ≤ b->alloc`). -/
structure CopyPost (a b b' : MpInt) : Prop where
  alloc : b'.alloc = b.alloc
  len : b'.digits.length = b.alloc
  used : b'.used = a.used
  sign : b'.sign = a.sign
  digit : ∀ i, b'.digit i = if i < a.used then a.digit i else if i < b.used then 0 else b.digit i

/-- The digits `mp_copy(a, b)` leaves. -/
def copyDigits (a b : MpInt) (i : Nat) : Nat := if i < a.used then a.digit i else if i < b.used then 0 else b.digit i

/-- `a` copied into `b`. -/
def MpInt.copyInto (a b : MpInt) : MpInt := MpInt.ofDigits a.used b.alloc a.sign (copyDigits a b)

theorem CopyPost.copyInto {a b : MpInt} (hb : b.Shape) (hroom : a.used ≤ b.alloc) :
    CopyPost a b (a.copyInto b) :=
  { alloc := rfl, len := MpInt.ofDigits_len _ _ _ _, used := rfl, sign := rfl
    digit := fun i => by
      simp only [MpInt.copyInto, MpInt.ofDigits_digit]
      have := hb.used_le
      by_cases hi : i < b.alloc
      · simp [hi, copyDigits]
      · simp [hi, show ¬ i < a.used by omega, show ¬ i < b.used by omega, hb.high_zero i (by omega)] }

/-- The digit facts of a copy: valid, the same magnitude. -/
theorem CopyPost.valid {a b b' : MpInt} (ha : a.Valid) (hb : b.Shape) (hroom : a.used ≤ b.alloc)
    (h : CopyPost a b b') : b'.Valid ∧ b'.mag = a.mag := by
  have hlo : ∀ i, i < a.used → b'.digit i = a.digit i := fun i hi => by simp [h.digit, hi]
  have hhi : ∀ i, a.used ≤ i → b'.digit i = 0 := fun i hi => by
    simp only [h.digit, show ¬ i < a.used by omega, ↓reduceIte]; split; rfl; exact hb.high_zero i (by omega)
  refine ⟨{ len := by rw [h.len, h.alloc], used_le := by rw [h.used, h.alloc]; exact hroom
            alloc_lt := by rw [h.alloc]; exact hb.alloc_lt
            digit_lt := fun i => by
              by_cases hi : i < a.used
              · rw [hlo i hi]; exact ha.digit_lt i
              · rw [hhi i (by omega)]; exact radix_pos
            high_zero := fun i hi => hhi i (by rw [h.used] at hi; exact hi)
            top := fun hu => by
              rw [h.used] at hu ⊢; rw [hlo _ (by omega)]; exact ha.top hu
            sign_ok := by rw [h.sign]; exact ha.sign_ok
            zero_pos := fun hu => by rw [h.sign]; exact ha.zero_pos (by rw [← h.used]; exact hu) }, ?_⟩
  unfold MpInt.mag; rw [h.used]; exact natUpTo_congr _ hlo

/-- `mp_copy(a, b)` leaves `b` valid with `a`'s value. -/
theorem CopyPost.spec {a b b' : MpInt} (ha : a.Valid) (hb : b.Shape) (hroom : a.used ≤ b.alloc)
    (h : CopyPost a b b') : b'.Valid ∧ b'.mag = a.mag ∧ b'.val = a.val := by
  have ⟨hv, hm⟩ := h.valid ha hb hroom
  exact ⟨hv, hm, by simp only [MpInt.val, h.sign, hm]⟩

/-! ## `mp_abs` -/

/-- What `mp_abs(a, b)` leaves in `b`: `a` copied, `sign := MP_ZPOS`. -/
structure AbsPost (a b b' : MpInt) : Prop where
  alloc : b'.alloc = b.alloc
  len : b'.digits.length = b.alloc
  used : b'.used = a.used
  sign : b'.sign = Layout.mpZpos
  digit : ∀ i, b'.digit i = if i < a.used then a.digit i else if i < b.used then 0 else b.digit i

theorem AbsPost.of_copy {a b c : MpInt} (h : CopyPost a b c) : AbsPost a b (c.withSign Layout.mpZpos) :=
  { alloc := h.alloc, len := h.len, used := h.used, sign := rfl, digit := h.digit }

/-- `mp_abs(a, b)` leaves `b` valid with value `|a|`. -/
theorem AbsPost.spec {a b b' : MpInt} (ha : a.Valid) (hb : b.Shape) (hroom : a.used ≤ b.alloc)
    (h : AbsPost a b b') : b'.Valid ∧ b'.mag = a.mag ∧ b'.val = a.mag := by
  have hc : CopyPost a b (b'.withSign a.sign) :=
    { alloc := h.alloc, len := h.len, used := h.used, sign := rfl, digit := h.digit }
  have ⟨hv, hm⟩ := hc.valid ha hb hroom
  have hm' : b'.mag = a.mag := hm
  refine ⟨{ hv.toShape with
            top := hv.top, sign_ok := Or.inl h.sign, zero_pos := fun _ => h.sign }, hm', ?_⟩
  simp [MpInt.val, h.sign, hm', Layout.mpZpos, Layout.mpNeg]

end Tom
