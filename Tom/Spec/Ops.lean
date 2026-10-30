import Tom.Spec.Algo

/-!
# Function contracts

For each libtommath function, the state it leaves, as a named-field
structure over the abstract `MpInt`s before and after the call (the digit
model of `Tom.Spec.Algo`), and the theorem that this state meets the
arithmetic specification. The machine proofs (`Tom.Machine`) establish the
structures; the theorems here turn them into statements about `Nat`/`Int`.

Aliasing (`mp_add(a, a, a)`, allowed by libtommath) is not covered yet: the
machine contracts take disjoint operands.
-/

namespace Tom

open MpInt

/-! ## `mp_clamp` -/

/-- What `mp_clamp(a)` leaves: the digits and `alloc` unchanged, `used`
lowered past the zero top digits, the sign reset when the result is zero. -/
structure ClampPost (a a' : MpInt) : Prop where
  digits : a'.digits = a.digits
  alloc : a'.alloc = a.alloc
  used : a'.used = clampUsed a.digit a.used
  sign : a'.sign = if a'.used = 0 then Layout.mpZpos else a.sign

theorem ClampPost.digit {a a' : MpInt} (h : ClampPost a a') : a'.digit = a.digit := by
  funext i; simp [MpInt.digit, h.digits]

/-- `mp_clamp` keeps the magnitude and makes a shaped `mp_int` valid. -/
theorem ClampPost.spec {a a' : MpInt} (hs : a.Shape)
    (hsign : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg) (h : ClampPost a a') :
    a'.Valid ∧ a'.mag = a.mag := by
  have hd := h.digit
  have hle := clampUsed_le a.digit a.used
  refine ⟨{ len := ?_, used_le := ?_, alloc_lt := ?_, digit_lt := ?_, high_zero := ?_,
            top := ?_, sign_ok := ?_, zero_pos := ?_ }, ?_⟩
  · rw [h.digits, h.alloc]; exact hs.len
  · rw [h.used, h.alloc]; exact Nat.le_trans hle hs.used_le
  · rw [h.alloc]; exact hs.alloc_lt
  · rw [hd]; exact hs.digit_lt
  · intro i hi
    rw [hd]
    by_cases hlt : i < a.used
    · exact clampUsed_zero a.digit a.used i (h.used ▸ hi) hlt
    · exact hs.high_zero i (by omega)
  · intro hu; rw [hd, h.used]; exact clampUsed_top a.digit a.used (h.used ▸ hu)
  · rw [h.sign]; split
    · exact Or.inl rfl
    · exact hsign
  · intro hu; rw [h.sign, ite_eq_left_iff.2 (fun h => absurd hu h)]
  · unfold MpInt.mag; rw [hd, h.used]; exact natUpTo_clampUsed a.digit a.used

/-! ## `s_mp_add` -/

/-- The digits `s_mp_add(a, b, c)` writes: the carry chain of the used
digits, as a digit function (zero past `max(used) + 1`). -/
def addDigits (a b : MpInt) (i : Nat) : Nat :=
  (addCarry (a.digits.take a.used) (b.digits.take b.used) 0).getD i 0

/-- What `s_mp_add(a, b, c)` leaves in `c` when `c` has room
(`c->alloc ≥ max + 1`, so `mp_grow` is not called): the carry chain's
digits, zeros above, `used` clamped from `max + 1`, the sign reset if the
sum is zero; `alloc` unchanged. -/
structure SAddPost (a b c c' : MpInt) : Prop where
  alloc : c'.alloc = c.alloc
  len : c'.digits.length = c.alloc
  digit : c'.digit = addDigits a b
  used : c'.used = clampUsed (addDigits a b) (max a.used b.used + 1)
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else c.sign

theorem addDigits_lt {a b : MpInt} (ha : a.Shape) (hb : b.Shape) (i : Nat) :
    addDigits a b i < radix := by
  unfold addDigits
  have hx : ∀ d ∈ a.digits.take a.used, d < radix := fun d hd => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
    have := ha.digit_lt j
    simp only [MpInt.digit, List.getElem_take] at this ⊢
    simpa [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show j < a.digits.length by simp at hj; omega)] using this
  have hy : ∀ d ∈ b.digits.take b.used, d < radix := fun d hd => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
    have := hb.digit_lt j
    simp only [MpInt.digit, List.getElem_take] at this ⊢
    simpa [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show j < b.digits.length by simp at hj; omega)] using this
  rw [List.getD_eq_getElem?_getD]
  cases hg : (addCarry _ _ 0)[i]? with
  | none => exact radix_pos
  | some d => exact addCarry_lt _ _ 0 hx hy (by decide) d (List.mem_of_getElem? hg)

theorem addDigits_high {a b : MpInt} (ha : a.Shape) (hb : b.Shape) (i : Nat)
    (hi : max a.used b.used + 1 ≤ i) : addDigits a b i = 0 := by
  unfold addDigits
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [length_addCarry, List.length_take, List.length_take, ha.len, hb.len,
      Nat.min_eq_left ha.used_le, Nat.min_eq_left hb.used_le]
    exact hi

theorem MpInt.mag_eq_natOf {a : MpInt} : a.mag = natOf (a.digits.take a.used) := by
  unfold MpInt.mag; rw [natOf_take]
  apply natUpTo_congr; intro i hi
  simp [MpInt.digit, List.getD_eq_getElem?_getD]

theorem natUpTo_addDigits {a b : MpInt} (ha : a.Shape) (hb : b.Shape) :
    natUpTo (addDigits a b) (max a.used b.used + 1) = a.mag + b.mag := by
  rw [MpInt.mag_eq_natOf, MpInt.mag_eq_natOf]
  have key := natOf_addCarry (a.digits.take a.used) (b.digits.take b.used) 0
  rw [Nat.add_zero] at key
  rw [← key]
  have hlen := length_addCarry (a.digits.take a.used) (b.digits.take b.used) 0
  rw [List.length_take, List.length_take, ha.len, hb.len, Nat.min_eq_left ha.used_le,
    Nat.min_eq_left hb.used_le] at hlen
  rw [← List.take_of_length_le (Nat.le_of_eq hlen), natOf_take]
  rfl

/-- `s_mp_add` computes `|c| = |a| + |b|` and leaves `c` valid. -/
theorem SAddPost.spec {a b c c' : MpInt} (ha : a.Shape) (hb : b.Shape)
    (hroom : max a.used b.used + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31)
    (hsign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg) (h : SAddPost a b c c') :
    c'.Valid ∧ c'.mag = a.mag + b.mag := by
  have hle := clampUsed_le (addDigits a b) (max a.used b.used + 1)
  refine ⟨{ len := ?_, used_le := ?_, alloc_lt := ?_, digit_lt := ?_, high_zero := ?_,
            top := ?_, sign_ok := ?_, zero_pos := ?_ }, ?_⟩
  · rw [h.len, h.alloc]
  · rw [h.used, h.alloc]; omega
  · rw [h.alloc]; exact hc
  · rw [h.digit]; exact addDigits_lt ha hb
  · intro i hi
    rw [h.digit]
    by_cases hlt : i < max a.used b.used + 1
    · exact clampUsed_zero _ _ i (h.used ▸ hi) hlt
    · exact addDigits_high ha hb i (by omega)
  · intro hu; rw [h.digit, h.used]; exact clampUsed_top _ _ (h.used ▸ hu)
  · rw [h.sign]; split
    · exact Or.inl rfl
    · exact hsign
  · intro hu; rw [h.sign, ite_eq_left_iff.2 (fun h => absurd hu h)]
  · unfold MpInt.mag; rw [h.digit, h.used, natUpTo_clampUsed]; exact natUpTo_addDigits ha hb

/-! ## `mp_cmp_mag` -/

/-- `mp_cmp_mag(a, b)` returns the `mp_ord` code of `cmpMag a b` and changes
nothing. -/
theorem cmpMag_spec {a b : MpInt} (ha : a.Valid) (hb : b.Valid) :
    ordCode (cmpMag a b) = ordCode (compare a.mag b.mag) := by
  rw [cmpMag_eq ha hb]

end Tom
