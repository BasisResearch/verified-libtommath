import Tom.Spec.Ops

/-!
# `s_mp_sub`: digit differences with borrow

`s_mp_sub(a, b, c)` (`vendor/libtommath/bn_s_mp_sub.c`) assumes
`|a| ≥ |b|` (its comment says `>`, but equality works too). With
`min = b->used` and `max = a->used`, it grows `c` to `max` digits if
needed, sets `c->used = max`, and then

* for `i < min`: `t = (a[i] - b[i]) - u` in `uint32_t` arithmetic,
  `u = t >> 31` (`MP_SIZEOF_BITS(mp_digit) - 1`), `c[i] = t & MP_MASK`;
* for `min ≤ i < max`: the same with `b[i]` replaced by nothing
  (`t = a[i] - u`);
* zeroes `c[max .. olduse)` (`MP_ZERO_DIGITS`, a no-op when
  `olduse ≤ max`) and calls `mp_clamp(c)`.

There is no final borrow digit: when `|a| ≥ |b|` the last borrow is zero.

`subBorrow` is the digit loop on lists, with the `uint32_t` wrap-around
replaced by `(x + radix - y - u) % radix` and the borrow by
`if x < y + u then 1 else 0`; `subDigit_c`/`subBorrow_c` show that the C's
formulas compute exactly these (stated on `Nat` modulo `2^32`, for the
machine and C proofs). `addDigit_c`/`addCarry_c` are the same for
`s_mp_add`'s digit (`(x + y + u) & MP_MASK`, `>> MP_DIGIT_BIT`).
-/

namespace Tom

open MpInt

/-! ## The C's `mp_digit` formulas -/

theorem radix_eq : radix = 268435456 := by
  simp only [radix, Layout.digitBits, Nat.reducePow]

theorem mpMask_eq : Layout.mpMask = radix - 1 := by
  simp only [radix_eq, Layout.mpMask]

/-- `n & MP_MASK` is `n % radix`. -/
theorem and_mpMask (n : Nat) : n &&& Layout.mpMask = n % radix := by
  rw [mpMask_eq, radix, Nat.and_two_pow_sub_one_eq_mod]

/-- `n >> MP_DIGIT_BIT` is `n / radix`. -/
theorem shiftRight_digitBits (n : Nat) : n >>> Layout.digitBits = n / radix := by
  rw [Nat.shiftRight_eq_div_pow]

/-- `s_mp_add`'s digit: `T = A + B + U` in `uint32_t` (no wrap: the sum is
below `2^29`), then `T & MP_MASK` is the model's digit. -/
theorem addDigit_c (x y u : Nat) (hx : x < radix) (hy : y < radix) (hu : u ≤ 1) :
    ((x + y + u) % 2 ^ 32) &&& Layout.mpMask = (x + y + u) % radix := by
  have : x + y + u < 2 ^ 32 := by rw [radix_eq] at hx hy; omega
  rw [and_mpMask, Nat.mod_eq_of_lt this]

/-- `s_mp_add`'s carry: `T >> MP_DIGIT_BIT` is the model's carry. -/
theorem addCarry_c (x y u : Nat) (hx : x < radix) (hy : y < radix) (hu : u ≤ 1) :
    ((x + y + u) % 2 ^ 32) >>> Layout.digitBits = (x + y + u) / radix := by
  have : x + y + u < 2 ^ 32 := by rw [radix_eq] at hx hy; omega
  rw [shiftRight_digitBits, Nat.mod_eq_of_lt this]

/-- `uint32_t` subtraction in two steps, `(A - B) - U`, is one subtraction
of `B + U`. -/
theorem sub_wrap_two_step (x y u : Nat) (hyu : y + u ≤ 2 ^ 32) :
    ((x + 2 ^ 32 - y) % 2 ^ 32 + 2 ^ 32 - u) % 2 ^ 32 = (x + 2 ^ 32 - (y + u)) % 2 ^ 32 := by
  simp only [Nat.reducePow] at hyu ⊢
  omega

/-- `s_mp_sub`'s digit: `T = A - B - U` in `uint32_t`, then `T & MP_MASK`
is the model's digit. -/
theorem subDigit_c (x y u : Nat) (hx : x < radix) (hy : y < radix) (hu : u ≤ 1) :
    ((x + 2 ^ 32 - (y + u)) % 2 ^ 32) &&& Layout.mpMask = (x + radix - y - u) % radix := by
  rw [and_mpMask, radix_eq] at *
  simp only [Nat.reducePow]
  omega

/-- `s_mp_sub`'s borrow: `T >> 31` is the model's borrow. -/
theorem subBorrow_c (x y u : Nat) (hx : x < radix) (hy : y < radix) (hu : u ≤ 1) :
    ((x + 2 ^ 32 - (y + u)) % 2 ^ 32) >>> 31 = if x < y + u then 1 else 0 := by
  rw [radix_eq] at hx hy
  rw [Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow]
  split <;> omega

/-- The second loop of `s_mp_sub` (`T = A - U`): its digit. -/
theorem subDigit_c_hi (x u : Nat) (hx : x < radix) (hu : u ≤ 1) :
    ((x + 2 ^ 32 - u) % 2 ^ 32) &&& Layout.mpMask = (x + radix - u) % radix := by
  have := subDigit_c x 0 u hx radix_pos hu
  simpa using this

/-- The second loop of `s_mp_sub` (`T = A - U`): its borrow. -/
theorem subBorrow_c_hi (x u : Nat) (hx : x < radix) (hu : u ≤ 1) :
    ((x + 2 ^ 32 - u) % 2 ^ 32) >>> 31 = if x < u then 1 else 0 := by
  have := subBorrow_c x 0 u hx radix_pos hu
  simpa using this

/-! ## `subBorrow` -/

/-- The digit loops of `s_mp_sub` on the used digits of `a` and `b`: one
output digit per digit of `a`, `b`'s digits read as `0` past its end (the
second loop). No final borrow digit. -/
def subBorrow : List Nat → List Nat → Nat → List Nat
  | [], _, _ => []
  | x :: xs, ys, u =>
    (x + radix - ys.headD 0 - u) % radix :: subBorrow xs ys.tail (if x < ys.headD 0 + u then 1 else 0)

/-- The first loop of `s_mp_sub` (`i < min`). -/
@[simp] theorem subBorrow_cons_cons (x y : Nat) (xs ys : List Nat) (u : Nat) :
    subBorrow (x :: xs) (y :: ys) u =
      (x + radix - y - u) % radix :: subBorrow xs ys (if x < y + u then 1 else 0) := rfl

/-- The second loop of `s_mp_sub` (`min ≤ i < max`). -/
@[simp] theorem subBorrow_cons_nil (x : Nat) (xs : List Nat) (u : Nat) :
    subBorrow (x :: xs) [] u = (x + radix - u) % radix :: subBorrow xs [] (if x < u then 1 else 0) := by
  simp [subBorrow]

@[simp] theorem subBorrow_nil (ys : List Nat) (u : Nat) : subBorrow [] ys u = [] := by
  simp [subBorrow]

theorem length_subBorrow : ∀ (xs ys : List Nat) (u : Nat), (subBorrow xs ys u).length = xs.length
  | [], _, _ => by simp
  | _ :: xs, ys, _ => by simp [subBorrow, length_subBorrow xs ys.tail]

theorem subBorrow_lt : ∀ (xs ys : List Nat) (u : Nat), ∀ d ∈ subBorrow xs ys u, d < radix
  | [], _, _ => by simp
  | x :: xs, ys, u => by
    intro d hd
    simp only [subBorrow, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt _ radix_pos
    · exact subBorrow_lt xs ys.tail _ d hd

/-- One step: digit plus subtrahend plus borrow-in is minuend plus
`radix` times borrow-out. -/
theorem subDigit_add (x y u : Nat) (hx : x < radix) (hy : y < radix) (hu : u ≤ 1) :
    (x + radix - y - u) % radix + y + u = x + radix * (if x < y + u then 1 else 0) := by
  rw [radix_eq] at *
  split <;> omega

theorem natOf_headD_tail (ys : List Nat) : natOf ys = ys.headD 0 + radix * natOf ys.tail := by
  cases ys <;> simp [natOf]

theorem headD_lt (ys : List Nat) (h : ∀ d ∈ ys, d < radix) : ys.headD 0 < radix := by
  cases ys with
  | nil => exact radix_pos
  | cons y ys => exact h y (List.mem_cons_self ..)

/-- `s_mp_sub` computes `|a| - |b| - u` when that is not negative. -/
theorem natOf_subBorrow : ∀ (xs ys : List Nat) (u : Nat),
    (∀ d ∈ xs, d < radix) → (∀ d ∈ ys, d < radix) → u ≤ 1 → natOf ys + u ≤ natOf xs →
    natOf (subBorrow xs ys u) = natOf xs - natOf ys - u
  | [], ys, u, _, _, _, _ => by simp [natOf]
  | x :: xs, ys, u, hx, hy, hu, hle => by
    have hx0 := hx x (List.mem_cons_self ..)
    have hy0 := headD_lt ys hy
    have hyt : ∀ d ∈ ys.tail, d < radix := fun d h => hy d (List.mem_of_mem_tail h)
    have hstep := subDigit_add x (ys.headD 0) u hx0 hy0 hu
    rw [natOf_headD_tail ys] at hle ⊢
    simp only [subBorrow, natOf_cons] at hle ⊢
    generalize ys.headD 0 = y at *
    generalize hb : (if x < y + u then 1 else 0) = b at *
    have hb1 : b ≤ 1 := by rw [← hb]; split <;> omega
    -- the borrow-out is covered by the higher digits
    have hYX : natOf ys.tail + b ≤ natOf xs := by
      have hrad := radix_pos
      by_cases hlt : x < y + u
      · simp only [hlt, ↓reduceIte] at hb; subst hb
        have : radix * natOf ys.tail < radix * natOf xs := by omega
        have := Nat.lt_of_mul_lt_mul_left this
        omega
      · simp only [hlt, ↓reduceIte] at hb; subst hb
        refine Nat.le_of_not_lt fun hgt => ?_
        have : radix * (natOf xs + 1) ≤ radix * natOf ys.tail := Nat.mul_le_mul_left _ hgt
        rw [Nat.mul_succ] at this
        omega
    rw [natOf_subBorrow xs ys.tail b (fun d h => hx d (List.mem_cons_of_mem _ h)) hyt hb1 hYX]
    have hm : radix * (natOf xs - natOf ys.tail - b) + radix * natOf ys.tail + radix * b =
        radix * natOf xs := by
      rw [← Nat.mul_add, ← Nat.mul_add]; congr 1; omega
    omega

/-! ## The `mp_int` contract -/

/-- The digits `s_mp_sub(a, b, c)` writes: the borrow chain over `a`'s used
digits, as a digit function (zero from `a->used` on). -/
def subDigits (a b : MpInt) (i : Nat) : Nat :=
  (subBorrow (a.digits.take a.used) (b.digits.take b.used) 0).getD i 0

/-- What `s_mp_sub(a, b, c)` leaves in `c` when `b->used ≤ a->used` and `c`
has room (`c->alloc ≥ a->used`, so `mp_grow` is not called): the borrow
chain's digits, zeros above (the loop writes `c[0 .. max)`,
`MP_ZERO_DIGITS` clears `c[max .. olduse)`, and `c`'s shape gives zeros
above `olduse`), `used` clamped from `a->used`, the sign reset if the
difference is zero; `alloc` unchanged. `c.sign` is the sign at entry (which
`mp_add`/`mp_sub` set just before the call). -/
structure SSubPost (a b c c' : MpInt) : Prop where
  alloc : c'.alloc = c.alloc
  len : c'.digits.length = c.alloc
  digit : c'.digit = subDigits a b
  used : c'.used = clampUsed (subDigits a b) a.used
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else c.sign

theorem MpInt.Shape.take_lt {a : MpInt} (ha : a.Shape) : ∀ d ∈ a.digits.take a.used, d < radix := by
  intro d hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
  have := ha.digit_lt j
  simp only [MpInt.digit, List.getElem_take] at this ⊢
  simpa [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show j < a.digits.length by simp at hj; omega)] using this

theorem subDigits_lt (a b : MpInt) (i : Nat) : subDigits a b i < radix := by
  unfold subDigits
  rw [List.getD_eq_getElem?_getD]
  cases hg : (subBorrow _ _ 0)[i]? with
  | none => exact radix_pos
  | some d => exact subBorrow_lt _ _ 0 d (List.mem_of_getElem? hg)

theorem length_subDigits {a : MpInt} (ha : a.Shape) (b : MpInt) :
    (subBorrow (a.digits.take a.used) (b.digits.take b.used) 0).length = a.used := by
  rw [length_subBorrow, List.length_take, ha.len, Nat.min_eq_left ha.used_le]

theorem subDigits_high {a : MpInt} (ha : a.Shape) (b : MpInt) (i : Nat) (hi : a.used ≤ i) :
    subDigits a b i = 0 := by
  unfold subDigits
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [length_subDigits ha]; exact hi

theorem natUpTo_subDigits {a b : MpInt} (ha : a.Shape) (hb : b.Shape) (hmag : b.mag ≤ a.mag) :
    natUpTo (subDigits a b) a.used = a.mag - b.mag := by
  have key := natOf_subBorrow (a.digits.take a.used) (b.digits.take b.used) 0
    ha.take_lt hb.take_lt (Nat.zero_le _)
    (by rw [← MpInt.mag_eq_natOf, ← MpInt.mag_eq_natOf]; omega)
  rw [Nat.sub_zero, ← MpInt.mag_eq_natOf, ← MpInt.mag_eq_natOf] at key
  rw [← key]
  rw [← List.take_of_length_le (Nat.le_of_eq (length_subDigits ha b)), natOf_take]
  rfl

/-- For `|a| ≥ |b|` with `b` clamped, `b->used ≤ a->used`: the C's
`min`/`max` are the right way round. -/
theorem MpInt.used_le_of_mag_le {a b : MpInt} (ha : a.Shape) (hb : b.Valid) (hmag : b.mag ≤ a.mag) :
    b.used ≤ a.used := by
  refine Nat.le_of_not_lt fun hlt => ?_
  have h1 := MpInt.mag_ge hb (by omega)
  have h2 := MpInt.mag_lt ha
  have : radix ^ a.used ≤ radix ^ (b.used - 1) := Nat.pow_le_pow_right radix_pos (by omega)
  omega

/-- `s_mp_sub` computes `|c| = |a| - |b|` when `|a| ≥ |b|`, and leaves `c`
valid. (The model reads `b` only through its used digits, so the
arithmetic holds without `b->used ≤ a->used`; the C needs it, and
`MpInt.used_le_of_mag_le` supplies it for clamped `b`.) -/
theorem SSubPost.spec {a b c c' : MpInt} (ha : a.Shape) (hb : b.Shape) (hmag : b.mag ≤ a.mag)
    (hroom : a.used ≤ c.alloc) (hc : c.alloc < 2 ^ 31)
    (hsign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg) (h : SSubPost a b c c') :
    c'.Valid ∧ c'.mag = a.mag - b.mag := by
  have hle := clampUsed_le (subDigits a b) a.used
  refine ⟨{ len := ?_, used_le := ?_, alloc_lt := ?_, digit_lt := ?_, high_zero := ?_,
            top := ?_, sign_ok := ?_, zero_pos := ?_ }, ?_⟩
  · rw [h.len, h.alloc]
  · rw [h.used, h.alloc]; omega
  · rw [h.alloc]; exact hc
  · rw [h.digit]; exact subDigits_lt a b
  · intro i hi
    rw [h.digit]
    by_cases hlt : i < a.used
    · exact clampUsed_zero _ _ i (h.used ▸ hi) hlt
    · exact subDigits_high ha b i (by omega)
  · intro hu; rw [h.digit, h.used]; exact clampUsed_top _ _ (h.used ▸ hu)
  · rw [h.sign]; split
    · exact Or.inl rfl
    · exact hsign
  · intro hu; rw [h.sign, ite_eq_left_iff.2 (fun h => absurd hu h)]
  · unfold MpInt.mag; rw [h.digit, h.used, natUpTo_clampUsed]; exact natUpTo_subDigits ha hb hmag

end Tom
