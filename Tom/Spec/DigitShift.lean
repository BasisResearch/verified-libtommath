import Tom.Spec.Set

/-!
# `mp_rshd`, `mp_lshd`: digit shifts

What the C functions leave (`vendor/libtommath/bn_mp_{rshd,lshd}.c`), one
field per C branch, and their meaning (`….spec`).

* `mp_rshd(a, k)`: `k ≤ 0` does nothing; `a->used ≤ k` is `mp_zero(a)`;
  otherwise `dp[x] := dp[x + k]` for `x < used - k`, the digits
  `[used - k, used)` zeroed, `used -= k` (`RshdShift`). Meaning: `mag / radix^k`.
* `mp_lshd(a, k)` (`a->alloc ≥ a->used + k`, so no `mp_grow`, D5): `k ≤ 0` or
  `a` zero does nothing; otherwise `used += k`, `dp[x] := dp[x - k]` for
  `x ∈ [k, used + k)`, the digits `[0, k)` zeroed (`LshdShift`). Meaning:
  `mag * radix^k`.

The shift amount `k` is the C's `int b` when it is nonnegative.
-/

namespace Tom

open MpInt

private theorem ite_pos' {α : Type} {p : Prop} [Decidable p] {a b : α} (h : p) : (if p then a else b) = a := by
  simp [h]

private theorem ite_neg' {α : Type} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) : (if p then a else b) = b := by
  simp [h]

/-- `Σ_{i<k+n} = Σ_{i<k} + radix^k Σ_{i<n} dig (i + k)`. -/
theorem natUpTo_digitShift (dig : Nat → Nat) (k : Nat) :
    ∀ n, natUpTo dig (k + n) = natUpTo dig k + radix ^ k * natUpTo (fun i => dig (i + k)) n
  | 0 => by simp [natUpTo]
  | n + 1 => by
    rw [show k + (n + 1) = (k + n) + 1 by omega, natUpTo, natUpTo_digitShift dig k n, natUpTo, Nat.pow_add,
      Nat.mul_add, Nat.mul_assoc, Nat.add_comm n k]
    omega

/-! ## `mp_rshd` -/

/-- The shifting branch of `mp_rshd(a, k)` (`0 < k < used`). -/
structure RshdShift (a : MpInt) (k : Nat) (a' : MpInt) : Prop where
  alloc : a'.alloc = a.alloc
  len : a'.digits.length = a.alloc
  used : a'.used = a.used - k
  sign : a'.sign = a.sign
  digit : ∀ i, a'.digit i = if i + k < a.used then a.digit (i + k) else if i < a.used then 0 else a.digit i

/-- What `mp_rshd(a, k)` leaves, by branch. -/
structure RshdPost (a : MpInt) (k : Nat) (a' : MpInt) : Prop where
  noop : k = 0 → a' = a
  zero : 0 < k → a.used ≤ k → ZeroPost a a'
  shift : 0 < k → k < a.used → RshdShift a k a'

/-- The digits of the shifting branch. -/
def rshdDigits (a : MpInt) (k i : Nat) : Nat :=
  if i + k < a.used then a.digit (i + k) else if i < a.used then 0 else a.digit i

theorem RshdShift.spec {a a' : MpInt} {k : Nat} (ha : a.Valid) (hk : k < a.used) (h : RshdShift a k a') :
    a'.Valid ∧ a'.mag = a.mag / radix ^ k := by
  have hlo : ∀ i, i < a.used - k → a'.digit i = a.digit (i + k) := fun i hi => by
    rw [h.digit, ite_pos' (by omega)]
  have hhi : ∀ i, a.used - k ≤ i → a'.digit i = 0 := fun i hi => by
    rw [h.digit, ite_neg' (by omega)]; split; rfl; exact ha.high_zero i (by omega)
  refine ⟨{ len := by rw [h.len, h.alloc], used_le := by rw [h.used, h.alloc]; have := ha.used_le; omega
            alloc_lt := by rw [h.alloc]; exact ha.alloc_lt
            digit_lt := fun i => by rw [h.digit]; split; exact ha.digit_lt _; split; exact radix_pos
                                    exact ha.digit_lt _
            high_zero := fun i hi => hhi i (by rw [h.used] at hi; exact hi)
            top := fun hu => by
              rw [h.used] at hu ⊢; rw [hlo _ (by omega), show a.used - k - 1 + k = a.used - 1 by omega]
              exact ha.top (by omega)
            sign_ok := by rw [h.sign]; exact ha.sign_ok
            zero_pos := fun hu => by rw [h.used] at hu; omega }, ?_⟩
  have hs := natUpTo_digitShift a.digit k (a.used - k)
  rw [show k + (a.used - k) = a.used by omega] at hs
  have hlt := natUpTo_lt a.digit ha.digit_lt k
  unfold MpInt.mag; rw [hs, h.used, natUpTo_congr _ hlo, Nat.add_mul_div_left _ _ (Nat.pow_pos radix_pos),
    Nat.div_eq_of_lt hlt, Nat.zero_add]

/-- `mp_rshd(a, k)` divides the magnitude by `radix^k` (truncating) and keeps `a` valid. -/
theorem RshdPost.spec {a a' : MpInt} {k : Nat} (ha : a.Valid) (h : RshdPost a k a') :
    a'.Valid ∧ a'.mag = a.mag / radix ^ k := by
  rcases Nat.eq_zero_or_pos k with h0 | hk
  · rw [h.noop h0, h0]; exact ⟨ha, by simp⟩
  by_cases hu : a.used ≤ k
  · have ⟨hv, hm, _⟩ := (h.zero hk hu).spec ha.toShape
    refine ⟨hv, ?_⟩
    rw [hm, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (MpInt.mag_lt ha.toShape)
      (Nat.pow_le_pow_right radix_pos hu))]
  · exact (h.shift hk (by omega)).spec ha (by omega)

/-! ## `mp_lshd` -/

/-- The shifting branch of `mp_lshd(a, k)` (`0 < k`, `0 < used`). -/
structure LshdShift (a : MpInt) (k : Nat) (a' : MpInt) : Prop where
  alloc : a'.alloc = a.alloc
  len : a'.digits.length = a.alloc
  used : a'.used = a.used + k
  sign : a'.sign = a.sign
  digit : ∀ i, a'.digit i = if i < k then 0 else if i < a.used + k then a.digit (i - k) else a.digit i

/-- What `mp_lshd(a, k)` leaves, by branch (`a->alloc ≥ a->used + k`). -/
structure LshdPost (a : MpInt) (k : Nat) (a' : MpInt) : Prop where
  noop : k = 0 ∨ a.used = 0 → a' = a
  shift : 0 < k → 0 < a.used → LshdShift a k a'

/-- The digits of the shifting branch. -/
def lshdDigits (a : MpInt) (k i : Nat) : Nat :=
  if i < k then 0 else if i < a.used + k then a.digit (i - k) else a.digit i

theorem LshdShift.spec {a a' : MpInt} {k : Nat} (ha : a.Valid) (hroom : a.used + k ≤ a.alloc)
    (hu : 0 < a.used) (h : LshdShift a k a') : a'.Valid ∧ a'.mag = a.mag * radix ^ k := by
  have hhi : ∀ i, a.used + k ≤ i → a'.digit i = 0 := fun i hi => by
    rw [h.digit, ite_neg' (by omega), ite_neg' (by omega)]; exact ha.high_zero i (by omega)
  refine ⟨{ len := by rw [h.len, h.alloc], used_le := by rw [h.used, h.alloc]; exact hroom
            alloc_lt := by rw [h.alloc]; exact ha.alloc_lt
            digit_lt := fun i => by rw [h.digit]; split; exact radix_pos; split <;> exact ha.digit_lt _
            high_zero := fun i hi => hhi i (by rw [h.used] at hi; exact hi)
            top := fun _ => by
              rw [h.used, h.digit, ite_neg' (by omega), ite_pos' (by omega),
                show a.used + k - 1 - k = a.used - 1 by omega]
              exact ha.top hu
            sign_ok := by rw [h.sign]; exact ha.sign_ok
            zero_pos := fun hu' => by rw [h.used] at hu'; omega }, ?_⟩
  have hs := natUpTo_digitShift a'.digit k a.used
  rw [Nat.add_comm k] at hs
  have h0 : natUpTo a'.digit k = 0 := by
    rw [natUpTo_zeros a'.digit 0 k (Nat.zero_le _) (fun i _ hi => by rw [h.digit, ite_pos' hi])]; rfl
  unfold MpInt.mag; rw [h.used, hs, h0, Nat.zero_add, Nat.mul_comm]
  congr 1
  exact natUpTo_congr _ fun i hi => by
    rw [h.digit, ite_neg' (by omega), ite_pos' (by omega), Nat.add_sub_cancel]

/-- `mp_lshd(a, k)` multiplies the magnitude by `radix^k` and keeps `a` valid. -/
theorem LshdPost.spec {a a' : MpInt} {k : Nat} (ha : a.Valid) (hroom : a.used + k ≤ a.alloc)
    (h : LshdPost a k a') : a'.Valid ∧ a'.mag = a.mag * radix ^ k := by
  by_cases h0 : k = 0 ∨ a.used = 0
  · rw [h.noop h0]
    rcases h0 with h0 | h0
    · simp [h0, ha]
    · simp [MpInt.mag_used_zero h0, ha]
  · exact (h.shift (by omega) (by omega)).spec ha hroom (by omega)

end Tom
