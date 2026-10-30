import Tom.Spec.Shift
import Tom.Spec.Grow6Step
import Tom.Spec.Sub

/-!
# `mp_mul_2(a, a)` with growth: the model steps

`mp_mul_2(a, a)` grows `a` to `a->used + 1` digits when `a->alloc ≤ a->used` (`mul2In`), then
doubles in place: the loop stores digit `x` as `m2g a x = (2 a[x] + carry) mod 2^28` (the
carry `addCarryAt a a x`, the next one `a[x] >> 27`: `m2c_succ`), a last carry digit `1` when
there is one, `used := a->used + carry`, the sign kept. `m2out a A n` is what it leaves (the
digits of `a + a` over `A`'s array, `n` used), and `m2out_post` its `Mul2Post` over the grown
input, so `Mul2Post.spec` gives the value `2 a`. `m2fin0`/`m2fin1`/`m2fin_nil`: the digits the
loop leaves equal `m2out`'s (no carry, a carry, an empty operand).
-/

namespace Tom

open MpInt

/-- The destination `mp_mul_2(a, a)` writes: grown to `a->used + 1` when short. -/
def mul2In (a : MpInt) : MpInt := if a.alloc < a.used + 1 then a.growTo (a.used + 1) else a

theorem mul2In_grown {a : MpInt} (ha : a.Shape) (h31 : a.used + 1 < 2 ^ 31) : GrownOf a (mul2In a) :=
  GrownOf.ite ha id h31

theorem mul2In_room (a : MpInt) : a.used + 1 ≤ (mul2In a).alloc := by
  unfold mul2In; split
  · simp [MpInt.growTo, MpInt.ofDigits]
  · omega

/-- The loop's digit `x`: `(2 a[x] + carry) mod 2^28`. -/
def m2g (a : MpInt) (j : Nat) : Nat := (2 * a.digit j + addCarryAt a a j) % 268435456

theorem m2g_eq {a : MpInt} (ha : a.Shape) {j : Nat} (hj : j < a.used) : m2g a j = addDigits a a j := by
  rw [addDigits_lt_max ha ha (by rw [Nat.max_self]; exact hj), radix_eq, m2g]
  congr 1; omega

/-- The next carry is the digit's top bit (`a[x] >> 27`). -/
theorem m2c_succ {a : MpInt} (ha : a.Shape) (j : Nat) : addCarryAt a a (j + 1) = a.digit j / 134217728 := by
  rw [addCarryAt_succ, radix_eq]
  have := addCarryAt_le_one ha ha j
  have := ha.digit_lt j
  rw [radix_eq] at this
  omega

/-- What `mp_mul_2(a, a)` leaves over `A`'s array, `n` digits used. -/
def m2out (a A : MpInt) (n : Nat) : MpInt := MpInt.ofDigits n A.alloc a.sign (addDigits a a)

theorem m2out_post {a A : MpInt} (ha : a.Shape) (hroom : a.used + 1 ≤ A.alloc) :
    Mul2Post a A (m2out a A (a.used + addCarryAt a a a.used)) where
  alloc := rfl
  len := MpInt.ofDigits_len _ _ _ _
  digit := funext fun j => by
    rw [m2out, MpInt.ofDigits_digit]; split
    · rfl
    · have := addCarryAt_le_one ha ha a.used
      exact (addDigits_self_high ha j (by omega)).symm
  used := rfl
  sign := rfl

theorem m2fin0 {a A : MpInt} {n : Nat} (ha : a.Shape) (hc : addCarryAt a a a.used = 0) (j : Nat) (hj : j < A.alloc) :
    (m2out a A n).digit j = if j < a.used then m2g a j else a.digit j := by
  rw [m2out, MpInt.ofDigits_digit, if_pos hj]; split
  · rename_i h; exact (m2g_eq ha h).symm
  · rw [ha.high_zero j (by omega)]; exact addDigits_self_high ha j (by omega)

theorem m2fin1 {a A : MpInt} {n : Nat} (ha : a.Shape) (hc : addCarryAt a a a.used = 1) (j : Nat) (hj : j < A.alloc) :
    (m2out a A n).digit j = if j = a.used then 1 else if j < a.used then m2g a j else a.digit j := by
  rw [m2out, MpInt.ofDigits_digit, if_pos hj]; split
  · rename_i h; subst h; rw [addDigits_self_used ha, hc]
  · split
    · rename_i _ h; exact (m2g_eq ha h).symm
    · rw [ha.high_zero j (by omega)]; exact addDigits_self_high ha j (by omega)

theorem m2fin_nil {a A : MpInt} {n : Nat} (ha : a.Shape) (hu : a.used = 0) (hd : A.digit = a.digit) (j : Nat)
    (hj : j < A.alloc) : (m2out a A n).digit j = A.digit j := by
  rw [m2out, MpInt.ofDigits_digit, if_pos hj, hd, ha.high_zero j (by omega)]
  exact addDigits_self_high ha j (by rw [hu]; simp)

theorem m2c_nil {a : MpInt} (hu : a.used = 0) : a.used + addCarryAt a a a.used = 0 := by
  rw [hu]; rfl

/-- **`mp_mul_2(a, a)` with growth computes `2 a`**, leaves `a` valid and only grows it. -/
theorem m2out_spec {a A : MpInt} (ha : a.Valid) (hg : GrownOf a A) (hroom : a.used + 1 ≤ A.alloc) :
    (m2out a A (a.used + addCarryAt a a a.used)).Valid ∧
      (m2out a A (a.used + addCarryAt a a a.used)).val = 2 * a.val ∧
      a.alloc ≤ (m2out a A (a.used + addCarryAt a a a.used)).alloc := by
  obtain ⟨hv, -, hval⟩ := Mul2Post.spec ha hroom hg.shape.alloc_lt (m2out_post ha.toShape hroom)
  exact ⟨hv, hval, hg.alloc⟩

end Tom
