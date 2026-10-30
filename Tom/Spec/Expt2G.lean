import Tom.Spec.Expt2
import Tom.Spec.Grow6Step

/-!
# `mp_2expt(a, b)` growing `a`

`mp_zero(a)` leaves `a` the zero of `a->alloc` digits (`ZeroPost.eq_zeroN`); `mp_grow(a, b / 28 + 1)`
keeps it when there is room and otherwise reallocates it to the zero of `b / 28 + 1` digits
(`MpInt.zeroN_growTo`): `expt2In a b`, the zero of `max a->alloc (b / 28 + 1)` digits, is what the
digit store finds. `Expt2Post (expt2In a b) b` is `Expt2Post` from it, so `Expt2Post.spec` applies
with no room premise on `a` (`expt2In_room`).
-/

namespace Tom

open MpInt

/-- `a` after `mp_zero(a)` and `mp_grow(a, b / 28 + 1)`. -/
def expt2In (a : MpInt) (b : Nat) : MpInt := MpInt.zeroN (max a.alloc (b / Layout.digitBits + 1))

/-- The value `mp_2expt` stores over `A`: one digit `2^(b mod 28)` at `b / 28`. -/
def expt2Res (A : MpInt) (b : Nat) : MpInt :=
  MpInt.ofDigits (b / 28 + 1) A.alloc A.sign fun j => if j = b / 28 then 2 ^ (b % 28) else 0

theorem ZeroPost.eq_zeroN {a x : MpInt} (h : ZeroPost a x) : x = MpInt.zeroN a.alloc :=
  MpInt.ext_len h.used h.alloc h.sign (by rw [h.len]; exact (List.length_replicate ..).symm)
    (funext fun i => by rw [h.digit, MpInt.zeroN_digit])

theorem MpInt.zeroN_growTo {n k : Nat} : (MpInt.zeroN n).growTo k = MpInt.zeroN k :=
  MpInt.ext_len rfl rfl rfl (by rw [MpInt.growTo, MpInt.ofDigits_len]; exact (List.length_replicate ..).symm)
    (funext fun i => by rw [MpInt.growTo, MpInt.ofDigits_digit, MpInt.zeroN_digit, MpInt.zeroN_digit]; split <;> rfl)

theorem expt2In_keep {a : MpInt} {b : Nat} (h : b / 28 + 1 ≤ a.alloc) : expt2In a b = MpInt.zeroN a.alloc := by
  show MpInt.zeroN (max a.alloc (b / 28 + 1)) = _; rw [Nat.max_eq_left h]

theorem expt2In_grow {a : MpInt} {b : Nat} (h : a.alloc < b / 28 + 1) :
    expt2In a b = (MpInt.zeroN a.alloc).growTo (b / 28 + 1) := by
  show MpInt.zeroN (max a.alloc (b / 28 + 1)) = _; rw [Nat.max_eq_right (Nat.le_of_lt h), MpInt.zeroN_growTo]

theorem expt2In_room (a : MpInt) (b : Nat) : b / 28 + 1 ≤ (expt2In a b).alloc :=
  Nat.le_max_right _ _

theorem expt2In_alloc_lt {a : MpInt} {b : Nat} (ha : a.alloc < 2 ^ 31) (hb : b < 2 ^ 31) :
    (expt2In a b).alloc < 2 ^ 31 := by
  show max a.alloc (b / 28 + 1) < 2 ^ 31; omega

/-- **The store**: over a zero `A` with room, `expt2Res A b` is `mp_2expt`'s result. -/
theorem expt2Res_post {A : MpInt} {b n : Nat} (hA : A = MpInt.zeroN n) (hroom : b / 28 + 1 ≤ A.alloc) :
    Expt2Post A b (expt2Res A b) :=
  { alloc := rfl, len := MpInt.ofDigits_len _ _ _ _, used := rfl, sign := by rw [hA]; rfl
    digit := fun j => by
      rw [expt2Res, MpInt.ofDigits_digit]; split
      · rfl
      · rw [if_neg (by simp only [Layout.digitBits]; omega)] }

theorem expt2Res_postI {a A : MpInt} {b : Nat} (hA : A = expt2In a b) : Expt2Post (expt2In a b) b (expt2Res A b) := by
  subst hA; exact expt2Res_post rfl (expt2In_room a b)

/-- **`mp_2expt(a, b)` growing**: `2^b`, valid. -/
theorem Expt2Post.specG {a a' : MpInt} {b : Nat} (ha : a.alloc < 2 ^ 31) (hb : b < 2 ^ 31)
    (h : Expt2Post (expt2In a b) b a') : a'.Valid ∧ a'.mag = 2 ^ b ∧ a'.val = 2 ^ b :=
  Expt2Post.spec (expt2In_room a b) (expt2In_alloc_lt ha hb) h

end Tom
