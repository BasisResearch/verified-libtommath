import Tom.Spec.Div2d
import Tom.Spec.Mont

/-!
# `mp_div_2d`'s bit loop: the model step

`bn_mp_div_2d.c`'s loop runs from the top digit down: `x = c->used - 1, …, 0`, carry `r`
(the low `d = b % 28` bits of the digit above). After `mp_copy` (and `mp_rshd`) digit `j` of
`c` is `dig j = a[j + b / 28]`; the loop stores `dig x / 2^d + r · 2^(28 - d)` into digit `x`,
which is `div2dDigit a b x`. `DL a b u dig f x r` is the loop head's value premise (the digit
function `f` of `c`, the next index `x`, the carry `r`); `DL.start` enters it, `DL.step` is one
iteration (`x > 0`, the back edge), `DL.fin` the last (`x = 0`): then the digits below `c->alloc`
are `div2dDigit a b`. Stated in the forms the rows (`mdiv2drg.rows.json`) write.
-/

namespace Tom.Div2dRStep

open MpInt
open Mont (upd)

/-- The loop head at `x` with carry `r`: digits in `(x, u)` done, the others `dig`'s. -/
structure DL (a : MpInt) (b u : Nat) (dig f : Nat → Nat) (x r : Nat) : Prop where
  f_eq : ∀ j, f j = if x < j ∧ j < u then div2dDigit a b j else dig j
  carry : r = dig (x + 1) % 2 ^ (b % 28)
  lt : ∀ j, f j < 268435456

/-- The value stored: `(dig x >> d) | (r << (28 - d))` with `r` the carry. -/
theorem stored {a : MpInt} {b x r : Nat} {dig : Nat → Nat} (hdig : ∀ j, dig j = a.digit (j + b / 28))
    (hr : r = dig (x + 1) % 2 ^ (b % 28)) :
    dig x / 2 ^ (b % 28) + r * 2 ^ (28 - b % 28) = div2dDigit a b x := by
  subst hr
  simp only [div2dDigit, Layout.digitBits, hdig, Nat.add_right_comm x 1]

theorem DL.start {a : MpInt} {b u : Nat} {dig : Nat → Nat} (hu : 0 < u) (hz : dig u = 0)
    (hlt : ∀ j, dig j < 268435456) : DL a b u dig dig (u - 1) 0 where
  f_eq j := by rw [if_neg (by omega)]
  carry := by rw [show u - 1 + 1 = u by omega, hz, Nat.zero_mod]
  lt := hlt

theorem div2dDigit_lt (a : MpInt) (ha : a.Shape) (b j : Nat) : div2dDigit a b j < 268435456 :=
  (div2dDigit_c _ _ _ (Nat.mod_lt _ (by decide)) (ha.digit_lt _) (Nat.mod_lt _ (Nat.two_pow_pos _))).2

/-- The stored digit fits (`div2dDigit_c`). -/
theorem stored_lt {e r d : Nat} (hd : d < 28) (he : e < 268435456) (hr : r < 2 ^ d) :
    e / 2 ^ d + r * 2 ^ (28 - d) < 268435456 :=
  (div2dDigit_c e r d hd he hr).2

/-- One iteration (`x > 0`): store digit `x`, carry its low bits down. -/
theorem DL.step {a : MpInt} {b u x r : Nat} {dig f : Nat → Nat} (h : DL a b u dig f x r) (ha : a.Shape)
    (hdig : ∀ j, dig j = a.digit (j + b / 28)) (hx0 : 0 < x) (hxu : x < u) :
    DL a b u dig (upd f x (f x / 2 ^ (b % 28) + r * 2 ^ (28 - b % 28))) (x - 1) (f x % 2 ^ (b % 28)) := by
  have hfx : f x = dig x := by rw [h.f_eq x, if_neg (by omega)]
  have hv := stored hdig h.carry
  rw [hfx]
  refine { f_eq := fun j => ?_, carry := by rw [show x - 1 + 1 = x by omega], lt := fun j => ?_ }
  · by_cases hj : j = x
    · subst hj; rw [Mont.upd_same, hv, if_pos (by omega)]
    · rw [Mont.upd_ne _ _ hj, h.f_eq j]
      by_cases h1 : x < j ∧ j < u
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
  · by_cases hj : j = x
    · subst hj; rw [Mont.upd_same, hv]; exact div2dDigit_lt a ha b j
    · rw [Mont.upd_ne _ _ hj]; exact h.lt j

/-- The last iteration (`x = 0`): every digit is the quotient's (the high ones are zero in both). -/
theorem DL.fin {a : MpInt} {b u r : Nat} {dig f : Nat → Nat} (h : DL a b u dig f 0 r)
    (hdig : ∀ j, dig j = a.digit (j + b / 28)) (hhi : ∀ j, u ≤ j → dig j = div2dDigit a b j) :
    ∀ j, upd f 0 (f 0 / 2 ^ (b % 28) + r * 2 ^ (28 - b % 28)) j = div2dDigit a b j := by
  have hf0 : f 0 = dig 0 := by rw [h.f_eq 0, if_neg (by omega)]
  intro j
  by_cases hj : j = 0
  · subst hj; rw [Mont.upd_same, hf0, stored hdig h.carry]
  · rw [Mont.upd_ne _ _ hj, h.f_eq j]
    by_cases h1 : j < u
    · rw [if_pos ⟨by omega, h1⟩]
    · rw [if_neg (by omega), hhi j (by omega)]

end Tom.Div2dRStep
