import Tom.Spec.Set
import Tom.Spec.Algo

/-!
# `mp_2expt(a, b)`: `a = 2^b`

The C (`bn_mp_2expt.c`): `mp_zero(a)`, `mp_grow(a, b / MP_DIGIT_BIT + 1)`,
`a->used = b / MP_DIGIT_BIT + 1`, `a->dp[b / MP_DIGIT_BIT] = 1 << (b % MP_DIGIT_BIT)`.
`Expt2Post` is that state (when `mp_grow` does not reallocate, D5); `Expt2Post.spec`:
`a'` is valid with value `2^b`.
-/

namespace Tom

open MpInt

/-- What `mp_2expt(a, b)` leaves in `a` (`b ≥ 0`, `b / 28 + 1 ≤ a->alloc`): one digit
`2^(b mod 28)` at `b / 28`, the rest zero. -/
structure Expt2Post (a : MpInt) (b : Nat) (a' : MpInt) : Prop where
  alloc : a'.alloc = a.alloc
  len : a'.digits.length = a.alloc
  used : a'.used = b / Layout.digitBits + 1
  sign : a'.sign = Layout.mpZpos
  digit : ∀ j, a'.digit j = if j = b / Layout.digitBits then 2 ^ (b % Layout.digitBits) else 0

theorem natUpTo_zero_fn : ∀ n, natUpTo (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by simp [natUpTo, natUpTo_zero_fn n]

/-- **`mp_2expt`** computes `2^b`, valid. -/
theorem Expt2Post.spec {a a' : MpInt} {b : Nat} (hroom : b / Layout.digitBits + 1 ≤ a.alloc)
    (hal : a.alloc < 2 ^ 31) (h : Expt2Post a b a') : a'.Valid ∧ a'.mag = 2 ^ b ∧ a'.val = 2 ^ b := by
  have hd : b % Layout.digitBits < Layout.digitBits := Nat.mod_lt _ (by decide)
  have hlt : 2 ^ (b % Layout.digitBits) < radix := Nat.pow_lt_pow_right (by decide) hd
  have hmag : a'.mag = 2 ^ b := by
    unfold MpInt.mag
    rw [h.used, natUpTo, natUpTo_congr (e := fun _ => 0) _ (fun i hi => by rw [h.digit, if_neg (by omega)]),
      natUpTo_zero_fn, h.digit, if_pos rfl, Nat.zero_add, radix, ← Nat.pow_mul, ← Nat.pow_add,
      Nat.div_add_mod]
  refine ⟨{ len := by rw [h.len, h.alloc], used_le := by rw [h.used, h.alloc]; exact hroom
            alloc_lt := by rw [h.alloc]; exact hal
            digit_lt := fun i => by rw [h.digit]; split; exact hlt; exact radix_pos
            high_zero := fun i hi => by rw [h.digit, if_neg (by rw [h.used] at hi; omega)]
            top := fun _ => by rw [h.used, Nat.add_sub_cancel, h.digit, if_pos rfl]; exact Nat.ne_of_gt (Nat.two_pow_pos _)
            sign_ok := Or.inl h.sign
            zero_pos := fun hu => by rw [h.used] at hu; exact absurd hu (Nat.succ_ne_zero _) }, hmag, ?_⟩
  unfold MpInt.val; rw [h.sign, hmag]; simp [Layout.mpZpos, Layout.mpNeg]

end Tom
