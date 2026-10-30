import Tom.Spec.Bits
import Tom.Spec.Sub

/-!
# The shape tests of the reduction moduli: `mp_dr_setup`, `mp_dr_is_modulus`, `mp_reduce_is_2k(_l)`

As the C states them (`vendor/libtommath/bn_mp_dr_setup.c`,
`bn_mp_dr_is_modulus.c`, `bn_mp_reduce_is_2k.c`, `bn_mp_reduce_is_2k_l.c`):

* `drSetupDigit a = 2^MP_DIGIT_BIT - dp[0]`;
* `IsDrModulus a`: at least two digits, all but the lowest `MP_MASK`;
  then `|a| + drSetupDigit a = radix ^ used` (`drSetupDigit_spec`: `a` is
  `b^k - d`, the form diminished-radix reduction needs);
* `isReduce2kL a`: zero is not, one digit is, otherwise at least
  `used / 2` digits are `MP_DIGIT_MAX` (`countMax`);
* `isReduce2k a`: zero is not, one digit is, otherwise every bit from
  `MP_DIGIT_BIT` up to `mp_count_bits(a)` is set.
-/

namespace Tom

open MpInt

/-- `mp_dr_setup(a, &d)`: `d = 2^MP_DIGIT_BIT - dp[0]`. -/
def drSetupDigit (a : MpInt) : Nat := radix - a.digit 0

/-- `mp_dr_is_modulus(a)`: at least two digits, all but the lowest `MP_MASK`. -/
def IsDrModulus (a : MpInt) : Prop := 2 ≤ a.used ∧ ∀ i, 1 ≤ i → i < a.used → a.digit i = Layout.mpMask

instance (a : MpInt) : Decidable (IsDrModulus a) :=
  decidable_of_iff (2 ≤ a.used ∧ ∀ i, i < a.used → 1 ≤ i → a.digit i = Layout.mpMask)
    ⟨fun ⟨h1, h2⟩ => ⟨h1, fun i h3 h4 => h2 i h4 h3⟩, fun ⟨h1, h2⟩ => ⟨h1, fun i h3 h4 => h2 i h4 h3⟩⟩

/-- Digits `1 … n-1` all `MP_MASK`: `Σ_{i<n} dig i · radix^i + radix = dig 0 + radix^n`. -/
theorem natUpTo_allMask (dig : Nat → Nat) :
    ∀ n, 1 ≤ n → (∀ i, 1 ≤ i → i < n → dig i = Layout.mpMask) → natUpTo dig n + radix = dig 0 + radix ^ n
  | 0, h, _ => absurd h (by omega)
  | 1, _, _ => by simp [natUpTo]
  | n + 2, _, h => by
    have ih := natUpTo_allMask dig (n + 1) (by omega) (fun i h1 h2 => h i h1 (by omega))
    have hd := h (n + 1) (by omega) (by omega)
    rw [natUpTo, hd, Tom.mpMask_eq]
    have hp : radix ^ (n + 2) = radix ^ (n + 1) * radix := Nat.pow_succ _ _
    have key : radix ^ (n + 1) * (radix - 1) + radix ^ (n + 1) = radix ^ (n + 1) * radix := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel radix_pos]
    omega

/-- **A DR modulus is `radix^used - drSetupDigit a`.** -/
theorem drSetupDigit_spec {a : MpInt} (ha : a.Shape) (h : IsDrModulus a) : a.mag + drSetupDigit a = radix ^ a.used := by
  have := natUpTo_allMask a.digit a.used (by have := h.1; omega) h.2
  have hd := ha.digit_lt 0
  unfold drSetupDigit MpInt.mag
  omega

/-- The number of digits below `n` equal to `MP_DIGIT_MAX` (`= MP_MASK`). -/
def countMax (dig : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => countMax dig n + if dig n = Layout.mpMask then 1 else 0

theorem countMax_le (dig : Nat → Nat) : ∀ n, countMax dig n ≤ n
  | 0 => Nat.le_refl _
  | n + 1 => by have := countMax_le dig n; simp only [countMax]; split <;> omega

/-- `mp_reduce_is_2k_l(a)` as the C states it (`MP_YES = 1`, `MP_NO = 0`). -/
def isReduce2kL (a : MpInt) : Nat :=
  if a.used = 0 then 0 else if a.used = 1 then 1 else if a.used / 2 ≤ countMax a.digit a.used then 1 else 0

/-- `mp_reduce_is_2k(a)` as the C states it (`MP_YES = 1`, `MP_NO = 0`): every bit from
`MP_DIGIT_BIT` up to `mp_count_bits(a)` set. -/
def isReduce2k (a : MpInt) : Nat :=
  if a.used = 0 then 0 else if a.used = 1 then 1
  else if (∀ ix, ix < countBits a → Layout.digitBits ≤ ix →
      (a.digit (ix / Layout.digitBits)).testBit (ix % Layout.digitBits) = true) then 1 else 0

/-- Digits `1 … n-1` all `MP_MASK`: at least `n - 1` of the first `n` digits are `MP_DIGIT_MAX`. -/
theorem countMax_allMask (dig : Nat → Nat) :
    ∀ n, (∀ i, 1 ≤ i → i < n → dig i = Layout.mpMask) → n - 1 ≤ countMax dig n
  | 0, _ => Nat.zero_le _
  | n + 1, h => by
    have ih := countMax_allMask dig n (fun i h1 h2 => h i h1 (by omega))
    simp only [countMax]
    by_cases hn : n = 0
    · subst hn; omega
    · rw [if_pos (h n (by omega) (by omega))]; omega

/-- **A DR modulus is a `2^k - L` one**: `mp_exptmod` sends it to `s_mp_exptmod(…, 1)` before it tests `mp_dr_is_modulus`. -/
theorem isReduce2kL_of_dr {a : MpInt} (h : IsDrModulus a) : isReduce2kL a = 1 := by
  have h2 := h.1
  have hc := countMax_allMask a.digit a.used h.2
  unfold isReduce2kL
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

end Tom
