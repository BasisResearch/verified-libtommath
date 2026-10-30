import Tom.Spec.Signed
import Tom.Spec.Algo

/-!
# `mp_init`, `mp_init_size`, `mp_grow`, `mp_clear`: what they leave

* `mp_init_size(a, size)` (`bn_mp_init_size.c`) allocates
  `MP_MAX(MP_MIN_PREC, size)` digits (`MP_MIN_PREC = (64 + 28 - 1) / 28 = 3`
  for `MP_32BIT`, `initPrec`) and sets `a` to zero: `MpInt.zeroN`.
  `mp_init(a)` is the same with `MP_PREC = 32` digits.
* `mp_grow(a, size)` with `a->alloc < size` reallocates to `size` digits:
  the old digits, zeros above (`MP_ZERO_DIGITS`), `alloc = size`; `used` and
  `sign` unchanged (`GrowPost`). `GrowPost.spec`: the value and the
  invariants are kept.
* `mp_clear(a)` frees the digits and zeroes the struct (`MpInt.cleared`).
-/

namespace Tom

/-- `MP_MIN_PREC` for `MP_32BIT` (`tommath_private.h`): `(64 + 28 - 1) / 28`. -/
def minPrec : Nat := (64 + Layout.digitBits - 1) / Layout.digitBits

theorem minPrec_eq : minPrec = 3 := by decide

/-- `MP_PREC` (`tommath.h`, not `MP_LOW_MEM`). -/
def defPrec : Nat := 32

/-- The precision `mp_init_size(a, size)` allocates. -/
def initPrec (size : Nat) : Nat := max minPrec size

/-- A zero `mp_int` with `n` digits allocated (`used = 0`, `MP_ZPOS`, all digits zero). -/
def MpInt.zeroN (n : Nat) : MpInt := ⟨0, n, Layout.mpZpos, List.replicate n 0⟩

/-- A cleared `mp_int` (`mp_clear`): every field zero, no digits. -/
def MpInt.cleared : MpInt := ⟨0, 0, 0, []⟩

theorem MpInt.zeroN_digit (n i : Nat) : (MpInt.zeroN n).digit i = 0 := by
  simp only [MpInt.zeroN, MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem MpInt.zeroN_valid {n : Nat} (h : n < 2 ^ 31) : (MpInt.zeroN n).Valid :=
  { len := List.length_replicate .., used_le := Nat.zero_le _, alloc_lt := h
    digit_lt := fun i => by rw [zeroN_digit]; exact Nat.two_pow_pos _
    high_zero := fun i _ => zeroN_digit n i
    top := fun h => absurd h (Nat.lt_irrefl 0)
    sign_ok := .inl rfl, zero_pos := fun _ => rfl }

theorem MpInt.zeroN_val (n : Nat) : (MpInt.zeroN n).val = 0 := by
  unfold MpInt.val
  rw [MpInt.mag_used_zero (x := MpInt.zeroN n) rfl]
  simp

/-- **What `mp_grow(a, size)` leaves when it reallocates** (`a->alloc < size`):
`alloc = size`, the old digits below the old `alloc`, zeros above; `used` and
`sign` as they were. -/
structure GrowPost (a : MpInt) (size : Nat) (a' : MpInt) : Prop where
  used : a'.used = a.used
  sign : a'.sign = a.sign
  alloc : a'.alloc = size
  len : a'.digits.length = size
  low : ∀ i, i < a.alloc → a'.digit i = a.digit i
  high : ∀ i, a.alloc ≤ i → a'.digit i = 0

/-- `mp_grow` keeps the value and the invariants. -/
theorem GrowPost.spec {a a' : MpInt} {size : Nat} (ha : a.Shape) (hs : a.alloc < size)
    (h2 : size < 2 ^ 31) (h : GrowPost a size a') :
    a'.Shape ∧ a'.mag = a.mag ∧ a'.val = a.val ∧ (a.Valid → a'.Valid) := by
  have hdig : ∀ i, a'.digit i = a.digit i := fun i => by
    by_cases hi : i < a.alloc
    · exact h.low i hi
    · rw [h.high i (by omega), ha.high_zero i (by have := ha.used_le; omega)]
  have hmag : a'.mag = a.mag := by
    unfold MpInt.mag; rw [h.used]; exact natUpTo_congr _ fun i _ => hdig i
  have hsh : a'.Shape :=
    { len := by rw [h.len, h.alloc], used_le := by rw [h.used, h.alloc]; have := ha.used_le; omega
      alloc_lt := by rw [h.alloc]; exact h2
      digit_lt := fun i => by rw [hdig]; exact ha.digit_lt i
      high_zero := fun i hi => by rw [hdig]; exact ha.high_zero i (by rw [← h.used]; exact hi) }
  refine ⟨hsh, hmag, by unfold MpInt.val; rw [hmag, h.sign], fun hv => ?_⟩
  exact { hsh with
    top := fun hu => by rw [hdig, h.used]; exact hv.top (by rw [← h.used]; exact hu)
    sign_ok := by rw [h.sign]; exact hv.sign_ok
    zero_pos := fun hu => by rw [h.sign]; exact hv.zero_pos (by rw [← h.used]; exact hu) }

end Tom
