import Tom.Spec.Init
import Tom.Spec.DigitShift
import Tom.Spec.Div2d
import Tom.Spec.Mont
import Tom.Spec.Ops

/-!
# Growing callees: the grown input, and `mp_lshd`'s loop model

`mp_grow(a, n)` (`GrowPost`) leaves `a` with `n` digits, the old ones kept and zeros above:
for a shaped `a` that is the canonical `a.growTo n` (`GrowPost.eq_growTo`). A function that
grows its destination first and then works as with room computes, from the grown input, what
the room contract computes from `a`:

* `lshdIn a k`: what `mp_lshd(a, k)` shifts (`a` grown to `used + k` iff `0 < k`, `0 < used`,
  `alloc < used + k`, the C's order of tests);
* `mul2dIn a b`: what `mp_mul_2d(a, b, a)` shifts (grown to `used + b / 28 + 1` iff short);
* `mulDIn a c`: the destination `mp_mul_d(a, b, c)` writes (grown to `a->used + 1` iff short).

`mp_lshd`'s copy loop: after `t` iterations (from the top) the digits `[used + k - t, used + k)`
hold `a`'s digits moved up by `k` (`lshdT`, one step `lshdT_step`); `memset(dp, 0, 4 k)` then
leaves `lshdDigits` (`lshdT_fill`).
-/

namespace Tom

open MpInt

/-- `a` with `n` digits: its digit function on `[0, n)`. -/
def MpInt.growTo (a : MpInt) (n : Nat) : MpInt := MpInt.ofDigits a.used n a.sign a.digit

theorem MpInt.digit_ge_alloc {a : MpInt} (ha : a.Shape) {i : Nat} (hi : a.alloc ≤ i) : a.digit i = 0 := by
  simp only [MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [ha.len]; exact hi),
    Option.getD_none]

theorem MpInt.growTo_digit {a : MpInt} (ha : a.Shape) {n : Nat} (hn : a.alloc ≤ n) : (a.growTo n).digit = a.digit :=
  funext fun i => by
    rw [MpInt.growTo, MpInt.ofDigits_digit]; split
    · rfl
    · exact (MpInt.digit_ge_alloc ha (by omega)).symm

/-- Two `mp_int`s with the same fields and digit functions over equally long arrays. -/
theorem MpInt.ext_len {a b : MpInt} (hu : a.used = b.used) (hal : a.alloc = b.alloc) (hs : a.sign = b.sign)
    (hl : a.digits.length = b.digits.length) (hd : a.digit = b.digit) : a = b := by
  obtain ⟨u, al, s, ds⟩ := a; obtain ⟨u', al', s', ds'⟩ := b
  simp only at hu hal hs hl; subst hu hal hs
  have : ds = ds' := List.ext_getElem hl fun i h1 h2 => by
    have := congrFun hd i
    simp only [MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2, Option.getD_some] at this
    exact this
  subst this; rfl

/-- **`mp_grow`'s result is the canonical grown `a`.** -/
theorem GrowPost.eq_growTo {a a' : MpInt} {n : Nat} (ha : a.Shape) (h : GrowPost a n a') : a' = a.growTo n :=
  MpInt.ext_len h.used h.alloc h.sign (by rw [h.len, MpInt.growTo, MpInt.ofDigits_len])
    (funext fun i => by
      rw [MpInt.growTo, MpInt.ofDigits_digit]
      by_cases hn : i < n
      · rw [if_pos hn]
        by_cases hi : i < a.alloc
        · exact h.low i hi
        · rw [h.high i (by omega), MpInt.digit_ge_alloc ha (by omega)]
      · rw [if_neg hn]
        have hl : a'.digits.length ≤ i := by rw [h.len]; omega
        simp only [MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_eq_none hl, Option.getD_none])

theorem MpInt.growTo_self {a : MpInt} (ha : a.Shape) : a.growTo a.alloc = a :=
  (GrowPost.eq_growTo ha ⟨rfl, rfl, rfl, ha.len, fun _ _ => rfl, fun _ hi => MpInt.digit_ge_alloc ha hi⟩).symm

theorem MpInt.growTo_shape {a : MpInt} (ha : a.Shape) {n : Nat} (hn : a.alloc ≤ n) (h31 : n < 2 ^ 31) :
    (a.growTo n).Shape :=
  { len := MpInt.ofDigits_len _ _ _ _
    used_le := by show a.used ≤ n; have := ha.used_le; omega
    alloc_lt := h31
    digit_lt := fun i => by rw [MpInt.growTo_digit ha hn]; exact ha.digit_lt i
    high_zero := fun i hi => by rw [MpInt.growTo_digit ha hn]; exact ha.high_zero i hi }

theorem MpInt.growTo_valid {a : MpInt} (ha : a.Valid) {n : Nat} (hn : a.alloc ≤ n) (h31 : n < 2 ^ 31) :
    (a.growTo n).Valid :=
  { MpInt.growTo_shape ha.toShape hn h31 with
    top := fun h => by rw [MpInt.growTo_digit ha.toShape hn]; exact ha.top h
    sign_ok := ha.sign_ok, zero_pos := ha.zero_pos }

/-! ## The grown inputs -/

/-- What `mp_lshd(a, k)` shifts. -/
def lshdIn (a : MpInt) (k : Nat) : MpInt :=
  if a.alloc < a.used + k ∧ 0 < k ∧ 0 < a.used then a.growTo (a.used + k) else a

/-- What `mp_mul_2d(a, b, a)` shifts. -/
def mul2dIn (a : MpInt) (b : Nat) : MpInt :=
  if a.alloc < a.used + b / 28 + 1 then a.growTo (a.used + b / 28 + 1) else a

/-- The destination `mp_mul_d(a, b, c)` writes. -/
def mulDIn (a c : MpInt) : MpInt :=
  if c.alloc < a.used + 1 then c.growTo (a.used + 1) else c

/-- The fields a grown input keeps. -/
structure GrownOf (a A : MpInt) : Prop where
  used : A.used = a.used
  sign : A.sign = a.sign
  digit : A.digit = a.digit
  alloc : a.alloc ≤ A.alloc
  shape : A.Shape

theorem GrownOf.ite {a : MpInt} (ha : a.Shape) {c : Prop} [Decidable c] {n : Nat} (hc : c → a.alloc < n)
    (h31 : n < 2 ^ 31) : GrownOf a (if c then a.growTo n else a) := by
  split
  · rename_i h; have := hc h
    exact ⟨rfl, rfl, MpInt.growTo_digit ha (by omega), Nat.le_of_lt this, MpInt.growTo_shape ha (by omega) h31⟩
  · exact ⟨rfl, rfl, rfl, Nat.le_refl _, ha⟩

/-- A grown input is `a` copied into itself (`mp_copy(a, A)` would leave `A`). -/
theorem GrownOf.copy {a A : MpInt} (h : GrownOf a A) : CopyPost a A A :=
  { alloc := rfl, len := h.shape.len, used := h.used, sign := h.sign
    digit := fun i => by
      by_cases hi : i < a.used
      · rw [if_pos hi, h.digit]
      · rw [if_neg hi, if_neg (by rw [h.used]; exact hi)] }

theorem lshdIn_grown {a : MpInt} (ha : a.Shape) {k : Nat} (h31 : a.used + k < 2 ^ 31) : GrownOf a (lshdIn a k) :=
  GrownOf.ite ha (fun h => h.1) h31

theorem lshdIn_room (a : MpInt) {k : Nat} (hk : 0 < k) (hu : 0 < a.used) :
    (lshdIn a k).used + k ≤ (lshdIn a k).alloc := by
  unfold lshdIn; split
  · simp [MpInt.growTo, MpInt.ofDigits]
  · rename_i h; by_cases h2 : a.alloc < a.used + k
    · exact absurd ⟨h2, hk, hu⟩ h
    · omega

theorem mul2dIn_grown {a : MpInt} (ha : a.Shape) {b : Nat} (h31 : a.used + b / 28 + 1 < 2 ^ 31) :
    GrownOf a (mul2dIn a b) :=
  GrownOf.ite ha id h31

theorem mul2dIn_room (a : MpInt) (b : Nat) : a.used + b / 28 + 1 ≤ (mul2dIn a b).alloc := by
  unfold mul2dIn; split
  · simp [MpInt.growTo, MpInt.ofDigits]
  · omega

theorem mulDIn_grown {a c : MpInt} (hc : c.Shape) (h31 : a.used + 1 < 2 ^ 31) : GrownOf c (mulDIn a c) :=
  GrownOf.ite hc id h31

theorem mulDIn_room (a c : MpInt) : a.used + 1 ≤ (mulDIn a c).alloc := by
  unfold mulDIn; split
  · simp [MpInt.growTo, MpInt.ofDigits]
  · omega

/-! ## `mp_lshd`'s loop -/

/-- The digits after `t` iterations of the copy loop (from the top). -/
def lshdT (a : MpInt) (k t j : Nat) : Nat :=
  if a.used + k - t ≤ j ∧ j < a.used + k then a.digit (j - k) else a.digit j

theorem lshdT_zero (a : MpInt) (k : Nat) : lshdT a k 0 = a.digit :=
  funext fun j => by simp only [lshdT]; rw [if_neg (by omega)]

/-- One iteration: digit `used + k - 1 - t` takes digit `used - 1 - t`. -/
theorem lshdT_step (a : MpInt) (k t : Nat) (ht : t < a.used) :
    Mont.upd (lshdT a k t) (a.used + k - 1 - t) (a.digit (a.used - 1 - t)) = lshdT a k (t + 1) :=
  funext fun j => by
    simp only [Mont.upd, lshdT]
    by_cases hj : j = a.used + k - 1 - t
    · subst hj; rw [if_pos rfl, if_pos (by omega)]; congr 1; omega
    · rw [if_neg hj]
      by_cases hin : a.used + k - t ≤ j ∧ j < a.used + k
      · rw [if_pos hin, if_pos (by omega)]
      · rw [if_neg hin, if_neg (by omega)]

/-- The loop's reads: digit `used - 1 - t` is still `a`'s. -/
theorem lshdT_read (a : MpInt) {k t : Nat} (hk : 0 < k) (ht : t < a.used) :
    lshdT a k t (a.used - 1 - t) = a.digit (a.used - 1 - t) := by
  simp only [lshdT]; rw [if_neg (by omega)]

/-- One iteration as the store leaves it (the stored value read from the current digits). -/
theorem lshdT_succ (a : MpInt) {k t : Nat} (hk : 0 < k) (ht : t < a.used) :
    lshdT a k (t + 1) = Mont.upd (lshdT a k t) (a.used + k - 1 - t) (lshdT a k t (a.used - 1 - t)) := by
  rw [lshdT_read a hk ht, lshdT_step a k t ht]

/-- The last iteration (`t + 1 = used`). -/
theorem lshdT_last (a : MpInt) {k t : Nat} (hk : 0 < k) (ht : t + 1 = a.used) :
    lshdT a k a.used = Mont.upd (lshdT a k t) (a.used + k - 1 - t) (lshdT a k t (a.used - 1 - t)) := by
  have := lshdT_succ a hk (show t < a.used by omega); rwa [ht] at this

theorem lshdT_lt {a : MpInt} (ha : a.Shape) (k t j : Nat) : lshdT a k t j < 268435456 := by
  unfold lshdT; split <;> exact ha.digit_lt _

/-- After the loop and `memset(dp, 0, 4 k)`: `lshdDigits`. -/
theorem lshdT_fill (a : MpInt) (k j : Nat) :
    (if 0 ≤ j ∧ j < k then 0 else lshdT a k a.used j) = lshdDigits a k j := by
  simp only [lshdT, lshdDigits, Nat.zero_le, true_and]
  by_cases h1 : j < k
  · simp [h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : j < a.used + k
    · rw [if_pos ⟨by omega, h2⟩, if_pos h2]
    · rw [if_neg (by omega), if_neg h2]

/-- The struct after the shift: `used + k` digits of `lshdDigits` in the same array. -/
def lshdRes (a : MpInt) (k : Nat) : MpInt := MpInt.ofDigits (a.used + k) a.alloc a.sign (lshdDigits a k)

theorem lshdRes_shift {a : MpInt} (ha : a.Shape) {k : Nat} (hroom : a.used + k ≤ a.alloc) :
    LshdShift a k (lshdRes a k) :=
  { alloc := rfl, len := MpInt.ofDigits_len _ _ _ _, used := rfl, sign := rfl
    digit := fun i => by
      simp only [lshdRes, MpInt.ofDigits_digit]
      split
      · rfl
      · simp only [show ¬ i < k by omega, show ¬ i < a.used + k by omega, ite_false]
        exact (ha.high_zero i (by omega)).symm }

/-! ## `mp_mul_d`'s loop and tail -/

namespace MulDG

/-- Digit `i` as the loop stores it: `(a[i] b + u) & MP_MASK`, `u` the carry into `i`. -/
def g (a : MpInt) (b i : Nat) : Nat := (a.digit i * b + combaW (mulDCol a b) i) % 268435456

theorem carry_succ (a : MpInt) (b i : Nat) :
    (a.digit i * b + combaW (mulDCol a b) i) / 268435456 = combaW (mulDCol a b) (i + 1) := by
  simp only [combaW, mulDCol, radix, Layout.digitBits, Nat.add_comm]

theorem g_lt {a : MpInt} {b i : Nat} (hi : i < a.used) : g a b i = mulDDigit a b i := by
  simp only [g, mulDDigit, if_pos hi, combaD, mulDCol, radix, Layout.digitBits, Nat.add_comm]

theorem carry_lt {a : MpInt} (ha : a.Shape) {b : Nat} (hb : b < radix) (i : Nat) :
    combaW (mulDCol a b) i < 268435456 := mulD_W_lt ha hb i

theorem high {a : MpInt} {b j : Nat} (hj : a.used < j) : mulDDigit a b j = 0 := by
  simp [mulDDigit, show ¬ j < a.used by omega, show j ≠ a.used by omega]

/-- The tail's digits without `memset` (`c->used ≤ a->used + 1`): the last carry at `a->used`,
the loop's digits below, `c`'s old ones above (zero). -/
theorem fill_n {a A : MpInt} (hA : A.Shape) {b : Nat} (hle : A.used ≤ a.used + 1) (j : Nat) :
    mulDDigit a b j = (if j = a.used then combaW (mulDCol a b) a.used else if j < a.used then g a b j else A.digit j) := by
  by_cases h1 : j = a.used
  · subst h1; simp [mulDDigit]
  · rw [if_neg h1]; by_cases h2 : j < a.used
    · rw [if_pos h2, g_lt h2]
    · rw [if_neg h2, high (by omega), hA.high_zero j (by omega)]

/-- With `memset(c->dp + a->used + 1, 0, …)` up to the old `c->used`. -/
theorem fill_m {a A : MpInt} (hA : A.Shape) {b : Nat} (j : Nat) :
    mulDDigit a b j = (if a.used + 1 ≤ j ∧ j < A.used then 0 else
      if j = a.used then combaW (mulDCol a b) a.used else if j < a.used then g a b j else A.digit j) := by
  by_cases h0 : a.used + 1 ≤ j ∧ j < A.used
  · rw [if_pos h0, high (by omega)]
  · rw [if_neg h0]
    by_cases h1 : j = a.used
    · subst h1; simp [mulDDigit]
    · rw [if_neg h1]; by_cases h2 : j < a.used
      · rw [if_pos h2, g_lt h2]
      · rw [if_neg h2, high (by omega), hA.high_zero j (by omega)]

/-- `mp_clamp`'s argument: `c0`'s array with the row's digits, `used := a->used + 1`, `a`'s sign. -/
def res (a : MpInt) (b : Nat) (c0 : MpInt) : MpInt :=
  { c0 with used := a.used + 1, sign := a.sign, digits := (List.range c0.alloc).map (mulDDigit a b) }

theorem res_digit {a c0 : MpInt} {b : Nat} (hroom : a.used + 1 ≤ c0.alloc) : (res a b c0).digit = mulDDigit a b := by
  funext i
  simp only [res, MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < c0.alloc
  · simp [h]
  · simp [h, high (a := a) (b := b) (j := i) (by omega)]

theorem res_shape {a c0 : MpInt} (ha : a.Shape) {b : Nat} (hb : b < radix) (hc : c0.Shape)
    (hroom : a.used + 1 ≤ c0.alloc) : (res a b c0).Shape :=
  { len := by simp [res]
    used_le := hroom
    alloc_lt := hc.alloc_lt
    digit_lt := fun i => by rw [res_digit hroom]; exact mulDDigit_lt ha hb i
    high_zero := fun i hi => by rw [res_digit hroom]; exact high (by simp only [res] at hi; omega) }

/-- **`mp_mul_d`'s result** from `mp_clamp`'s. -/
theorem post {a c0 c4 : MpInt} {b : Nat} (hroom : a.used + 1 ≤ c0.alloc) (hcl : ClampPost (res a b c0) c4) :
    MulDPost a b c0 c4 :=
  { alloc := hcl.alloc
    len := by rw [hcl.digits]; simp [res]
    digit := by rw [hcl.digit, res_digit hroom]
    used := by rw [hcl.used, res_digit hroom]; rfl
    sign := by rw [hcl.sign]; rfl }

end MulDG

end Tom
