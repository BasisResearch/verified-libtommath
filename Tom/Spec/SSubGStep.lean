import Tom.Spec.Grow6Step
import Tom.Spec.Indexed

/-!
# `s_mp_sub(a, b, c)` with growth: the grown destination and the two loops

`sSubIn a b c`: `c` grown to `a->used` when short (`b->used ≤ a->used`). Both loops store
`(a[i] - b[i] - u) & MP_MASK` (the second with `b[i] = 0`) in the machine's literal forms
`(x + 2^28 - y - u) % 2^28`, the borrow is bit 31 of the 32-bit difference
`(x + 2^32 - (y + u)) % 2^32 / 2^31`, and `subBorrowAt a b i` throughout (`borrow1`,
`borrow2`). After `t` digits the array holds `ov a b old t` (`step1`, `step2`); the tail zeroes
up to the old `used` (`fill_n`, `fill_m`) and `mp_clamp` of `res` gives `SSubPost` (`post`).
-/

namespace Tom

open MpInt

/-- The destination `s_mp_sub(a, b, c)` writes. -/
def sSubIn (a c : MpInt) : MpInt :=
  if c.alloc < a.used then c.growTo a.used else c

theorem sSubIn_grown {a c : MpInt} (hc : c.Shape) (h31 : a.used < 2 ^ 31) : GrownOf c (sSubIn a c) :=
  GrownOf.ite hc id h31

theorem sSubIn_room (a c : MpInt) : a.used ≤ (sSubIn a c).alloc := by
  unfold sSubIn; split
  · simp [MpInt.growTo, MpInt.ofDigits]
  · omega

namespace SSubG

/-- Digit `j` as the loops write it. -/
def dig (a b : MpInt) (j : Nat) : Nat := (a.digit j + 268435456 - b.digit j - subBorrowAt a b j) % 268435456

/-- The array after `t` digits. -/
def ov (a b : MpInt) (old : Nat → Nat) (t j : Nat) : Nat := if j < t then dig a b j else old j

theorem ov_zero (a b : MpInt) (old : Nat → Nat) : ov a b old 0 = old := funext fun j => by simp [ov]

theorem ov_self (a b : MpInt) {old : Nat → Nat} {x : MpInt} (h : old = x.digit) (t : Nat) :
    ov a b old t t = x.digit t := by
  subst h; simp [ov]

theorem step1 (a b : MpInt) (old : Nat → Nat) {i x y u : Nat} (hx : x = a.digit i) (hy : y = b.digit i)
    (hu : u = subBorrowAt a b i) :
    ov a b old (i + 1) = Mont.upd (ov a b old i) i ((x + 268435456 - y - u) % 268435456) :=
  funext fun j => by
    subst hx hy hu
    simp only [Mont.upd, ov]
    by_cases hj : j = i
    · subst hj; simp [dig]
    · rw [if_neg hj]; by_cases h2 : j < i
      · rw [if_pos (by omega), if_pos h2]
      · rw [if_neg (by omega), if_neg h2]

theorem step2 (a b : MpInt) (old : Nat → Nat) {i x u : Nat} (hb0 : b.digit i = 0) (hx : x = a.digit i)
    (hu : u = subBorrowAt a b i) :
    ov a b old (i + 1) = Mont.upd (ov a b old i) i ((x + 268435456 - u) % 268435456) :=
  funext fun j => by
    subst hx hu
    simp only [Mont.upd, ov]
    by_cases hj : j = i
    · subst hj; simp [dig, hb0]
    · rw [if_neg hj]; by_cases h2 : j < i
      · rw [if_pos (by omega), if_pos h2]
      · rw [if_neg (by omega), if_neg h2]

theorem borrow1 (a b : MpInt) {i x y u : Nat} (hx : x = a.digit i) (hy : y = b.digit i)
    (hu : u = subBorrowAt a b i) (hxl : x < 268435456) (hyl : y < 268435456) :
    (x + 4294967296 - (y + u)) % 4294967296 / 2147483648 = subBorrowAt a b (i + 1) := by
  have h1 := subBorrowAt_le_one a b i
  rw [subBorrowAt_succ, ← hx, ← hy, ← hu]
  subst hu
  split <;> omega

theorem borrow2 (a b : MpInt) {i x u : Nat} (hb0 : b.digit i = 0) (hx : x = a.digit i)
    (hu : u = subBorrowAt a b i) (hxl : x < 268435456) :
    (x + 4294967296 - u) % 4294967296 / 2147483648 = subBorrowAt a b (i + 1) := by
  have h1 := subBorrowAt_le_one a b i
  rw [subBorrowAt_succ, ← hx, hb0, ← hu]
  subst hu
  split <;> omega

theorem dig_eq {a b : MpInt} (ha : a.Shape) (hb : b.Shape) {j : Nat} (hj : j < a.used) :
    dig a b j = subDigits a b j := by
  rw [subDigits_lt_used ha hb hj]; rfl

/-- The tail without `memset` (`c->used ≤ a->used`). -/
theorem fill_n {a b A : MpInt} (ha : a.Shape) (hb : b.Shape) (hA : A.Shape) (hle : A.used ≤ a.used) (j : Nat) :
    subDigits a b j = ov a b A.digit a.used j := by
  simp only [ov]; split
  · exact (dig_eq ha hb ‹_›).symm
  · rw [subDigits_ge ha b (by omega), hA.high_zero j (by omega)]

/-- With `memset(…, 0, 4 (olduse - a->used))`. -/
theorem fill_m {a b A : MpInt} (ha : a.Shape) (hb : b.Shape) (hA : A.Shape) (j : Nat) :
    subDigits a b j = (if a.used ≤ j ∧ j < A.used then 0 else ov a b A.digit a.used j) := by
  by_cases h0 : a.used ≤ j ∧ j < A.used
  · rw [if_pos h0, subDigits_ge ha b h0.1]
  · rw [if_neg h0]; simp only [ov]; split
    · exact (dig_eq ha hb ‹_›).symm
    · rw [subDigits_ge ha b (by omega), hA.high_zero j (by omega)]

/-- `mp_clamp`'s argument: `c0`'s array with the difference's digits, `used := a->used`. -/
def res (a b c0 : MpInt) : MpInt :=
  { c0 with used := a.used, digits := (List.range c0.alloc).map (subDigits a b) }

theorem res_digit {a b c0 : MpInt} (ha : a.Shape) (hroom : a.used ≤ c0.alloc) : (res a b c0).digit = subDigits a b := by
  funext i
  simp only [res, MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < c0.alloc
  · simp [h]
  · simp [h, subDigits_ge ha b (i := i) (by omega)]

theorem res_shape {a b c0 : MpInt} (ha : a.Shape) (hc : c0.Shape) (hroom : a.used ≤ c0.alloc) :
    (res a b c0).Shape :=
  { len := by simp [res]
    used_le := hroom
    alloc_lt := hc.alloc_lt
    digit_lt := fun i => by rw [res_digit ha hroom]; exact subDigits_lt a b i
    high_zero := fun i hi => by rw [res_digit ha hroom]; exact subDigits_ge ha b (by simp only [res] at hi; omega) }

/-- **`s_mp_sub`'s result** from `mp_clamp`'s. -/
theorem post {a b c0 c4 : MpInt} (ha : a.Shape) (hroom : a.used ≤ c0.alloc) (hcl : ClampPost (res a b c0) c4) :
    SSubPost a b c0 c4 :=
  { alloc := hcl.alloc
    len := by rw [hcl.digits]; simp [res]
    digit := by rw [hcl.digit, res_digit ha hroom]
    used := by rw [hcl.used, res_digit ha hroom]; rfl
    sign := by rw [hcl.sign]; rfl }

end SSubG

end Tom
