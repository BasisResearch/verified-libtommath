import Tom.Spec.Grow6Step
import Tom.Spec.Indexed

/-!
# `s_mp_add(a, b, c)` with growth: the grown destination and the two loops

`sAddIn a b c`: `c` grown to `max(used) + 1` when short. The first loop (`i < min`) stores
`(b[i] + a[i] + u) & MP_MASK`, the second (`min ≤ i < max`) `(x[i] + u) & MP_MASK` with `x` the
longer operand; the carry `u` is `addCarryAt a b i` throughout (`carry1`, `carry2`). After `t`
digits the array holds `ov a b n X old t` (`step1`, `step2`: one store each, in the machine's
literal form `Mont.upd`); the tail stores the last carry at `max` and zeroes up to the old
`used` (`fill_n`, `fill_m`), and `mp_clamp` of `res` gives `SAddPost` (`post`).
-/

namespace Tom

open MpInt

/-- The destination `s_mp_add(a, b, c)` writes. -/
def sAddIn (a b c : MpInt) : MpInt :=
  if c.alloc < max a.used b.used + 1 then c.growTo (max a.used b.used + 1) else c

theorem sAddIn_grown {a b c : MpInt} (hc : c.Shape) (h31 : max a.used b.used + 1 < 2 ^ 31) :
    GrownOf c (sAddIn a b c) :=
  GrownOf.ite hc id h31

theorem sAddIn_room (a b c : MpInt) : max a.used b.used + 1 ≤ (sAddIn a b c).alloc := by
  unfold sAddIn; split
  · simp [MpInt.growTo, MpInt.ofDigits]
  · omega

namespace SAddG

/-- The first loop's digit. -/
def g1 (a b : MpInt) (j : Nat) : Nat := (b.digit j + a.digit j + addCarryAt a b j) % 268435456

/-- The second loop's digit (`X` the longer operand). -/
def g2 (a b X : MpInt) (j : Nat) : Nat := (X.digit j + addCarryAt a b j) % 268435456

/-- Digit `j` as the loops write it (`n = min`). -/
def dig (a b : MpInt) (n : Nat) (X : MpInt) (j : Nat) : Nat := if j < n then g1 a b j else g2 a b X j

/-- The array after `t` digits: the loops' digits below `t`, `old` above. -/
def ov (a b : MpInt) (n : Nat) (X : MpInt) (old : Nat → Nat) (t j : Nat) : Nat :=
  if j < t then dig a b n X j else old j

/-- The current digit of an operand that is the destination: still its own. -/
theorem ov_self (a b : MpInt) (n : Nat) (X : MpInt) {old : Nat → Nat} {x : MpInt} (h : old = x.digit) (t : Nat) :
    ov a b n X old t t = x.digit t := by
  subst h; simp [ov]

theorem ov_zero (a b : MpInt) (n : Nat) (X : MpInt) (old : Nat → Nat) : ov a b n X old 0 = old :=
  funext fun j => by simp [ov]

theorem carry1 (a b : MpInt) {i ya yb : Nat} (hya : ya = a.digit i) (hyb : yb = b.digit i) :
    (yb + ya + addCarryAt a b i) / 268435456 = addCarryAt a b (i + 1) := by
  subst hya hyb; rw [addCarryAt_succ, Nat.add_comm (b.digit i)]; rfl

theorem carry2 (a b X : MpInt) {i yx : Nat} (hyx : yx = X.digit i) (hX : a.digit i + b.digit i = X.digit i) :
    (yx + addCarryAt a b i) / 268435456 = addCarryAt a b (i + 1) := by
  subst hyx; rw [addCarryAt_succ, hX]; rfl

theorem step1 (a b : MpInt) (n : Nat) (X : MpInt) (old : Nat → Nat) {i ya yb u : Nat} (hi : i < n)
    (hya : ya = a.digit i) (hyb : yb = b.digit i) (hu : u = addCarryAt a b i) :
    ov a b n X old (i + 1) = Mont.upd (ov a b n X old i) i ((yb + ya + u) % 268435456) :=
  funext fun j => by
    subst hya hyb hu
    simp only [Mont.upd, ov, dig]
    by_cases hj : j = i
    · subst hj; simp [hi, g1]
    · rw [if_neg hj]; by_cases h2 : j < i
      · rw [if_pos (by omega), if_pos h2]
      · rw [if_neg (by omega), if_neg h2]

theorem step2 (a b : MpInt) (n : Nat) (X : MpInt) (old : Nat → Nat) {i yx u : Nat} (hi : n ≤ i)
    (hyx : yx = X.digit i) (hu : u = addCarryAt a b i) :
    ov a b n X old (i + 1) = Mont.upd (ov a b n X old i) i ((yx + u) % 268435456) :=
  funext fun j => by
    subst hyx hu
    simp only [Mont.upd, ov, dig]
    by_cases hj : j = i
    · subst hj; simp [show ¬ j < n by omega, g2]
    · rw [if_neg hj]; by_cases h2 : j < i
      · rw [if_pos (by omega), if_pos h2]
      · rw [if_neg (by omega), if_neg h2]

/-- What the loops leave below `max` is the sum's digits. -/
theorem dig_eq {a b : MpInt} (ha : a.Shape) (hb : b.Shape) {n : Nat} {X : MpInt}
    (hX : ∀ j, n ≤ j → a.digit j + b.digit j = X.digit j) {j : Nat} (hj : j < max a.used b.used) :
    dig a b n X j = addDigits a b j := by
  rw [addDigits_lt_max ha hb hj]
  simp only [dig, g1, g2, radix, Layout.digitBits]
  split
  · rw [Nat.add_comm (b.digit j)]
  · rw [← hX j (by omega)]

/-- The tail without `memset` (`c->used ≤ max + 1`). -/
theorem fill_n {a b A : MpInt} (ha : a.Shape) (hb : b.Shape) (hA : A.Shape) {n mx : Nat} {X : MpInt}
    (hX : ∀ j, n ≤ j → a.digit j + b.digit j = X.digit j) (hmx : mx = max a.used b.used)
    (hle : A.used ≤ mx + 1) (j : Nat) :
    addDigits a b j = (if j = mx then addCarryAt a b mx else ov a b n X A.digit mx j) := by
  subst hmx
  by_cases h1 : j = max a.used b.used
  · subst h1; rw [if_pos rfl, addDigits_max ha hb]
  · rw [if_neg h1]; simp only [ov]
    by_cases h2 : j < max a.used b.used
    · rw [if_pos h2, dig_eq ha hb hX h2]
    · rw [if_neg h2, addDigits_gt ha hb (by omega), hA.high_zero j (by omega)]

/-- The tail with `memset(…, 0, 4 (olduse - max - 1))`. -/
theorem fill_m {a b A : MpInt} (ha : a.Shape) (hb : b.Shape) (hA : A.Shape) {n mx : Nat} {X : MpInt}
    (hX : ∀ j, n ≤ j → a.digit j + b.digit j = X.digit j) (hmx : mx = max a.used b.used) (j : Nat) :
    addDigits a b j = (if mx + 1 ≤ j ∧ j < A.used then 0 else
      if j = mx then addCarryAt a b mx else ov a b n X A.digit mx j) := by
  by_cases h0 : mx + 1 ≤ j ∧ j < A.used
  · rw [if_pos h0, addDigits_gt ha hb (by omega)]
  · rw [if_neg h0]
    subst hmx
    by_cases h1 : j = max a.used b.used
    · subst h1; rw [if_pos rfl, addDigits_max ha hb]
    · rw [if_neg h1]; simp only [ov]
      by_cases h2 : j < max a.used b.used
      · rw [if_pos h2, dig_eq ha hb hX h2]
      · rw [if_neg h2, addDigits_gt ha hb (by omega), hA.high_zero j (by omega)]

/-- `mp_clamp`'s argument: `c0`'s array with the sum's digits, `used := mx + 1` (`mx = max`). -/
def res (a b c0 : MpInt) (mx : Nat) : MpInt :=
  { c0 with used := mx + 1, digits := (List.range c0.alloc).map (addDigits a b) }

theorem res_digit {a b c0 : MpInt} (ha : a.Shape) (hb : b.Shape) {mx : Nat} (hmx : mx = max a.used b.used)
    (hroom : mx + 1 ≤ c0.alloc) : (res a b c0 mx).digit = addDigits a b := by
  subst hmx
  funext i
  simp only [res, MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < c0.alloc
  · simp [h]
  · simp [h, addDigits_gt ha hb (i := i) (by omega)]

theorem res_shape {a b c0 : MpInt} (ha : a.Shape) (hb : b.Shape) (hc : c0.Shape) {mx : Nat}
    (hmx : mx = max a.used b.used) (hroom : mx + 1 ≤ c0.alloc) : (res a b c0 mx).Shape :=
  { len := by simp [res]
    used_le := hroom
    alloc_lt := hc.alloc_lt
    digit_lt := fun i => by rw [res_digit ha hb hmx hroom]; exact addDigits_lt ha hb i
    high_zero := fun i hi => by
      rw [res_digit ha hb hmx hroom]; exact addDigits_gt ha hb (by simp only [res] at hi; omega) }

/-- **`s_mp_add`'s result** from `mp_clamp`'s. -/
theorem post {a b c0 c4 : MpInt} (ha : a.Shape) (hb : b.Shape) {mx : Nat} (hmx : mx = max a.used b.used)
    (hroom : mx + 1 ≤ c0.alloc) (hcl : ClampPost (res a b c0 mx) c4) : SAddPost a b c0 c4 :=
  { alloc := hcl.alloc
    len := by rw [hcl.digits]; simp [res]
    digit := by rw [hcl.digit, res_digit ha hb hmx hroom]
    used := by rw [hcl.used, res_digit ha hb hmx hroom]; subst hmx; rfl
    sign := by rw [hcl.sign]; rfl }

/-- Past the shorter operand its digits are zero: the longer one's are the sum's inputs. -/
theorem longer_b {a b : MpInt} (ha : a.Shape) :
    ∀ j, a.used ≤ j → a.digit j + b.digit j = b.digit j := fun j hj => by
  rw [ha.high_zero j hj, Nat.zero_add]

theorem longer_a {a b : MpInt} (hb : b.Shape) :
    ∀ j, b.used ≤ j → a.digit j + b.digit j = a.digit j := fun j hj => by
  rw [hb.high_zero j hj, Nat.add_zero]

end SAddG

end Tom
