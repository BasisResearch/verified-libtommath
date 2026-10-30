import Tom.Spec.Sub

/-!
# The digit models by index

The RV64I and C implementations of `s_mp_add` and `s_mp_sub` compute digit
`i` from `a->dp[i]`, `b->dp[i]` and a running carry (borrow), while the
contracts (`SAddPost.digit`, `SSubPost.digit`) state the digits as the list
models `addDigits`, `subDigits`. This file gives the models in that indexed
form.

* `addCarryAt a b i`: the carry into position `i` of `s_mp_add`;
  `addDigits a b i` is `(a[i] + b[i] + carry i) % radix` below
  `max(used)`, the final carry at `max(used)`, and zero above.
* `subBorrowAt a b i`: the borrow into position `i` of `s_mp_sub`;
  `subDigits a b i` is `(a[i] + radix - b[i] - borrow i) % radix` below
  `a->used`, and zero from there on.

Both read both operands' digits at every position. For a shaped `mp_int`,
`dp[i] = 0` from `used` on (`Shape.high_zero`), so this covers the C's
second loops (`x->dp[i] + u`, `a->dp[i] - u`) too. The carry (borrow) into
`i` depends only on the digits below `i` (`addCarryAt_congr`,
`subBorrowAt_congr`), which is what a loop invariant needs.
-/

namespace Tom

open MpInt

/-! ## Digit functions of lists -/

/-- Digit `i` of a digit list, `0` past its end. -/
def listDigit (ds : List Nat) (i : Nat) : Nat := ds.getD i 0

@[simp] theorem listDigit_nil (i : Nat) : listDigit [] i = 0 := rfl

@[simp] theorem listDigit_cons_zero (d : Nat) (ds : List Nat) : listDigit (d :: ds) 0 = d := by
  simp [listDigit]

@[simp] theorem listDigit_cons_succ (d : Nat) (ds : List Nat) (i : Nat) :
    listDigit (d :: ds) (i + 1) = listDigit ds i := by
  simp [listDigit]

theorem listDigit_headD (ds : List Nat) : ds.headD 0 = listDigit ds 0 := by
  cases ds <;> simp

theorem listDigit_tail (ds : List Nat) (i : Nat) : listDigit ds.tail i = listDigit ds (i + 1) := by
  cases ds <;> simp

/-- The used digits of a shaped `mp_int`, read by index, are its digits. -/
theorem MpInt.Shape.listDigit_take {a : MpInt} (ha : a.Shape) :
    listDigit (a.digits.take a.used) = a.digit := by
  funext i
  by_cases h : i < a.used
  · simp [listDigit, MpInt.digit, List.getD_eq_getElem?_getD, h]
  · rw [ha.high_zero i (by omega)]
    simp [listDigit, List.getD_eq_getElem?_getD, List.getElem?_take, h]

theorem MpInt.Shape.length_take {a : MpInt} (ha : a.Shape) : (a.digits.take a.used).length = a.used := by
  rw [List.length_take, ha.len, Nat.min_eq_left ha.used_le]

/-! ## Carry and borrow chains on digit functions -/

/-- The carry into position `i` of a digit-by-digit addition of `dx` and
`dy` with carry-in `u`. -/
def carryChain (dx dy : Nat → Nat) (u : Nat) : Nat → Nat
  | 0 => u
  | i + 1 => (dx i + dy i + carryChain dx dy u i) / radix

/-- The borrow into position `i` of a digit-by-digit subtraction of `dy`
from `dx` with borrow-in `u`. -/
def borrowChain (dx dy : Nat → Nat) (u : Nat) : Nat → Nat
  | 0 => u
  | i + 1 => if dx i < dy i + borrowChain dx dy u i then 1 else 0

/-- Dropping the lowest digit: the chain from position `1` is the chain of
the shifted digits with the first carry as carry-in. -/
theorem carryChain_shift (dx dy dx' dy' : Nat → Nat) (u : Nat)
    (hx : ∀ j, dx' j = dx (j + 1)) (hy : ∀ j, dy' j = dy (j + 1)) :
    ∀ i, carryChain dx dy u (i + 1) = carryChain dx' dy' ((dx 0 + dy 0 + u) / radix) i
  | 0 => rfl
  | i + 1 => by
    show (dx (i + 1) + dy (i + 1) + carryChain dx dy u (i + 1)) / radix =
      (dx' i + dy' i + carryChain dx' dy' _ i) / radix
    rw [carryChain_shift dx dy dx' dy' u hx hy i, hx, hy]

theorem borrowChain_shift (dx dy dx' dy' : Nat → Nat) (u : Nat)
    (hx : ∀ j, dx' j = dx (j + 1)) (hy : ∀ j, dy' j = dy (j + 1)) :
    ∀ i, borrowChain dx dy u (i + 1) =
      borrowChain dx' dy' (if dx 0 < dy 0 + u then 1 else 0) i
  | 0 => rfl
  | i + 1 => by
    show (if dx (i + 1) < dy (i + 1) + borrowChain dx dy u (i + 1) then 1 else 0) =
      (if dx' i < dy' i + borrowChain dx' dy' _ i then 1 else 0)
    rw [borrowChain_shift dx dy dx' dy' u hx hy i, hx, hy]

/-- The carry into `i` depends only on the digits below `i`. -/
theorem carryChain_congr {dx dy ex ey : Nat → Nat} (u : Nat) :
    ∀ i, (∀ j, j < i → dx j = ex j) → (∀ j, j < i → dy j = ey j) →
      carryChain dx dy u i = carryChain ex ey u i
  | 0, _, _ => rfl
  | i + 1, hx, hy => by
    simp only [carryChain, hx i (Nat.lt_succ_self i), hy i (Nat.lt_succ_self i),
      carryChain_congr u i (fun j hj => hx j (Nat.lt_succ_of_lt hj))
        (fun j hj => hy j (Nat.lt_succ_of_lt hj))]

/-- The borrow into `i` depends only on the digits below `i`. -/
theorem borrowChain_congr {dx dy ex ey : Nat → Nat} (u : Nat) :
    ∀ i, (∀ j, j < i → dx j = ex j) → (∀ j, j < i → dy j = ey j) →
      borrowChain dx dy u i = borrowChain ex ey u i
  | 0, _, _ => rfl
  | i + 1, hx, hy => by
    simp only [borrowChain, hx i (Nat.lt_succ_self i), hy i (Nat.lt_succ_self i),
      borrowChain_congr u i (fun j hj => hx j (Nat.lt_succ_of_lt hj))
        (fun j hj => hy j (Nat.lt_succ_of_lt hj))]

/-- With digits below the radix and carry-in at most one, every carry is at
most one. -/
theorem carryChain_le_one {dx dy : Nat → Nat} {u : Nat} (hx : ∀ i, dx i < radix)
    (hy : ∀ i, dy i < radix) (hu : u ≤ 1) : ∀ i, carryChain dx dy u i ≤ 1
  | 0 => hu
  | i + 1 => by
    have ih := carryChain_le_one hx hy hu i
    have := hx i
    have := hy i
    show (dx i + dy i + carryChain dx dy u i) / radix ≤ 1
    exact (Nat.div_le_iff_le_mul_add_pred radix_pos).2 (by omega)

theorem borrowChain_le_one {dx dy : Nat → Nat} {u : Nat} (hu : u ≤ 1) :
    ∀ i, borrowChain dx dy u i ≤ 1
  | 0 => hu
  | _ + 1 => by simp only [borrowChain]; split <;> omega

/-! ## The list models by index -/

/-- `addCarry` by index: digit `i` below the longer length is the digit
sum with the carry into `i`, digit `max` is the final carry, and there are
no digits above. -/
theorem addCarry_getD : ∀ (xs ys : List Nat) (u i : Nat),
    (addCarry xs ys u).getD i 0 =
      if i < max xs.length ys.length then
        (listDigit xs i + listDigit ys i + carryChain (listDigit xs) (listDigit ys) u i) % radix
      else if i = max xs.length ys.length then carryChain (listDigit xs) (listDigit ys) u i
      else 0
  | [], [], u, 0 => by simp [addCarry, carryChain]
  | [], [], u, i + 1 => by simp [addCarry]
  | x :: xs, [], u, 0 => by simp [addCarry, carryChain]
  | [], y :: ys, u, 0 => by simp [addCarry, carryChain]
  | x :: xs, y :: ys, u, 0 => by simp [addCarry, carryChain]
  | x :: xs, [], u, i + 1 => by
    rw [carryChain_shift (listDigit (x :: xs)) (listDigit []) (listDigit xs) (listDigit []) u
      (fun _ => by simp) (fun _ => by simp) i]
    simp only [addCarry, List.getD_cons_succ, addCarry_getD xs [] _ i, listDigit_cons_zero,
      listDigit_cons_succ, listDigit_nil, Nat.add_zero, List.length_cons, List.length_nil]
    repeat' split
    all_goals first | with_reducible rfl | omega
  | [], y :: ys, u, i + 1 => by
    rw [carryChain_shift (listDigit []) (listDigit (y :: ys)) (listDigit []) (listDigit ys) u
      (fun _ => by simp) (fun _ => by simp) i]
    simp only [addCarry, List.getD_cons_succ, addCarry_getD [] ys _ i, listDigit_cons_zero,
      listDigit_cons_succ, listDigit_nil, Nat.zero_add, List.length_cons, List.length_nil]
    repeat' split
    all_goals first | with_reducible rfl | omega
  | x :: xs, y :: ys, u, i + 1 => by
    rw [carryChain_shift (listDigit (x :: xs)) (listDigit (y :: ys)) (listDigit xs) (listDigit ys) u
      (fun _ => by simp) (fun _ => by simp) i]
    simp only [addCarry, List.getD_cons_succ, addCarry_getD xs ys _ i, listDigit_cons_zero,
      listDigit_cons_succ, List.length_cons]
    repeat' split
    all_goals first | with_reducible rfl | omega

/-- `subBorrow` by index: digit `i` below the minuend's length is the digit
difference with the borrow into `i`. The subtrahend is read as `0` past its
end. (From the minuend's length on there are no digits: `length_subBorrow`.) -/
theorem subBorrow_getD : ∀ (xs ys : List Nat) (u i : Nat), i < xs.length →
    (subBorrow xs ys u).getD i 0 =
      (listDigit xs i + radix - listDigit ys i - borrowChain (listDigit xs) (listDigit ys) u i) % radix
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | x :: xs, ys, u, 0, _ => by
    rw [subBorrow, List.getD_cons_zero, listDigit_cons_zero, listDigit_headD]
    rfl
  | x :: xs, ys, u, i + 1, h => by
    rw [subBorrow, List.getD_cons_succ,
      subBorrow_getD xs ys.tail _ i (by rw [List.length_cons] at h; omega),
      borrowChain_shift (listDigit (x :: xs)) (listDigit ys) (listDigit xs) (listDigit ys.tail) u
        (fun _ => by simp) (fun j => listDigit_tail ys j) i,
      listDigit_cons_succ, listDigit_cons_zero, listDigit_tail, listDigit_headD]

/-! ## `s_mp_add` by index -/

/-- The carry into position `i` of `s_mp_add(a, b, c)`. -/
def addCarryAt (a b : MpInt) : Nat → Nat := carryChain a.digit b.digit 0

@[simp] theorem addCarryAt_zero (a b : MpInt) : addCarryAt a b 0 = 0 := rfl

theorem addCarryAt_succ (a b : MpInt) (i : Nat) :
    addCarryAt a b (i + 1) = (a.digit i + b.digit i + addCarryAt a b i) / radix := rfl

/-- Below `max(used)`: the digit sum with the carry, modulo the radix (both
loops of `s_mp_add`; past `x->used` the shorter operand's digit is `0`). -/
theorem addDigits_lt_max {a b : MpInt} (ha : a.Shape) (hb : b.Shape) {i : Nat}
    (hi : i < max a.used b.used) :
    addDigits a b i = (a.digit i + b.digit i + addCarryAt a b i) % radix := by
  unfold addDigits
  rw [addCarry_getD, ha.length_take, hb.length_take, ha.listDigit_take, hb.listDigit_take,
    ite_eq_left hi]
  rfl

/-- At `max(used)`: the final carry digit. -/
theorem addDigits_max {a b : MpInt} (ha : a.Shape) (hb : b.Shape) :
    addDigits a b (max a.used b.used) = addCarryAt a b (max a.used b.used) := by
  unfold addDigits
  rw [addCarry_getD, ha.length_take, hb.length_take, ha.listDigit_take, hb.listDigit_take,
    ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl]
  rfl

/-- Above `max(used)`: zero. -/
theorem addDigits_gt {a b : MpInt} (ha : a.Shape) (hb : b.Shape) {i : Nat}
    (hi : max a.used b.used < i) : addDigits a b i = 0 :=
  addDigits_high ha hb i hi

/-- Every carry of `s_mp_add` is at most one. -/
theorem addCarryAt_le_one {a b : MpInt} (ha : a.Shape) (hb : b.Shape) (i : Nat) :
    addCarryAt a b i ≤ 1 :=
  carryChain_le_one ha.digit_lt hb.digit_lt (Nat.zero_le 1) i

/-- The carry into `i` depends only on the digits below `i`. -/
theorem addCarryAt_congr {a b a' b' : MpInt} {i : Nat}
    (ha : ∀ j, j < i → a.digit j = a'.digit j) (hb : ∀ j, j < i → b.digit j = b'.digit j) :
    addCarryAt a b i = addCarryAt a' b' i :=
  carryChain_congr 0 i ha hb

/-- Digit `i` below `max(used)` depends only on the digits up to `i`. -/
theorem addDigits_congr {a b a' b' : MpInt} (ha : a.Shape) (hb : b.Shape) (ha' : a'.Shape)
    (hb' : b'.Shape) {i : Nat} (hi : i < max a.used b.used) (hi' : i < max a'.used b'.used)
    (hda : ∀ j, j ≤ i → a.digit j = a'.digit j) (hdb : ∀ j, j ≤ i → b.digit j = b'.digit j) :
    addDigits a b i = addDigits a' b' i := by
  rw [addDigits_lt_max ha hb hi, addDigits_lt_max ha' hb' hi', hda i (Nat.le_refl i),
    hdb i (Nat.le_refl i),
    addCarryAt_congr (fun j hj => hda j (Nat.le_of_lt hj)) (fun j hj => hdb j (Nat.le_of_lt hj))]

/-! ## `s_mp_sub` by index -/

/-- The borrow into position `i` of `s_mp_sub(a, b, c)`. -/
def subBorrowAt (a b : MpInt) : Nat → Nat := borrowChain a.digit b.digit 0

@[simp] theorem subBorrowAt_zero (a b : MpInt) : subBorrowAt a b 0 = 0 := rfl

theorem subBorrowAt_succ (a b : MpInt) (i : Nat) :
    subBorrowAt a b (i + 1) = if a.digit i < b.digit i + subBorrowAt a b i then 1 else 0 := rfl

/-- Below `a->used`: the digit difference with the borrow, modulo the radix
(both loops of `s_mp_sub`; past `b->used`, `b`'s digit is `0`). The model
reads `b` only through its used digits, so `b->used ≤ a->used` is not
needed here. -/
theorem subDigits_lt_used {a b : MpInt} (ha : a.Shape) (hb : b.Shape) {i : Nat}
    (hi : i < a.used) :
    subDigits a b i = (a.digit i + radix - b.digit i - subBorrowAt a b i) % radix := by
  unfold subDigits
  rw [subBorrow_getD _ _ _ _ (by rw [ha.length_take]; exact hi), ha.listDigit_take,
    hb.listDigit_take]
  rfl

/-- From `a->used` on: zero. -/
theorem subDigits_ge {a : MpInt} (ha : a.Shape) (b : MpInt) {i : Nat} (hi : a.used ≤ i) :
    subDigits a b i = 0 :=
  subDigits_high ha b i hi

/-- Every borrow of `s_mp_sub` is at most one. -/
theorem subBorrowAt_le_one (a b : MpInt) (i : Nat) : subBorrowAt a b i ≤ 1 :=
  borrowChain_le_one (Nat.zero_le 1) i

/-- The borrow into `i` depends only on the digits below `i`. -/
theorem subBorrowAt_congr {a b a' b' : MpInt} {i : Nat}
    (ha : ∀ j, j < i → a.digit j = a'.digit j) (hb : ∀ j, j < i → b.digit j = b'.digit j) :
    subBorrowAt a b i = subBorrowAt a' b' i :=
  borrowChain_congr 0 i ha hb

/-- Digit `i` below `a->used` depends only on the digits up to `i`. -/
theorem subDigits_congr {a b a' b' : MpInt} (ha : a.Shape) (hb : b.Shape) (ha' : a'.Shape)
    (hb' : b'.Shape) {i : Nat} (hi : i < a.used) (hi' : i < a'.used)
    (hda : ∀ j, j ≤ i → a.digit j = a'.digit j) (hdb : ∀ j, j ≤ i → b.digit j = b'.digit j) :
    subDigits a b i = subDigits a' b' i := by
  rw [subDigits_lt_used ha hb hi, subDigits_lt_used ha' hb' hi', hda i (Nat.le_refl i),
    hdb i (Nat.le_refl i),
    subBorrowAt_congr (fun j hj => hda j (Nat.le_of_lt hj)) (fun j hj => hdb j (Nat.le_of_lt hj))]

end Tom
