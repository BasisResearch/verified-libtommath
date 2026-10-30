import Tom.Spec.MpInt

/-!
# Digit-level models of libtommath's algorithms

Each model is the C routine's digit loop as a function on digit lists, with
the C's `mp_digit` arithmetic replaced by `% radix` and `/ radix` (the
implementations show the two agree when the digits are below the radix). The
models are proved against `Nat` here once; the RV64I proofs (`Tom.Machine`)
and, later, the C proofs (Phase 3) show that the code computes the model.

* `addCarry`: the two loops of `s_mp_add` plus the final carry digit.
* `clampUsed`: `mp_clamp`'s `used` after the loop.
* `cmpTop`, `cmpMag`: `mp_cmp_mag`.
-/

namespace Tom

/-! ## `natOf` -/

theorem natOf_nil : natOf [] = 0 := rfl

theorem natOf_cons (d : Nat) (ds : List Nat) : natOf (d :: ds) = d + radix * natOf ds := rfl

theorem radix_pos : 0 < radix := Nat.two_pow_pos _

theorem natOf_append (xs ys : List Nat) :
    natOf (xs ++ ys) = natOf xs + radix ^ xs.length * natOf ys := by
  induction xs with
  | nil => simp [natOf]
  | cons x xs ih =>
    simp only [List.cons_append, natOf_cons, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm radix (radix ^ xs.length)]
    omega

/-- Trailing zero digits do not change the value. -/
theorem natOf_append_zeros (xs : List Nat) (n : Nat) :
    natOf (xs ++ List.replicate n 0) = natOf xs := by
  rw [natOf_append]
  suffices h : natOf (List.replicate n 0) = 0 by rw [h, Nat.mul_zero, Nat.add_zero]
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, natOf_cons, ih]

/-- A list of `n` digits below the radix has value below `radix ^ n`. -/
theorem natOf_lt (ds : List Nat) (h : ∀ d ∈ ds, d < radix) :
    natOf ds < radix ^ ds.length := by
  induction ds with
  | nil => simp [natOf]
  | cons d ds ih =>
    have hd := h d (List.mem_cons_self ..)
    have ih := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [natOf_cons, List.length_cons, Nat.pow_succ]
    have : radix * natOf ds + radix ≤ radix * radix ^ ds.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    rw [Nat.mul_comm (radix ^ ds.length)]; omega

/-! ## `s_mp_add`: digit sums with carry -/

/-- The digit loop of `s_mp_add` on the used digits of its two operands,
then the carry digit. -/
def addCarry : List Nat → List Nat → Nat → List Nat
  | [], [], u => [u]
  | x :: xs, [], u => (x + u) % radix :: addCarry xs [] ((x + u) / radix)
  | [], y :: ys, u => (y + u) % radix :: addCarry [] ys ((y + u) / radix)
  | x :: xs, y :: ys, u => (x + y + u) % radix :: addCarry xs ys ((x + y + u) / radix)

theorem natOf_addCarry : ∀ (xs ys : List Nat) (u : Nat),
    natOf (addCarry xs ys u) = natOf xs + natOf ys + u
  | [], [], u => by simp [addCarry, natOf]
  | x :: xs, [], u => by
    simp only [addCarry, natOf_cons, natOf_addCarry xs [] _, natOf_nil]
    have := Nat.mod_add_div (x + u) radix
    rw [Nat.mul_add, Nat.mul_add]; omega
  | [], y :: ys, u => by
    simp only [addCarry, natOf_cons, natOf_addCarry [] ys _, natOf_nil]
    have := Nat.mod_add_div (y + u) radix
    rw [Nat.mul_add, Nat.mul_add]; omega
  | x :: xs, y :: ys, u => by
    simp only [addCarry, natOf_cons, natOf_addCarry xs ys _]
    have := Nat.mod_add_div (x + y + u) radix
    rw [Nat.mul_add, Nat.mul_add]; omega

theorem length_addCarry : ∀ (xs ys : List Nat) (u : Nat),
    (addCarry xs ys u).length = max xs.length ys.length + 1
  | [], [], _ => by simp [addCarry]
  | _ :: xs, [], _ => by simp [addCarry, length_addCarry xs []]
  | [], _ :: ys, _ => by simp [addCarry, length_addCarry [] ys]
  | _ :: xs, _ :: ys, _ => by
    simp [addCarry, length_addCarry xs ys, Nat.succ_max_succ]

/-- With digits below the radix and a carry of at most one, every carry is
at most one, so every digit (including the last) is below the radix. -/
theorem addCarry_lt : ∀ (xs ys : List Nat) (u : Nat),
    (∀ d ∈ xs, d < radix) → (∀ d ∈ ys, d < radix) → u ≤ 1 →
    ∀ d ∈ addCarry xs ys u, d < radix
  | [], [], u, _, _, hu => by
    have : 1 < radix := by decide
    simp only [addCarry, List.mem_singleton]; omega
  | x :: xs, [], u, hx, hy, hu => by
    have hx0 := hx x (List.mem_cons_self ..)
    intro d hd
    simp only [addCarry, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt _ radix_pos
    · refine addCarry_lt xs [] _ (fun d h => hx d (List.mem_cons_of_mem _ h)) hy ?_ d hd
      exact (Nat.div_le_iff_le_mul_add_pred radix_pos).2 (by omega)
  | [], y :: ys, u, hx, hy, hu => by
    have hy0 := hy y (List.mem_cons_self ..)
    intro d hd
    simp only [addCarry, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt _ radix_pos
    · refine addCarry_lt [] ys _ hx (fun d h => hy d (List.mem_cons_of_mem _ h)) ?_ d hd
      exact (Nat.div_le_iff_le_mul_add_pred radix_pos).2 (by omega)
  | x :: xs, y :: ys, u, hx, hy, hu => by
    have hx0 := hx x (List.mem_cons_self ..)
    have hy0 := hy y (List.mem_cons_self ..)
    intro d hd
    simp only [addCarry, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt _ radix_pos
    · refine addCarry_lt xs ys _ (fun d h => hx d (List.mem_cons_of_mem _ h))
        (fun d h => hy d (List.mem_cons_of_mem _ h)) ?_ d hd
      exact (Nat.div_le_iff_le_mul_add_pred radix_pos).2 (by omega)

/-! ## `mp_clamp` -/

/-- `used` after `mp_clamp`'s loop: strip zero digits from the top. -/
def clampUsed (dig : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if dig n = 0 then clampUsed dig n else n + 1

theorem clampUsed_le (dig : Nat → Nat) : ∀ n, clampUsed dig n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    simp only [clampUsed]; split
    · exact Nat.le_succ_of_le (clampUsed_le dig n)
    · exact Nat.le_refl _

/-- The top digit after clamping is nonzero. -/
theorem clampUsed_top (dig : Nat → Nat) : ∀ n, 0 < clampUsed dig n → dig (clampUsed dig n - 1) ≠ 0
  | 0 => fun h => absurd h (Nat.lt_irrefl 0)
  | n + 1 => by
    simp only [clampUsed]; split
    · exact clampUsed_top dig n
    · intro _; simpa

/-- The digits clamping strips are zero. -/
theorem clampUsed_zero (dig : Nat → Nat) : ∀ n i, clampUsed dig n ≤ i → i < n → dig i = 0
  | 0 => fun _ _ h => absurd h (Nat.not_lt_zero _)
  | n + 1 => by
    intro i hi hn
    simp only [clampUsed] at hi; split at hi
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hn with h | rfl
      · exact clampUsed_zero dig n i hi h
      · assumption
    · omega

/-- `clampUsed` is the `u` with zero digits from `u` to `n` and a nonzero
digit below it (or `u = 0`). -/
theorem clampUsed_eq (dig : Nat → Nat) (u : Nat) (ht : u = 0 ∨ dig (u - 1) ≠ 0) :
    ∀ n, u ≤ n → (∀ i, u ≤ i → i < n → dig i = 0) → clampUsed dig n = u
  | 0, hu, _ => by simp [clampUsed]; omega
  | n + 1, hu, hz => by
    rcases Nat.lt_or_eq_of_le hu with h | h
    · simp only [clampUsed, hz n (by omega) (Nat.lt_succ_self n), if_true]
      exact clampUsed_eq dig u ht n (by omega) (fun i h1 h2 => hz i h1 (Nat.lt_succ_of_lt h2))
    · subst h
      rcases ht with ht | ht
      · omega
      · simp only [clampUsed, Nat.add_sub_cancel] at ht ⊢; simp [ht]

/-! ## `mp_cmp_mag` -/

/-- The digit loop of `mp_cmp_mag`: compare digits `n - 1` down to `0`. -/
def cmpTop (da db : Nat → Nat) : Nat → Ordering
  | 0 => .eq
  | n + 1 => if da n > db n then .gt else if da n < db n then .lt else cmpTop da db n

/-- Equal digits from `m` to `n` do not change the comparison. -/
theorem cmpTop_skip (da db : Nat → Nat) (m : Nat) :
    ∀ n, m ≤ n → (∀ j, m ≤ j → j < n → da j = db j) → cmpTop da db n = cmpTop da db m
  | 0, h, _ => by rw [Nat.le_zero.1 h]
  | n + 1, h, he => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · have hn := he n (by omega) (Nat.lt_succ_self n)
      simp only [cmpTop, hn, Nat.lt_irrefl, if_false]
      exact cmpTop_skip da db m n (by omega) (fun j h1 h2 => he j h1 (Nat.lt_succ_of_lt h2))
    · rw [h]

/-- `mp_cmp_mag`: compare `used`, then the digits from the top. -/
def cmpMag (a b : MpInt) : Ordering :=
  if a.used > b.used then .gt else if a.used < b.used then .lt else cmpTop a.digit b.digit a.used

end Tom

namespace Tom

/-! ## `natUpTo` -/

theorem natUpTo_lt (dig : Nat → Nat) (h : ∀ i, dig i < radix) : ∀ n, natUpTo dig n < radix ^ n
  | 0 => by simp [natUpTo]
  | n + 1 => by
    have ih := natUpTo_lt dig h n
    have hd := h n
    simp only [natUpTo, Nat.pow_succ]
    have : radix ^ n * dig n + radix ^ n ≤ radix ^ n * radix := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hd
    omega

theorem natUpTo_ge_top (dig : Nat → Nat) (n : Nat) (h : dig n ≠ 0) :
    radix ^ n ≤ natUpTo dig (n + 1) := by
  simp only [natUpTo]
  have : radix ^ n * 1 ≤ radix ^ n * dig n := Nat.mul_le_mul_left _ (by omega)
  omega

theorem natUpTo_congr {d e : Nat → Nat} : ∀ n, (∀ i, i < n → d i = e i) → natUpTo d n = natUpTo e n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [natUpTo, natUpTo_congr n (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

/-- Zero digits from `m` to `n` add nothing. -/
theorem natUpTo_zeros (dig : Nat → Nat) (m : Nat) :
    ∀ n, m ≤ n → (∀ i, m ≤ i → i < n → dig i = 0) → natUpTo dig n = natUpTo dig m
  | 0, h, _ => by rw [Nat.le_zero.1 h]
  | n + 1, h, hz => by
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · simp only [natUpTo, hz n (by omega) (Nat.lt_succ_self n), Nat.mul_zero, Nat.add_zero]
      exact natUpTo_zeros dig m n (by omega) (fun i h1 h2 => hz i h1 (Nat.lt_succ_of_lt h2))
    · rfl

theorem natOf_take (ds : List Nat) : ∀ n, natOf (ds.take n) = natUpTo (fun i => ds.getD i 0) n
  | 0 => by simp [natOf, natUpTo]
  | n + 1 => by
    rw [natUpTo, ← natOf_take ds n]
    by_cases hn : n < ds.length
    · rw [List.take_add_one, List.getElem?_eq_getElem hn, Option.toList_some, natOf_append,
        List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)]
      simp [natOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    · have h1 : ds.take (n + 1) = ds.take n := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : ds.length ≤ n)]

/-! ## `mp_clamp` keeps the value -/

theorem natUpTo_clampUsed (dig : Nat → Nat) (n : Nat) :
    natUpTo dig (clampUsed dig n) = natUpTo dig n :=
  (natUpTo_zeros dig _ n (clampUsed_le dig n) (clampUsed_zero dig n)).symm

/-! ## `mp_cmp_mag` compares magnitudes -/

theorem cmpTop_eq (da db : Nat → Nat) (ha : ∀ i, da i < radix) (hb : ∀ i, db i < radix) :
    ∀ n, cmpTop da db n = compare (natUpTo da n) (natUpTo db n)
  | 0 => by simp [cmpTop, natUpTo]
  | n + 1 => by
    have hA := natUpTo_lt da ha n
    have hB := natUpTo_lt db hb n
    simp only [cmpTop, natUpTo]
    split
    · rename_i hgt
      have : radix ^ n * (db n + 1) ≤ radix ^ n * da n := Nat.mul_le_mul_left _ hgt
      rw [Nat.mul_succ] at this
      exact (Nat.compare_eq_gt.2 (by omega)).symm
    · split
      · rename_i _ hlt
        have : radix ^ n * (da n + 1) ≤ radix ^ n * db n := Nat.mul_le_mul_left _ hlt
        rw [Nat.mul_succ] at this
        exact (Nat.compare_eq_lt.2 (by omega)).symm
      · rename_i h1 h2
        have he : da n = db n := by omega
        rw [cmpTop_eq da db ha hb n, he]
        simp only [Nat.compare_eq_ite_lt (natUpTo da n), Nat.compare_eq_ite_lt (_ + _)]
        by_cases h3 : natUpTo da n < natUpTo db n
        · simp [h3]
        · by_cases h4 : natUpTo db n < natUpTo da n
          · simp [h3, h4]
          · simp [h3, h4]

/-- A valid `mp_int` with `used` digits has magnitude in `[radix^(used-1), radix^used)`. -/
theorem MpInt.mag_lt {a : MpInt} (h : a.Shape) : a.mag < radix ^ a.used :=
  natUpTo_lt _ h.digit_lt _

theorem MpInt.mag_ge {a : MpInt} (h : a.Valid) (hu : 0 < a.used) : radix ^ (a.used - 1) ≤ a.mag := by
  have := natUpTo_ge_top a.digit (a.used - 1) (h.top hu)
  rwa [Nat.sub_add_cancel hu] at this

theorem cmpMag_eq {a b : MpInt} (ha : a.Valid) (hb : b.Valid) : cmpMag a b = compare a.mag b.mag := by
  unfold cmpMag
  split
  · rename_i h
    have h1 := MpInt.mag_ge ha (by omega)
    have h2 := MpInt.mag_lt hb.toShape
    have : radix ^ b.used ≤ radix ^ (a.used - 1) := Nat.pow_le_pow_right radix_pos (by omega)
    exact (Nat.compare_eq_gt.2 (by omega)).symm
  · split
    · rename_i _ h
      have h1 := MpInt.mag_ge hb (by omega)
      have h2 := MpInt.mag_lt ha.toShape
      have : radix ^ a.used ≤ radix ^ (b.used - 1) := Nat.pow_le_pow_right radix_pos (by omega)
      exact (Nat.compare_eq_lt.2 (by omega)).symm
    · rename_i h1 h2
      have he : a.used = b.used := by omega
      unfold MpInt.mag; rw [← he]
      exact cmpTop_eq _ _ ha.digit_lt hb.digit_lt _

end Tom
