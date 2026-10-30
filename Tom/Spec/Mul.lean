import Tom.Spec.Signed
import Tom.Spec.MpIntU

/-!
# Multiplication: columns and the comba carry chain

The product of two digit vectors, column by column:
`col da db ua ub k = Σ_{i < ua, i ≤ k, k - i < ub} da i * db (k - i)`, and
`natUpTo da ua * natUpTo db ub = natUpTo (col …) (ua + ub)` (`prod_cols`).

`s_mp_mul_digs_fast` (comba) computes column `k` as the C does
(`colC`: from `tx = k - ty`, `ty = min (ub - 1) k`, `iy = min (ua - tx) (ty + 1)`
terms `da (tx + iz) * db (ty - iz)`; `colC_eq`: it is `col`), adds the carry
`combaW k`, keeps the low digit (`combaD`) and carries the rest
(`comba_sum`). With `digs ≥ ua + ub` the digits are the product
(`comba_prod`); with fewer, the product mod `radix ^ digs` (`comba_mod`).
`MulFastPost.spec`: what the C leaves, as values.

`mp_mul_d` is the same carry chain over the row `a.digit i * b` (`MulDPost.spec`).
`s_mp_mul_digs` (schoolbook) adds rows into a `digs`-digit temporary
(`rowStep`, `schoolT`): each row adds `radix^ix * a[ix] * |b|` mod
`radix ^ digs` (`row_val`), so the temporary ends as `|a| * |b| mod radix ^ digs`
(`schoolT_val`).
-/

namespace Tom

/-- `Σ_{i<n} f i`. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_congr {f g : Nat → Nat} : ∀ n, (∀ i, i < n → f i = g i) → sumTo f n = sumTo g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [sumTo, sumTo_congr n (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem sumTo_zeros (f : Nat → Nat) (m : Nat) :
    ∀ n, m ≤ n → (∀ i, m ≤ i → i < n → f i = 0) → sumTo f n = sumTo f m
  | 0, h, _ => by rw [Nat.le_zero.1 h]
  | n + 1, h, hz => by
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · simp only [sumTo, hz n (by omega) (Nat.lt_succ_self n), Nat.add_zero]
      exact sumTo_zeros f m n (by omega) (fun i h1 h2 => hz i h1 (Nat.lt_succ_of_lt h2))
    · rfl

theorem sumTo_zero_fun (n : Nat) : sumTo (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumTo, ih]

/-- An indicator sum over `[lo, hi)` is a sum from `lo`. -/
theorem sumTo_window (g : Nat → Nat) (lo hi : Nat) :
    ∀ n, hi ≤ n → sumTo (fun i => if lo ≤ i ∧ i < hi then g i else 0) n = sumTo (fun iz => g (lo + iz)) (hi - lo) := by
  intro n hn
  rw [sumTo_zeros _ hi n hn (fun i h1 _ => by simp only [show ¬ i < hi by omega, and_false, if_false])]
  by_cases hlh : lo ≤ hi
  · obtain ⟨m, rfl⟩ : ∃ m, hi = lo + m := ⟨hi - lo, by omega⟩
    rw [show lo + m - lo = m by omega]
    induction m with
    | zero =>
      simp only [Nat.add_zero, sumTo]
      rw [sumTo_zeros _ 0 lo (Nat.zero_le _) (fun i _ h2 => by simp only [show ¬ lo ≤ i by omega, false_and,
        if_false])]
      rfl
    | succ m ih =>
      rw [show lo + (m + 1) = (lo + m) + 1 by omega, sumTo, sumTo]
      rw [sumTo_congr (lo + m) (g := fun i => if lo ≤ i ∧ i < lo + m then g i else 0)
        (fun i hi => by simp only [show i < lo + m + 1 ↔ True from ⟨fun _ => trivial, fun _ => by omega⟩,
          show i < lo + m ↔ True from ⟨fun _ => trivial, fun _ => hi⟩])]
      rw [ih (by omega) (by omega)]
      simp only [show lo ≤ lo + m by omega, show lo + m < lo + m + 1 by omega, and_self, if_true]
  · rw [show hi - lo = 0 by omega, sumTo_zeros _ 0 hi (Nat.zero_le _)
      (fun i _ h2 => by simp only [show ¬ lo ≤ i by omega, false_and, if_false])]
    rfl

/-! ## `natUpTo` arithmetic -/

theorem natUpTo_zero_fun (n : Nat) : natUpTo (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natUpTo, ih]

theorem natUpTo_add (f g : Nat → Nat) (n : Nat) :
    natUpTo (fun i => f i + g i) n = natUpTo f n + natUpTo g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [natUpTo, ih, Nat.mul_add]; omega

theorem natUpTo_mul (c : Nat) (f : Nat → Nat) (n : Nat) :
    natUpTo (fun i => c * f i) n = c * natUpTo f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [natUpTo, ih, Nat.mul_add]
    rw [Nat.mul_left_comm]

/-- A vector shifted up by `s` places. -/
theorem natUpTo_shift (h : Nat → Nat) (s : Nat) :
    ∀ n, natUpTo (fun k => if s ≤ k then h (k - s) else 0) (s + n) = radix ^ s * natUpTo h n
  | 0 => by
    simp only [Nat.add_zero, natUpTo, Nat.mul_zero]
    rw [natUpTo_zeros _ 0 s (Nat.zero_le _) (fun i _ h2 => by simp only [show ¬ s ≤ i by omega, if_false])]
    rfl
  | n + 1 => by
    rw [show s + (n + 1) = (s + n) + 1 by omega, natUpTo, natUpTo_shift h s n, natUpTo]
    simp only [show s ≤ s + n by omega, if_true, show s + n - s = n by omega, Nat.pow_add, Nat.mul_add]
    rw [Nat.mul_assoc]

/-- Splitting at `m`. -/
theorem natUpTo_split (f : Nat → Nat) (m : Nat) :
    ∀ n, natUpTo f (m + n) = natUpTo f m + radix ^ m * natUpTo (fun i => f (m + i)) n
  | 0 => by simp [natUpTo]
  | n + 1 => by
    rw [show m + (n + 1) = (m + n) + 1 by omega, natUpTo, natUpTo_split f m n, natUpTo, Nat.pow_add,
      Nat.mul_add, Nat.mul_assoc]
    omega

/-! ## Columns -/

/-- Column `k` of the product of `da` (`ua` digits) and `db` (`ub` digits). -/
def col (da db : Nat → Nat) (ua ub k : Nat) : Nat :=
  sumTo (fun i => if i ≤ k ∧ k - i < ub then da i * db (k - i) else 0) ua

theorem col_zero_ua (da db : Nat → Nat) (ub k : Nat) : col da db 0 ub k = 0 := rfl

theorem col_succ (da db : Nat → Nat) (ua ub k : Nat) :
    col da db (ua + 1) ub k =
      col da db ua ub k + if ua ≤ k ∧ k - ua < ub then da ua * db (k - ua) else 0 := rfl

/-- Columns at and above `ua + ub - 1` are empty. -/
theorem col_high (da db : Nat → Nat) (ua ub k : Nat) (hk : ua + ub ≤ k + 1) : col da db ua ub k = 0 := by
  unfold col
  rw [sumTo_congr ua (g := fun _ => 0) (fun i hi => by
    simp only [show ¬ (i ≤ k ∧ k - i < ub) by omega, if_false]), sumTo_zero_fun]

/-- **Schoolbook**: the product is the sum of its columns. -/
theorem prod_cols (da db : Nat → Nat) (ub : Nat) :
    ∀ ua, natUpTo da ua * natUpTo db ub = natUpTo (col da db ua ub) (ua + ub)
  | 0 => by
    simp only [natUpTo, Nat.zero_mul, Nat.zero_add]
    rw [natUpTo_congr ub (e := fun _ => 0) (fun i _ => col_zero_ua da db ub i), natUpTo_zero_fun]
  | ua + 1 => by
    have ih := prod_cols da db ub ua
    -- the new column terms: `da ua * db j` at `ua + j`
    have hsplit : natUpTo (col da db (ua + 1) ub) (ua + 1 + ub) =
        natUpTo (col da db ua ub) (ua + 1 + ub) +
          natUpTo (fun k => if ua ≤ k then (if k - ua < ub then da ua * db (k - ua) else 0) else 0)
            (ua + 1 + ub) := by
      rw [← natUpTo_add]
      apply natUpTo_congr; intro k _
      rw [col_succ]
      by_cases h1 : ua ≤ k
      · by_cases h2 : k - ua < ub <;> simp [h1, h2]
      · simp [h1]
    have hold : natUpTo (col da db ua ub) (ua + 1 + ub) = natUpTo (col da db ua ub) (ua + ub) :=
      natUpTo_zeros _ _ _ (by omega) (fun k h1 _ => col_high da db ua ub k (by omega))
    have hnew : natUpTo (fun k => if ua ≤ k then (if k - ua < ub then da ua * db (k - ua) else 0) else 0)
        (ua + 1 + ub) = radix ^ ua * (da ua * natUpTo db ub) := by
      rw [show ua + 1 + ub = ua + (ub + 1) by omega,
        natUpTo_shift (fun j => if j < ub then da ua * db j else 0) ua (ub + 1)]
      congr 1
      rw [natUpTo, if_neg (Nat.lt_irrefl _), Nat.mul_zero, Nat.add_zero,
        natUpTo_congr ub (e := fun j => da ua * db j) (fun j hj => by simp [hj]), natUpTo_mul]
    rw [hsplit, hold, hnew, ← ih, natUpTo, Nat.add_mul, Nat.mul_assoc]

/-! ## Comba: the C's column and the carry chain -/

/-- `ty = MP_MIN(b->used - 1, ix)` (for `ub ≥ 1`). -/
def combaTy (ub k : Nat) : Nat := min (ub - 1) k

/-- `tx = ix - ty`. -/
def combaTx (ub k : Nat) : Nat := k - combaTy ub k

/-- `iy = MP_MIN(a->used - tx, ty + 1)`. -/
def combaIy (ua ub k : Nat) : Nat := min (ua - combaTx ub k) (combaTy ub k + 1)

/-- The inner loop's partial sum after `n` terms: `Σ_{iz<n} da (tx + iz) * db (ty - iz)`. -/
def combaPart (da db : Nat → Nat) (ub k n : Nat) : Nat :=
  sumTo (fun iz => da (combaTx ub k + iz) * db (combaTy ub k - iz)) n

/-- Column `k` as `s_mp_mul_digs_fast` computes it. -/
def colC (da db : Nat → Nat) (ua ub k : Nat) : Nat := combaPart da db ub k (combaIy ua ub k)

/-- The C's column is the column. -/
theorem colC_eq (da db : Nat → Nat) (ua ub k : Nat) (hub : 1 ≤ ub) :
    colC da db ua ub k = col da db ua ub k := by
  unfold colC combaPart col
  have hw := sumTo_window (fun i => da i * db (k - i)) (combaTx ub k) (min ua (k + 1)) ua (Nat.min_le_left _ _)
  rw [sumTo_congr ua (g := fun i => if combaTx ub k ≤ i ∧ i < min ua (k + 1) then da i * db (k - i) else 0)
    (fun i hi => by
      unfold combaTx combaTy
      by_cases h : i ≤ k ∧ k - i < ub
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]), hw]
  have hiy : combaIy ua ub k = min ua (k + 1) - combaTx ub k := by
    unfold combaIy combaTx combaTy; omega
  rw [hiy]
  apply sumTo_congr; intro iz hiz
  unfold combaTx combaTy at *
  rw [show k - (k - min (ub - 1) k + iz) = min (ub - 1) k - iz by omega]

/-- The carry into column `k` (`_W` before the column's terms). -/
def combaW (cl : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (combaW cl k + cl k) / radix

/-- Digit `k` (`W[ix] = _W & MP_MASK`). -/
def combaD (cl : Nat → Nat) (k : Nat) : Nat := (combaW cl k + cl k) % radix

theorem combaD_lt (cl : Nat → Nat) (k : Nat) : combaD cl k < radix := Nat.mod_lt _ radix_pos

/-- **The carry chain**: digits plus the outgoing carry are the column sum. -/
theorem comba_sum (cl : Nat → Nat) :
    ∀ n, natUpTo (combaD cl) n + radix ^ n * combaW cl n = natUpTo cl n
  | 0 => by simp [natUpTo, combaW]
  | n + 1 => by
    have ih := comba_sum cl n
    have hdm := Nat.mod_add_div (combaW cl n + cl n) radix
    simp only [natUpTo, combaW, combaD, Nat.pow_succ]
    have : radix ^ n * radix * ((combaW cl n + cl n) / radix) =
        radix ^ n * (radix * ((combaW cl n + cl n) / radix)) := by rw [Nat.mul_assoc]
    rw [this]
    have e : radix ^ n * ((combaW cl n + cl n) % radix) + radix ^ n * (radix * ((combaW cl n + cl n) / radix)) =
        radix ^ n * combaW cl n + radix ^ n * cl n := by
      rw [← Nat.mul_add, hdm, Nat.mul_add]
    omega

/-- With room for every column, the digits are the product and no carry is left. -/
theorem comba_prod (da db : Nat → Nat) (ua ub : Nat) (ha : ∀ i, da i < radix) (hb : ∀ i, db i < radix) :
    natUpTo (combaD (col da db ua ub)) (ua + ub) = natUpTo da ua * natUpTo db ub ∧
      combaW (col da db ua ub) (ua + ub) = 0 := by
  have hs := comba_sum (col da db ua ub) (ua + ub)
  rw [← prod_cols] at hs
  have hlt : natUpTo da ua * natUpTo db ub < radix ^ (ua + ub) := by
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul'' (natUpTo_lt da ha ua) (natUpTo_lt db hb ub)
  have hw : combaW (col da db ua ub) (ua + ub) = 0 := by
    rcases Nat.eq_zero_or_pos (combaW (col da db ua ub) (ua + ub)) with h | h
    · exact h
    · have : radix ^ (ua + ub) * 1 ≤ radix ^ (ua + ub) * combaW (col da db ua ub) (ua + ub) :=
        Nat.mul_le_mul_left _ h
      omega
  refine ⟨?_, hw⟩
  rw [hw, Nat.mul_zero, Nat.add_zero] at hs
  exact hs

/-- With `n` columns, the digits are the product mod `radix ^ n`. -/
theorem comba_mod (da db : Nat → Nat) (ua ub n : Nat) (hn : n ≤ ua + ub) :
    natUpTo (combaD (col da db ua ub)) n = (natUpTo da ua * natUpTo db ub) % radix ^ n := by
  obtain ⟨m, hm⟩ : ∃ m, ua + ub = n + m := ⟨ua + ub - n, by omega⟩
  have hs := comba_sum (col da db ua ub) n
  rw [prod_cols, hm, natUpTo_split, ← hs]
  have hlt := natUpTo_lt (combaD (col da db ua ub)) (combaD_lt _) n
  rw [Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-! ## Bounds the machine needs (`mp_word` does not overflow) -/

theorem sumTo_le {f : Nat → Nat} {B : Nat} : ∀ n, (∀ i, i < n → f i ≤ B) → sumTo f n ≤ n * B
  | 0, _ => by simp [sumTo]
  | n + 1, h => by
    have := sumTo_le n (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have := h n (Nat.lt_succ_self n)
    simp only [sumTo, Nat.succ_mul]; omega

theorem sumTo_mono (f : Nat → Nat) {m n : Nat} (h : m ≤ n) : sumTo f m ≤ sumTo f n := by
  induction n with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · simp only [sumTo]; have := ih (by omega); omega
    · exact Nat.le_refl _

/-- A partial column is at most the column. -/
theorem combaPart_le (da db : Nat → Nat) (ua ub k n : Nat) (hn : n ≤ combaIy ua ub k) :
    combaPart da db ub k n ≤ colC da db ua ub k := sumTo_mono _ hn

/-- A column has at most `min ua ub` terms, each below `radix ^ 2`. -/
theorem colC_le {da db : Nat → Nat} (ha : ∀ i, da i < radix) (hb : ∀ i, db i < radix) (ua ub k : Nat)
    (hub : 1 ≤ ub) :
    colC da db ua ub k ≤ min ua ub * ((radix - 1) * (radix - 1)) := by
  unfold colC combaPart
  have hiy : combaIy ua ub k ≤ min ua ub := by unfold combaIy combaTx combaTy; omega
  refine Nat.le_trans (sumTo_le _ (B := (radix - 1) * (radix - 1)) fun i _ =>
    Nat.mul_le_mul (by have := ha (combaTx ub k + i); omega) (by have := hb (combaTy ub k - i); omega))
    (Nat.mul_le_mul_right _ hiy)

/-- The carry stays below `2 ^ 36` while every column leaves `2 ^ 36` of room in 64 bits. -/
theorem combaW_lt {cl : Nat → Nat} (hcl : ∀ k, cl k + 2 ^ 36 ≤ 2 ^ 64) : ∀ k, combaW cl k < 2 ^ 36
  | 0 => by simp [combaW]
  | k + 1 => by
    have ih := combaW_lt hcl k
    have := hcl k
    simp only [combaW]
    exact Nat.div_lt_of_lt_mul (by simp only [radix, Layout.digitBits]; omega)

/-- `MP_MAXFAST = 256` operands leave that room. -/
theorem colC_room {da db : Nat → Nat} (ha : ∀ i, da i < radix) (hb : ∀ i, db i < radix) (ua ub k : Nat)
    (hub : 1 ≤ ub) (hm : min ua ub ≤ 256) : colC da db ua ub k + 2 ^ 36 ≤ 2 ^ 64 := by
  have h := colC_le ha hb ua ub k hub
  have h2 : min ua ub * ((radix - 1) * (radix - 1)) ≤ 256 * ((radix - 1) * (radix - 1)) :=
    Nat.mul_le_mul_right _ hm
  simp only [radix, Layout.digitBits] at h h2 ⊢
  omega

/-! ## `s_mp_mul_digs_fast` -/

/-- The digits `s_mp_mul_digs_fast(a, b, c, digs)` leaves: the comba digits of the
first `pa = min digs (a.used + b.used)` columns, zero above. -/
def mulFastDigit (a b : MpInt) (pa i : Nat) : Nat :=
  if i < pa then combaD (col a.digit b.digit a.used b.used) i else 0

/-- What `s_mp_mul_digs_fast(a, b, c, digs)` leaves in `c` when `c->alloc ≥ digs`
(no `mp_grow`, D5): the comba digits, `used` clamped from `pa`, the sign reset if
zero (`mp_clamp`), `alloc` unchanged. -/
structure MulFastPost (a b c c' : MpInt) (digs : Nat) : Prop where
  alloc : c'.alloc = c.alloc
  len : c'.digits.length = c.alloc
  digit : c'.digit = mulFastDigit a b (min digs (a.used + b.used))
  used : c'.used = clampUsed (mulFastDigit a b (min digs (a.used + b.used))) (min digs (a.used + b.used))
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else c.sign

theorem mulFastDigit_lt (a b : MpInt) (pa i : Nat) : mulFastDigit a b pa i < radix := by
  unfold mulFastDigit; split
  · exact combaD_lt _ _
  · exact radix_pos

/-- `s_mp_mul_digs_fast` computes `|a| * |b| mod radix ^ digs` (the whole product when
`digs ≥ a.used + b.used`) and leaves `c` valid. -/
theorem MulFastPost.spec {a b c c' : MpInt} {digs : Nat} (ha : a.ShapeU) (hb : b.ShapeU)
    (hroom : digs ≤ c.alloc) (hc : c.alloc < 2 ^ 31)
    (hsign : c.sign = Layout.mpZpos ∨ c.sign = Layout.mpNeg) (h : MulFastPost a b c c' digs) :
    c'.Valid ∧ c'.mag = (a.mag * b.mag) % radix ^ (min digs (a.used + b.used)) ∧
      (a.used + b.used ≤ digs → c'.mag = a.mag * b.mag) := by
  have hle := clampUsed_le (mulFastDigit a b (min digs (a.used + b.used))) (min digs (a.used + b.used))
  have hmag : c'.mag = (a.mag * b.mag) % radix ^ (min digs (a.used + b.used)) := by
    unfold MpInt.mag; rw [h.digit, h.used, natUpTo_clampUsed]
    rw [natUpTo_congr _ (e := combaD (col a.digit b.digit a.used b.used))
      (fun i hi => by simp [mulFastDigit, hi])]
    exact comba_mod _ _ _ _ _ (Nat.min_le_right _ _)
  refine ⟨{ len := ?_, used_le := ?_, alloc_lt := ?_, digit_lt := ?_, high_zero := ?_,
            top := ?_, sign_ok := ?_, zero_pos := ?_ }, hmag, fun hd => ?_⟩
  · rw [h.len, h.alloc]
  · rw [h.used, h.alloc]; omega
  · rw [h.alloc]; exact hc
  · rw [h.digit]; exact mulFastDigit_lt a b _
  · intro i hi
    rw [h.digit]
    by_cases hlt : i < min digs (a.used + b.used)
    · exact clampUsed_zero _ _ i (h.used ▸ hi) hlt
    · simp [mulFastDigit, hlt]
  · intro hu; rw [h.digit, h.used]; exact clampUsed_top _ _ (h.used ▸ hu)
  · rw [h.sign]; split
    · exact Or.inl rfl
    · exact hsign
  · intro hu; rw [h.sign, ite_eq_left_iff.2 (fun h => absurd hu h)]
  · rw [hmag, Nat.min_eq_right hd]
    exact Nat.mod_eq_of_lt (by
      rw [Nat.pow_add]; exact Nat.mul_lt_mul'' ha.mag_lt hb.mag_lt)

/-! ## `mp_mul_d` -/

/-- The row `a * b` for a digit `b`: column `i` is `a.digit i * b`. -/
def mulDCol (a : MpInt) (b : Nat) (i : Nat) : Nat := a.digit i * b

/-- The digits `mp_mul_d(a, b, c)` leaves: the carry chain of the row, the last
carry at `a.used`, zero above. -/
def mulDDigit (a : MpInt) (b : Nat) (i : Nat) : Nat :=
  if i < a.used then combaD (mulDCol a b) i else if i = a.used then combaW (mulDCol a b) a.used else 0

/-- The carry stays a digit (`u` is an `mp_digit`). -/
theorem mulD_W_lt {a : MpInt} (ha : a.Shape) {b : Nat} (hb : b < radix) : ∀ i, combaW (mulDCol a b) i < radix
  | 0 => radix_pos
  | i + 1 => by
    have ih := mulD_W_lt ha hb i
    have hd := ha.digit_lt i
    simp only [combaW, mulDCol]
    apply Nat.div_lt_of_lt_mul
    have : a.digit i * b ≤ (radix - 1) * (radix - 1) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : (radix - 1) * (radix - 1) + radix ≤ radix * radix := by
      simp only [radix, Layout.digitBits]; omega
    omega

theorem mulDDigit_lt {a : MpInt} (ha : a.Shape) {b : Nat} (hb : b < radix) (i : Nat) : mulDDigit a b i < radix := by
  unfold mulDDigit; split
  · exact combaD_lt _ _
  · split
    · exact mulD_W_lt ha hb _
    · exact radix_pos

/-- What `mp_mul_d(a, b, c)` leaves in `c` when `c->alloc ≥ a->used + 1` (no
`mp_grow`, D5): the row's digits, `used` clamped from `a->used + 1`, `a`'s sign
(reset if zero), `alloc` unchanged. -/
structure MulDPost (a : MpInt) (b : Nat) (c c' : MpInt) : Prop where
  alloc : c'.alloc = c.alloc
  len : c'.digits.length = c.alloc
  digit : c'.digit = mulDDigit a b
  used : c'.used = clampUsed (mulDDigit a b) (a.used + 1)
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else a.sign

/-- `mp_mul_d` computes `|c| = |a| * b`, `c = a * b`, and leaves `c` valid. -/
theorem MulDPost.spec {a c c' : MpInt} {b : Nat} (ha : a.Valid) (hb : b < radix)
    (hroom : a.used + 1 ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (h : MulDPost a b c c') :
    c'.Valid ∧ c'.mag = a.mag * b ∧ c'.val = a.val * b := by
  have hle := clampUsed_le (mulDDigit a b) (a.used + 1)
  have hmag : c'.mag = a.mag * b := by
    unfold MpInt.mag; rw [h.digit, h.used, natUpTo_clampUsed, natUpTo]
    rw [natUpTo_congr _ (e := combaD (mulDCol a b)) (fun i hi => by simp [mulDDigit, hi])]
    simp only [mulDDigit, Nat.lt_irrefl, if_false, if_true]
    rw [comba_sum, Nat.mul_comm]
    unfold mulDCol; rw [natUpTo_congr _ (e := fun i => b * a.digit i) (fun i _ => Nat.mul_comm _ _), natUpTo_mul]
  have hs := ha.sign_ok
  refine ⟨{ len := ?_, used_le := ?_, alloc_lt := ?_, digit_lt := ?_, high_zero := ?_,
            top := ?_, sign_ok := ?_, zero_pos := ?_ }, hmag, ?_⟩
  · rw [h.len, h.alloc]
  · rw [h.used, h.alloc]; omega
  · rw [h.alloc]; exact hc
  · rw [h.digit]; exact mulDDigit_lt ha.toShape hb
  · intro i hi
    rw [h.digit]
    by_cases hlt : i < a.used + 1
    · exact clampUsed_zero _ _ i (h.used ▸ hi) hlt
    · simp [mulDDigit, show ¬ i < a.used by omega, show i ≠ a.used by omega]
  · intro hu; rw [h.digit, h.used]; exact clampUsed_top _ _ (h.used ▸ hu)
  · rw [h.sign]; split
    · exact Or.inl rfl
    · exact hs
  · intro hu; rw [h.sign, ite_eq_left_iff.2 (fun h => absurd hu h)]
  · unfold MpInt.val; rw [hmag, h.sign]
    by_cases hz : c'.used = 0
    · have : a.mag * b = 0 := by rw [← hmag]; exact MpInt.mag_used_zero hz
      simp only [hz, if_true, Layout.mpZpos, Layout.mpNeg]
      rcases Nat.mul_eq_zero.1 this with h0 | h0 <;> split <;> simp [h0]
    · simp only [hz, if_false]; split <;> push_cast <;> simp [Int.neg_mul]

/-! ## `s_mp_mul_digs`: schoolbook rows into a `digs`-digit temporary -/

/-- Row `ix`'s column inputs: `t[ix + iy] + tmpx * b[iy]`. -/
def rowCl (T : Nat → Nat) (x : Nat) (db : Nat → Nat) (ix iy : Nat) : Nat := T (ix + iy) + x * db iy

/-- One row of `s_mp_mul_digs`: `pb` columns of the carry chain from `ix`, then the
last carry at `ix + pb` when that is below `digs`. -/
def rowStep (T : Nat → Nat) (x : Nat) (db : Nat → Nat) (ix pb digs : Nat) : Nat → Nat := fun j =>
  if ix ≤ j ∧ j < ix + pb then combaD (rowCl T x db ix) (j - ix)
  else if j = ix + pb ∧ ix + pb < digs then combaW (rowCl T x db ix) pb else T j

/-- The temporary after `ix` rows (`pb = MP_MIN(b->used, digs - ix)`). -/
def schoolT (da db : Nat → Nat) (ub digs : Nat) : Nat → Nat → Nat
  | 0 => fun _ => 0
  | ix + 1 => rowStep (schoolT da db ub digs ix) (da ix) db ix (min ub (digs - ix)) digs

/-- A row's carry stays a digit (`u` is an `mp_digit`). -/
theorem rowW_lt {T : Nat → Nat} {x : Nat} {db : Nat → Nat} {ix : Nat} (hT : ∀ j, T j < radix) (hx : x < radix)
    (hb : ∀ j, db j < radix) : ∀ n, combaW (rowCl T x db ix) n < radix
  | 0 => radix_pos
  | n + 1 => by
    have ih := rowW_lt (ix := ix) hT hx hb n
    have h1 := hT (ix + n); have h2 := hb n
    simp only [combaW, rowCl]
    apply Nat.div_lt_of_lt_mul
    have : x * db n ≤ (radix - 1) * (radix - 1) := Nat.mul_le_mul (by omega) (by omega)
    have h3 : (radix - 1) * (radix - 1) + 2 * radix ≤ radix * radix + 1 := by
      simp only [radix, Layout.digitBits]; omega
    omega

theorem rowStep_lt {T : Nat → Nat} {x : Nat} {db : Nat → Nat} {ix pb digs : Nat} (hT : ∀ j, T j < radix)
    (hx : x < radix) (hb : ∀ j, db j < radix) (j : Nat) : rowStep T x db ix pb digs j < radix := by
  unfold rowStep; split
  · exact combaD_lt _ _
  · split
    · exact rowW_lt hT hx hb _
    · exact hT j

theorem rowStep_high {T : Nat → Nat} {x : Nat} {db : Nat → Nat} {ix ub digs : Nat}
    (hz : ∀ j, ix + ub ≤ j → T j = 0) (j : Nat) (hj : ix + 1 + ub ≤ j) :
    rowStep T x db ix (min ub (digs - ix)) digs j = 0 := by
  unfold rowStep
  rw [if_neg (by omega), if_neg (by omega)]
  exact hz j (by omega)

/-- **One row**: it adds `radix^ix * x * |b|` to the temporary, mod `radix ^ digs`. -/
theorem row_val {T : Nat → Nat} {x : Nat} {db : Nat → Nat} {ix ub digs : Nat} (hT : ∀ j, T j < radix)
    (hx : x < radix) (hb : ∀ j, db j < radix) (hz : ∀ j, ix + ub ≤ j → T j = 0) :
    natUpTo (rowStep T x db ix (min ub (digs - ix)) digs) digs =
      (natUpTo T digs + radix ^ ix * (x * natUpTo db ub)) % radix ^ digs := by
  have hlt := natUpTo_lt _ (rowStep_lt (ix := ix) (pb := min ub (digs - ix)) (digs := digs) hT hx hb) digs
  by_cases hix : digs ≤ ix
  · -- no column of this row is below `digs`
    have he : natUpTo (rowStep T x db ix (min ub (digs - ix)) digs) digs = natUpTo T digs :=
      natUpTo_congr _ (fun j hj => by unfold rowStep; rw [if_neg (by omega), if_neg (by omega)])
    rw [he]
    obtain ⟨e, he⟩ : ∃ e, ix = digs + e := ⟨ix - digs, by omega⟩
    rw [he, Nat.pow_add, Nat.mul_assoc, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (natUpTo_lt _ hT digs)]
  · obtain ⟨n, rfl⟩ : ∃ n, digs = ix + n := ⟨digs - ix, by omega⟩
    rw [Nat.add_sub_cancel_left] at hlt ⊢
    have hpn : min ub n ≤ n := Nat.min_le_right _ _
    have hpu : min ub n ≤ ub := Nat.min_le_left _ _
    have hcase : min ub n = ub ∨ min ub n = n := by omega
    generalize min ub n = p at hlt hpn hpu hcase ⊢
    obtain ⟨q, rfl⟩ : ∃ q, n = p + q := ⟨n - p, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, ub = p + r := ⟨ub - p, by omega⟩
    -- the pieces of the left side
    have hlow : natUpTo (rowStep T x db ix p (ix + (p + q))) ix = natUpTo T ix :=
      natUpTo_congr _ (fun j hj => by unfold rowStep; rw [if_neg (by omega), if_neg (by omega)])
    have hmid : natUpTo (fun i => rowStep T x db ix p (ix + (p + q)) (ix + i)) p =
        natUpTo (combaD (rowCl T x db ix)) p :=
      natUpTo_congr _ (fun i hi => by unfold rowStep; rw [if_pos (by omega), show ix + i - ix = i by omega])
    have hL : natUpTo (rowStep T x db ix p (ix + (p + q))) (ix + (p + q)) =
        natUpTo T ix + radix ^ ix * (natUpTo (combaD (rowCl T x db ix)) p +
          radix ^ p * natUpTo (fun i => rowStep T x db ix p (ix + (p + q)) (ix + (p + i))) q) := by
      rw [natUpTo_split _ ix (p + q), hlow, natUpTo_split (fun i => rowStep T x db ix p (ix + (p + q)) (ix + i)) p q,
        hmid]
    -- the pieces of the right side
    have hcs := comba_sum (rowCl T x db ix) p
    have hcl : natUpTo (rowCl T x db ix) p = natUpTo (fun i => T (ix + i)) p + x * natUpTo db p := by
      unfold rowCl; rw [natUpTo_add, natUpTo_mul]
    have hB := natUpTo_split db p r
    have hTd : natUpTo T (ix + (p + q)) = natUpTo T ix + radix ^ ix * (natUpTo (fun i => T (ix + i)) p +
        radix ^ p * natUpTo (fun i => T (ix + (p + i))) q) := by
      rw [natUpTo_split _ ix (p + q), natUpTo_split (fun i => T (ix + i)) p q]
    -- atoms
    generalize hA : natUpTo T ix = A at hL hTd
    generalize hD : natUpTo (combaD (rowCl T x db ix)) p = D at hL hcs
    generalize hW : combaW (rowCl T x db ix) p = W at hcs
    generalize hTm : natUpTo (fun i => T (ix + i)) p = Tm at hcl hTd
    generalize hBp : natUpTo db p = Bp at hcl hB
    generalize hRest : natUpTo (fun i => db (p + i)) r = Rest at hB
    generalize hP : radix ^ ix = P at hL hTd
    generalize hQ : radix ^ p = Q at hL hTd hcs hB
    rw [hcl] at hcs
    have hcsP : P * D + P * (Q * W) = P * Tm + P * (x * Bp) := by
      rw [← Nat.mul_add, ← Nat.mul_add, hcs]
    rcases Nat.eq_zero_or_pos q with hq | hq
    · -- `ix + pb = digs`: the last carry is dropped
      subst hq
      simp only [Nat.add_zero] at *
      simp only [natUpTo, Nat.mul_zero, Nat.add_zero] at hL hTd
      have hPQ : radix ^ (ix + p) = P * Q := by rw [← hP, ← hQ, Nat.pow_add]
      rw [hL, hTd, hB, hPQ]
      rw [hL, hPQ] at hlt
      have e : A + P * Tm + P * (x * (Bp + Q * Rest)) = (A + P * D) + P * Q * (W + x * Rest) := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hcsP ⊢
        omega
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    · -- `pb = ub < digs - ix`: so `r = 0`; the last carry is stored at `ix + ub`, zeros above
      have hr : r = 0 := by omega
      subst hr
      simp only [Nat.add_zero] at *
      have hR0 : Rest = 0 := by rw [← hRest]; rfl
      subst hR0
      simp only [Nat.mul_zero, Nat.add_zero] at hB
      have htop : natUpTo (fun i => rowStep T x db ix p (ix + (p + q)) (ix + (p + i))) q = W := by
        rw [natUpTo_zeros _ 1 q hq (fun i h1 _ => by
          unfold rowStep; rw [if_neg (by omega), if_neg (by omega)]; exact hz _ (by omega))]
        simp only [natUpTo, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
        unfold rowStep; rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, hW]
      have htq : natUpTo (fun i => T (ix + (p + i))) q = 0 := by
        rw [natUpTo_congr q (e := fun _ => 0) (fun i _ => hz _ (by omega)), natUpTo_zero_fun]
      rw [htop] at hL; rw [htq, Nat.mul_zero, Nat.add_zero] at hTd
      rw [hL] at hlt
      rw [hL, hTd, hB]
      have e : A + P * Tm + P * (x * Bp) = A + P * (D + Q * W) := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hcsP ⊢
        omega
      rw [e, Nat.mod_eq_of_lt hlt]

/-- **Schoolbook**: after `ix` rows the temporary holds `|a mod radix^ix| * |b| mod radix ^ digs`
(digits below `radix`, zero from `ix + ub` on). -/
theorem schoolT_val {da db : Nat → Nat} {ub digs : Nat} (ha : ∀ i, da i < radix) (hb : ∀ i, db i < radix) :
    ∀ ix, (∀ j, schoolT da db ub digs ix j < radix) ∧ (∀ j, ix + ub ≤ j → schoolT da db ub digs ix j = 0) ∧
      natUpTo (schoolT da db ub digs ix) digs = (natUpTo da ix * natUpTo db ub) % radix ^ digs
  | 0 => ⟨fun _ => radix_pos, fun _ _ => rfl, by simp [schoolT, natUpTo, natUpTo_zero_fun]⟩
  | ix + 1 => by
    obtain ⟨hlt, hz, hv⟩ := schoolT_val ha hb ix
    refine ⟨fun j => rowStep_lt hlt (ha ix) hb j, fun j hj => rowStep_high hz j (by omega), ?_⟩
    show natUpTo (rowStep (schoolT da db ub digs ix) (da ix) db ix (min ub (digs - ix)) digs) digs = _
    rw [row_val hlt (ha ix) hb hz, hv, Nat.mod_add_mod, natUpTo, Nat.add_mul]
    congr 2
    rw [Nat.mul_assoc]

/-! ## Squaring: a column is twice its half plus the middle square -/

theorem sumTo_succ_left (f : Nat → Nat) : ∀ n, sumTo f (n + 1) = f 0 + sumTo (fun i => f (i + 1)) n
  | 0 => by simp [sumTo]
  | n + 1 => by
    rw [sumTo, sumTo_succ_left f n, sumTo]; omega

/-- A window whose terms pair up symmetrically sums to twice its first half plus,
for an odd length, its middle term. -/
theorem sumTo_sym (g : Nat → Nat) :
    ∀ L lo, (∀ iz, iz < L → g (lo + iz) = g (lo + (L - 1 - iz))) →
      sumTo (fun iz => g (lo + iz)) L =
        2 * sumTo (fun iz => g (lo + iz)) (L / 2) + (if L % 2 = 1 then g (lo + L / 2) else 0)
  | 0, _, _ => by simp [sumTo]
  | 1, lo, _ => by simp [sumTo]
  | L + 2, lo, h => by
    have ih := sumTo_sym g L (lo + 1) (fun iz hiz => by
      have := h (iz + 1) (by omega)
      rw [show lo + 1 + iz = lo + (iz + 1) by omega, show lo + 1 + (L - 1 - iz) = lo + (L + 2 - 1 - (iz + 1)) by omega]
      exact this)
    have hends : g (lo + (L + 1)) = g lo := by
      have := h 0 (by omega); rw [Nat.add_zero, show L + 2 - 1 - 0 = L + 1 by omega] at this; exact this.symm
    have hsh : ∀ n, sumTo (fun i => g (lo + (i + 1))) n = sumTo (fun iz => g (lo + 1 + iz)) n :=
      fun n => sumTo_congr n (fun i _ => by rw [show lo + (i + 1) = lo + 1 + i by omega])
    have e1 : sumTo (fun iz => g (lo + iz)) (L + 2) =
        g lo + sumTo (fun iz => g (lo + 1 + iz)) L + g (lo + (L + 1)) := by
      rw [sumTo, sumTo_succ_left, hsh, Nat.add_zero]
    have e2 : sumTo (fun iz => g (lo + iz)) ((L + 2) / 2) = g lo + sumTo (fun iz => g (lo + 1 + iz)) (L / 2) := by
      rw [show (L + 2) / 2 = L / 2 + 1 by omega, sumTo_succ_left, hsh, Nat.add_zero]
    rw [e1, e2, ih, hends, show (L + 2) % 2 = L % 2 by omega, show (L + 2) / 2 = L / 2 + 1 by omega,
      show lo + (L / 2 + 1) = lo + 1 + L / 2 by omega]
    omega

/-- `iy = MP_MIN(iy, ((ty - tx) + 1) >> 1)`: half the window. -/
def combaIyS (ua k : Nat) : Nat := min (combaIy ua ua k) ((combaTy ua k - combaTx ua k + 1) / 2)

/-- Column `k` of `a²` as `s_mp_sqr_fast` computes it: twice the half window, plus the
square of the middle digit in even columns. -/
def colS (da : Nat → Nat) (ua k : Nat) : Nat :=
  2 * combaPart da da ua k (combaIyS ua k) + (if k % 2 = 0 then da (k / 2) * da (k / 2) else 0)

/-- The squaring column is the column of `a * a`. -/
theorem colS_eq (da : Nat → Nat) (ua k : Nat) (hua : 1 ≤ ua) (hk : k < 2 * ua) :
    colS da ua k = col da da ua ua k := by
  rw [← colC_eq da da ua ua k hua]
  unfold colS colC combaPart combaIyS
  have hty : combaTx ua k + combaTy ua k = k := by unfold combaTx combaTy; omega
  by_cases hlast : k + 1 = 2 * ua
  · -- the top (odd) column is empty
    have hiy : combaIy ua ua k = 0 := by unfold combaIy combaTx combaTy; omega
    rw [hiy, show k % 2 = 1 by omega]
    simp [sumTo]
  · have hiy : 2 * combaTx ua k + combaIy ua ua k = k + 1 := by unfold combaIy combaTx combaTy; omega
    have hhalf : (combaTy ua k - combaTx ua k + 1) / 2 = combaIy ua ua k / 2 := by omega
    rw [hhalf, show min (combaIy ua ua k) (combaIy ua ua k / 2) = combaIy ua ua k / 2 by omega]
    -- the terms as `g (tx + iz)` with `g i = da i * da (k - i)`
    have hg : ∀ n, n ≤ combaIy ua ua k →
        sumTo (fun iz => da (combaTx ua k + iz) * da (combaTy ua k - iz)) n =
          sumTo (fun iz => (fun i => da i * da (k - i)) (combaTx ua k + iz)) n :=
      fun n hn => sumTo_congr n (fun iz hiz => by
        show _ = da (combaTx ua k + iz) * da (k - (combaTx ua k + iz))
        rw [show k - (combaTx ua k + iz) = combaTy ua k - iz by omega])
    rw [hg _ (Nat.le_refl _), hg _ (Nat.div_le_self _ _)]
    rw [sumTo_sym (fun i => da i * da (k - i)) (combaIy ua ua k) _ (fun iz hiz => by
      rw [show k - (combaTx ua k + (combaIy ua ua k - 1 - iz)) = combaTx ua k + iz by omega,
        show k - (combaTx ua k + iz) = combaTx ua k + (combaIy ua ua k - 1 - iz) by omega, Nat.mul_comm])]
    by_cases hev : k % 2 = 0
    · rw [if_pos hev, if_pos (by omega)]
      rw [show combaTx ua k + combaIy ua ua k / 2 = k / 2 by omega, show k - k / 2 = k / 2 by omega]
    · rw [if_neg hev, if_neg (by omega)]

theorem combaW_congr {cl cl' : Nat → Nat} : ∀ n, (∀ k, k < n → cl k = cl' k) → combaW cl n = combaW cl' n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [combaW, combaW_congr n (fun k hk => h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]

theorem combaD_congr {cl cl' : Nat → Nat} {k : Nat} (h : ∀ j, j ≤ k → cl j = cl' j) :
    combaD cl k = combaD cl' k := by
  unfold combaD; rw [combaW_congr k (fun j hj => h j (by omega)), h k (Nat.le_refl _)]

/-- `s_mp_sqr_fast(a, b)` leaves what `s_mp_mul_digs_fast(a, a, b, 2 a.used)` would:
its comba digits over `colS` are those over `col a a` (`colS_eq`, `combaD_congr`). -/
abbrev SqrFastPost (a b b' : MpInt) : Prop := MulFastPost a a b b' (a.used + a.used)

theorem sqrFast_digit (a : MpInt) (hua : 1 ≤ a.used) (k : Nat) (hk : k < a.used + a.used) :
    combaD (colS a.digit a.used) k = combaD (col a.digit a.digit a.used a.used) k :=
  combaD_congr fun j hj => colS_eq a.digit a.used j hua (by omega)

/-- `s_mp_sqr_fast` computes `|b| = |a|²` and leaves `b` valid. -/
theorem SqrFastPost.spec {a b b' : MpInt} (ha : a.Shape) (hroom : a.used + a.used ≤ b.alloc)
    (hc : b.alloc < 2 ^ 31) (hsign : b.sign = Layout.mpZpos ∨ b.sign = Layout.mpNeg) (h : SqrFastPost a b b') :
    b'.Valid ∧ b'.mag = a.mag * a.mag := by
  have := MulFastPost.spec ha.toShapeU ha.toShapeU hroom hc hsign h
  exact ⟨this.1, this.2.2 (Nat.le_refl _)⟩

end Tom
