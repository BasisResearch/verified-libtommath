import Tom.Spec.DivD

/-!
# `mp_div`'s long division: the quotient digit loop

The image compiles the normalised long division of `bn_mp_div.c` (HAC 14.20, Knuth's
Algorithm D, TAOCP vol. 2 §4.3.1), not `BN_MP_DIV_SMALL`: `tommath_superclass.h`
defines `LTM_ALL` and leaves `SC_RSA_1` (which would define `BN_MP_DIV_SMALL`)
commented out, `c/Makefile` passes only `-DMP_32BIT`, and `mp_div` @0x80000898 (370
instructions, `experiments/disasm.txt`) calls `mp_init_size`, `mp_lshd`, `mp_rshd`,
`mp_mul_2d`, `mp_mul_d`, `mp_div_2d` and `__udivdi3` (the bit-by-bit variant calls none
of `mp_lshd`, `mp_mul_d`, `__udivdi3`).

With `A = |a| * 2^norm` (`x`) and `B = |b| * 2^norm` (`y`), `n = x.used - 1`,
`t = y.used - 1`, the C computes the quotient digits `q[n-t] … q[0]` of `A / B`:

* **Normalisation.** `norm = divNorm (mp_count_bits(y))` makes the top digit of
  `y` have exactly `MP_DIGIT_BIT - 1 = 27` bits: `2^26 ≤ y[t] < 2^27` (`divNorm_top`).
  (Not `≥ radix/2` as in Knuth: the comment's "y >= b/2" is not what the code does;
  the three-digit test below makes up for it.)
* **Step 2.** `y <<= (n-t)` digits; `while (x >= y) { q[n-t]++; x -= y; }`;
  `y >>= (n-t)` digits. `repSub_spec`: `q[n-t] = A / (B b^(n-t))`, `x = A % (B b^(n-t))`;
  `step2_lt`: at most `3` subtractions.
* **Step 3**, for `i = n … t+1`, position `k = i - t - 1`, `x < B b^(k+1)`:
  - `i > x.used`: skip (`knuth_skip`: the digit is `0`, `x` unchanged);
  - 3.1 the estimate `q̂₀ = knuthEst x[i] x[i-1] y[t]`
    (`b - 1` if `x[i] = y[t]`, else `min ((x[i] b + x[i-1]) / y[t]) (b - 1)` by `__udivdi3`);
  - 3.2 `do { q̂--; t1 = q̂ * (y[t] b + y[t-1]); t2 = x[i] b² + x[i-1] b + x[i-2]; }
    while (mp_cmp_mag(t1, t2) == MP_GT)`: `fixDown (knuthTest Y2 X3) q̂₀`. `t2` has
    `used = 3` without clamping, so `mp_cmp_mag` answers `MP_GT` only when also
    `t1 ≥ b²` (`knuthTest`, `cmpMag_three`); with `x[i] = 0` the test can stop early.
  - `knuthQhat_bounds`: `q ≤ q̂ ≤ q + 1` for the true digit `q = x / (B b^k)` (Knuth's
    Theorem B for the estimate, the three-digit test for the error; with `y[t] ≥ 2^26`
    and the early stop the bound still holds);
  - 3.3 `x -= q̂ * y * b^k` (`mp_mul_d`, `mp_lshd`, `mp_sub`), 3.4 if `x < 0`:
    `x += y * b^k`, `q̂--` (`addBack_spec`).
  `knuth_step`: the digit written is `x / (B b^k)`, the new `x` is `x % (B b^k)`.
* **The invariant** (`DivInv`): before iteration `i`, `x = A % (B b^(i-t))`, the digits
  of `q` at and above `i - t` are those of `A / B`, below are still `0`. `DivInv.init`
  (after step 2), `DivInv.step` (with `knuth_step` or `knuth_skip`), `DivInv.finish` (`i = t`: `x = A % B`,
  `q`'s digits are `natDigit (A / B)`).

The C quantities are stated on the values of `x` and `y` (`natDigit x i` is `x.dp[i]`
for a shaped `x`, `MpInt.Shape.digit_eq`); the callees (`mp_mul_d`, `mp_lshd`,
`mp_sub`, `mp_add`, `mp_copy`, `mp_cmp`, `mp_cmp_mag`) are used through their values.
The `mp_digit`/`mp_word` steps are `knuthEst_c`, `knuthStart_c`, `knuthDec_c`.
-/

namespace Tom

open MpInt

/-! ## Digits at the top -/

theorem div_top1 {N j : Nat} (h : N < radix ^ (j + 1)) : N / radix ^ j = natDigit N j := by
  rw [div_pow_succ, Nat.div_eq_of_lt h, Nat.mul_zero, Nat.add_zero]

theorem div_top2 {N j : Nat} (h : N < radix ^ (j + 2)) :
    N / radix ^ j = natDigit N (j + 1) * radix + natDigit N j := by
  rw [div_pow_succ, div_top1 (j := j + 1) h, Nat.mul_comm radix (natDigit N (j + 1))]; omega

theorem div_top3 {N j : Nat} (h : N < radix ^ (j + 3)) :
    N / radix ^ j = natDigit N (j + 2) * radix ^ 2 + natDigit N (j + 1) * radix + natDigit N j := by
  rw [div_pow_succ, div_top2 (j := j + 1) h, Nat.pow_two]
  show _ = natDigit N (j + 1 + 1) * (radix * radix) + _ + _
  rw [Nat.mul_add, Nat.mul_comm radix (natDigit N (j + 1 + 1) * radix), Nat.mul_assoc,
    Nat.mul_comm radix (natDigit N (j + 1))]
  omega

theorem div_bracket (X s : Nat) (hs : 0 < s) : X / s * s ≤ X ∧ X < (X / s + 1) * s :=
  ⟨Nat.div_mul_le_self X s, by rw [Nat.succ_mul]; exact Nat.lt_div_mul_add hs⟩

/-! ## Normalisation -/

/-- `norm` of `mp_div` from `cb = mp_count_bits(y)`: `(DIGIT_BIT - 1) - cb % DIGIT_BIT`
when that is positive, else `0`. -/
def divNorm (cb : Nat) : Nat :=
  if cb % Layout.digitBits < Layout.digitBits - 1 then Layout.digitBits - 1 - cb % Layout.digitBits else 0

theorem divNorm_lt (cb : Nat) : divNorm cb < Layout.digitBits := by
  unfold divNorm; split <;> simp only [digitBits_eq] at * <;> omega

theorem divNorm_mod (cb : Nat) : (cb + divNorm cb) % Layout.digitBits = Layout.digitBits - 1 := by
  unfold divNorm; split <;> simp only [digitBits_eq] at * <;> omega

theorem two_pow_lt_iff {m n : Nat} : 2 ^ m < 2 ^ n ↔ m < n := Nat.pow_lt_pow_iff_right (by decide)

/-- **Normalisation**: if `cb` is the bit count of `B0 > 0` (`mp_count_bits`), then
`B = B0 * 2^norm` with `t + 1` digits has its top digit in `[2^26, 2^27)`. -/
theorem divNorm_top {B0 cb t : Nat} (hcb : 1 ≤ cb) (h2 : B0 < 2 ^ cb) (h3 : 2 ^ (cb - 1) ≤ B0)
    (ht1 : radix ^ t ≤ B0 * 2 ^ divNorm cb) (ht2 : B0 * 2 ^ divNorm cb < radix ^ (t + 1)) :
    2 ^ 26 ≤ natDigit (B0 * 2 ^ divNorm cb) t ∧ natDigit (B0 * 2 ^ divNorm cb) t < 2 ^ 27 := by
  have hmod := divNorm_mod cb
  generalize divNorm cb = nm at hmod ht1 ht2 ⊢
  generalize hB : B0 * 2 ^ nm = B at ht1 ht2 ⊢
  have hlo : 2 ^ (cb - 1 + nm) ≤ B := by rw [← hB, Nat.pow_add]; exact Nat.mul_le_mul_right _ h3
  have hhi : B < 2 ^ (cb + nm) := by
    rw [← hB, Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
  rw [radix_pow_eq] at ht1 ht2
  simp only [digitBits_eq] at hmod ht1 ht2
  have e1 : 28 * t < cb + nm := two_pow_lt_iff.1 (Nat.lt_of_le_of_lt ht1 hhi)
  have e2 : cb - 1 + nm < 28 * (t + 1) := two_pow_lt_iff.1 (Nat.lt_of_le_of_lt hlo ht2)
  have hL : cb + nm = 28 * t + 27 := by omega
  rw [div_top1 (by rw [radix_pow_eq]; exact ht2) |>.symm, radix_pow_eq]
  simp only [digitBits_eq]
  constructor
  · rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hlo
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by decide) (by omega))

theorem natDigit_top_le {B t : Nat} : natDigit B t * radix ^ t ≤ B := by
  unfold natDigit
  exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mod_le _ _)) (Nat.div_mul_le_self _ _)

/-! ## Step 2 -/

/-- Step 2 subtracts `y * b^(n-t)` at most three times. -/
theorem step2_lt {A B n t : Nat} (hA : A < radix ^ (n + 1)) (hyt : 2 ^ 26 ≤ natDigit B t) (htn : t ≤ n) :
    A / (B * radix ^ (n - t)) < 4 := by
  have hB : 2 ^ 26 * radix ^ t ≤ B := Nat.le_trans (Nat.mul_le_mul_right _ hyt) natDigit_top_le
  have h1 : 2 ^ 26 * radix ^ n ≤ B * radix ^ (n - t) := by
    calc 2 ^ 26 * radix ^ n = 2 ^ 26 * radix ^ t * radix ^ (n - t) := by
          rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' htn]
      _ ≤ B * radix ^ (n - t) := Nat.mul_le_mul_right _ hB
  have hpos : 0 < B * radix ^ (n - t) :=
    Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.two_pow_pos _) (radix_pow_pos n)) h1
  rw [Nat.div_lt_iff_lt_mul hpos]
  calc A < radix ^ (n + 1) := hA
    _ = 4 * (2 ^ 26 * radix ^ n) := by rw [Nat.pow_succ, ← Nat.mul_assoc]; simp only [radix_eq]; omega
    _ ≤ 4 * (B * radix ^ (n - t)) := Nat.mul_le_mul_left _ h1

/-! ## Step 3.1–3.2: the estimate and the three-digit test -/

/-- Step 3.1: `q̂₀`. -/
def knuthEst (xi xi1 yt : Nat) : Nat :=
  if xi = yt then radix - 1 else min ((xi * radix + xi1) / yt) (radix - 1)

/-- `mp_cmp_mag(&t1, &t2) == MP_GT` for `t1 = q̂ * Y2` (clamped by `mp_mul_d`) and
`t2 = X3` (three digits, `used = 3`, not clamped). -/
def knuthTest (Y2 X3 q : Nat) : Bool := decide (radix ^ 2 ≤ q * Y2) && decide (X3 < q * Y2)

/-- The do-while of step 3.2: decrement while the test holds. -/
def fixDown (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | q + 1 => if p (q + 1) then fixDown p q else q + 1

/-- `Y2 = y[t] * b + y[t-1]` (`t1` before `mp_mul_d`; `y[-1]` read as `0`). -/
def knuthY2 (B t : Nat) : Nat := natDigit B t * radix + (if 1 ≤ t then natDigit B (t - 1) else 0)

/-- `X3 = x[i] * b² + x[i-1] * b + x[i-2]` (`t2`; `x[-1]` read as `0`). -/
def knuthX3 (x i : Nat) : Nat :=
  natDigit x i * radix ^ 2 + natDigit x (i - 1) * radix + (if 2 ≤ i then natDigit x (i - 2) else 0)

/-- `q̂` after step 3.2. -/
def knuthQhat (x B t i : Nat) : Nat :=
  fixDown (knuthTest (knuthY2 B t) (knuthX3 x i)) (knuthEst (natDigit x i) (natDigit x (i - 1)) (natDigit B t))

theorem fixDown_le (p : Nat → Bool) : ∀ q, fixDown p q ≤ q
  | 0 => Nat.le_refl 0
  | q + 1 => by
    simp only [fixDown]; split
    · exact Nat.le_succ_of_le (fixDown_le p q)
    · exact Nat.le_refl _

theorem fixDown_ge (p : Nat → Bool) {m : Nat} (hm : p m = false) : ∀ q, m ≤ q → m ≤ fixDown p q
  | 0, h => h
  | q + 1, h => by
    simp only [fixDown]
    rcases Nat.lt_or_eq_of_le h with h | h
    · split
      · exact fixDown_ge p hm q (by omega)
      · exact Nat.le_of_lt h
    · rw [← h, hm]; exact Nat.le_refl _

theorem fixDown_false (p : Nat → Bool) (h0 : p 0 = false) : ∀ q, p (fixDown p q) = false
  | 0 => h0
  | q + 1 => by
    simp only [fixDown]
    split
    · exact fixDown_false p h0 q
    · rename_i h; simpa using h

/-- The do-while stops when the test fails. -/
theorem fixDown_stop {p : Nat → Bool} {q : Nat} (h : p q = false) : fixDown p q = q := by
  cases q with
  | zero => rfl
  | succ q => simp [fixDown, h]

/-- The do-while decrements when the test holds. -/
theorem fixDown_dec {p : Nat → Bool} {q : Nat} (h : p q = true) (hq : 0 < q) : fixDown p q = fixDown p (q - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp [fixDown, h]

theorem knuthTest_zero (Y2 X3 : Nat) : knuthTest Y2 X3 0 = false := by
  simp [knuthTest, radix_eq]

/-- The test holds only for `q̂ > 0`, so `q̂ - 1` does not wrap. -/
theorem knuthTest_pos {Y2 X3 q : Nat} (h : knuthTest Y2 X3 q = true) : 0 < q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · rw [knuthTest_zero] at h; exact absurd h (by decide)
  · exact hq

theorem knuthEst_le (xi xi1 yt : Nat) : knuthEst xi xi1 yt ≤ radix - 1 := by
  unfold knuthEst; split
  · exact Nat.le_refl _
  · exact Nat.min_le_right _ _

/-- **The estimate's error**, on abstract windows: `X` the dividend window, `Y` the
divisor, `s = b^t`, `X2 = xi * b + xi1 = X / s`, `yt = Y / s`, `Y2 ≈ Y * b / s`,
`X3 ≈ X * b / s`. -/
theorem est_bounds {X Y s xi xi1 yt Y2 X3 : Nat} (hs : 0 < s) (hxi1 : xi1 < radix)
    (hX2a : (xi * radix + xi1) * s ≤ X) (hX2b : X < (xi * radix + xi1 + 1) * s)
    (hyta : yt * s ≤ Y) (hytb : Y < (yt + 1) * s)
    (hY2a : Y2 * s ≤ Y * radix) (hY2b : Y * radix < (Y2 + 1) * s)
    (hX3a : X3 * s < (X + 1) * radix) (hX3b : X * radix < (X3 + 1) * s)
    (hX3c : xi * radix ^ 2 ≤ X3) (hq : X < Y * radix) (hyt : radix ≤ yt * yt) :
    X / Y ≤ fixDown (knuthTest Y2 X3) (knuthEst xi xi1 yt) ∧
      fixDown (knuthTest Y2 X3) (knuthEst xi xi1 yt) ≤ X / Y + 1 := by
  have hyt1 : 1 ≤ yt := by
    rcases Nat.eq_zero_or_pos yt with h | h
    · rw [h] at hyt; simp [radix_eq] at hyt
    · exact h
  have hsY : s ≤ Y := Nat.le_trans (by simpa using Nat.mul_le_mul_right s hyt1) hyta
  have hY : 0 < Y := Nat.lt_of_lt_of_le hs hsY
  have hqY := Nat.div_mul_le_self X Y
  have hqr : X / Y < radix := (Nat.div_lt_iff_lt_mul hY).2 (by rw [Nat.mul_comm]; exact hq)
  have hq_yt : X / Y * yt ≤ xi * radix + xi1 := by
    have h1 : X / Y * yt * s ≤ X / Y * Y := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hyta
    have h2 : X / Y * yt * s < (xi * radix + xi1 + 1) * s := by omega
    exact Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_right h2)
  have hest_ge : X / Y ≤ knuthEst xi xi1 yt := by
    unfold knuthEst; split
    · omega
    · exact Nat.le_min.2 ⟨(Nat.le_div_iff_mul_le (by omega)).2 hq_yt, by omega⟩
  have hest_le := knuthEst_le xi xi1 yt
  have htq : knuthTest Y2 X3 (X / Y) = false := by
    have h1 : X / Y * Y2 * s ≤ X / Y * Y * radix := by
      rw [Nat.mul_assoc, Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hY2a
    have h2 : X / Y * Y * radix ≤ X * radix := Nat.mul_le_mul_right _ hqY
    have h3 : X / Y * Y2 * s < (X3 + 1) * s := by omega
    have h4 := Nat.lt_of_mul_lt_mul_right h3
    simp only [knuthTest, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt]
    exact Or.inr (by omega)
  generalize hqh : fixDown (knuthTest Y2 X3) (knuthEst xi xi1 yt) = qh
  have hqh_le : qh ≤ knuthEst xi xi1 yt := hqh ▸ fixDown_le _ _
  have hqh_f : knuthTest Y2 X3 qh = false := hqh ▸ fixDown_false _ (knuthTest_zero _ _) _
  refine ⟨hqh ▸ fixDown_ge _ htq _ hest_ge, ?_⟩
  suffices h : (qh - 1) * Y ≤ X by
    have := (Nat.le_div_iff_mul_le hY).2 h; omega
  by_cases hxi : xi = 0
  · subst hxi
    have hest : knuthEst 0 xi1 yt ≤ xi1 / yt := by
      unfold knuthEst; rw [if_neg (by omega)]; simp only [Nat.zero_mul, Nat.zero_add]
      exact Nat.min_le_left _ _
    simp only [Nat.zero_mul, Nat.zero_add] at hX2a
    generalize he : xi1 / yt = e at hest
    have hey : e * yt ≤ xi1 := he ▸ Nat.div_mul_le_self xi1 yt
    have hxi1' : xi1 < yt * yt := Nat.lt_of_lt_of_le hxi1 hyt
    have hey2 : e < yt := Nat.lt_of_mul_lt_mul_right (a := yt) (show e * yt < yt * yt by omega)
    refine Nat.le_trans (Nat.mul_le_mul_right _ (show qh - 1 ≤ e - 1 by omega)) ?_
    rcases Nat.lt_or_ge e 2 with he2 | he2
    · rw [show e - 1 = 0 by omega, Nat.zero_mul]; exact Nat.zero_le _
    · have hE1 : (e - 1) * Y < (e - 1) * ((yt + 1) * s) := Nat.mul_lt_mul_of_pos_left hytb (by omega)
      have hE2 : (e - 1) * (yt + 1) ≤ xi1 := by
        have h1 : (e - 1) * (yt + 1) = (e - 1) * yt + (e - 1) := by rw [Nat.mul_succ]
        have h2 : (e - 1) * yt + yt = e * yt := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
        omega
      have hE3 : (e - 1) * ((yt + 1) * s) ≤ xi1 * s := by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hE2
      omega
  · have hb2 : radix ^ 2 ≤ X3 :=
      Nat.le_trans (by simpa using Nat.mul_le_mul_right (radix ^ 2) (show 1 ≤ xi by omega)) hX3c
    have hle : qh * Y2 ≤ X3 := by
      simp only [knuthTest, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt, Nat.not_le] at hqh_f
      omega
    rcases Nat.eq_zero_or_pos qh with h0 | hpos
    · rw [h0]; simp
    · have h1 : qh * (Y * radix) < qh * ((Y2 + 1) * s) := Nat.mul_lt_mul_of_pos_left hY2b hpos
      have h2 : qh * ((Y2 + 1) * s) = qh * Y2 * s + qh * s := by
        rw [Nat.succ_mul, Nat.mul_add, Nat.mul_assoc]
      have h3 : qh * Y2 * s ≤ X3 * s := Nat.mul_le_mul_right _ hle
      have h4 : qh * s ≤ Y * radix := by
        calc qh * s ≤ radix * s := Nat.mul_le_mul_right _ (by omega)
          _ ≤ radix * Y := Nat.mul_le_mul_left _ hsY
          _ = Y * radix := Nat.mul_comm _ _
      have h5 : qh * Y * radix < (X + 1 + Y) * radix := by
        rw [Nat.mul_assoc, Nat.add_mul]; omega
      have h6 := Nat.lt_of_mul_lt_mul_right h5
      rw [Nat.sub_one_mul]; omega

theorem x3_t0 {X d2 d1 d0 : Nat} (hX : X = d2 * radix + d1) (hd0 : d0 < radix) :
    (d2 * radix ^ 2 + d1 * radix + d0) * radix ^ 0 < (X + 1) * radix ∧
      X * radix < (d2 * radix ^ 2 + d1 * radix + d0 + 1) * radix ^ 0 := by
  subst hX
  simp only [radix_eq, Nat.reducePow] at *
  constructor <;> omega

theorem knuthX3_eq {x j : Nat} (h : x < radix ^ (j + 3)) : knuthX3 x (j + 2) = x / radix ^ j := by
  unfold knuthX3
  rw [div_top3 h, show j + 2 - 1 = j + 1 by omega, show j + 2 - 2 = j by omega,
    if_pos (show 2 ≤ j + 2 by omega)]

/-- **Step 3.2's result**: `q ≤ q̂ ≤ q + 1` for the true digit `q = x / (B b^k)`, when
`x < B b^(k+1)` and `B` has `t + 1` digits with top digit `≥ 2^26`. -/
theorem knuthQhat_bounds {x B t k : Nat} (hB : B < radix ^ (t + 1)) (hyt : 2 ^ 26 ≤ natDigit B t)
    (hx : x < B * radix ^ (k + 1)) :
    x / (B * radix ^ k) ≤ knuthQhat x B t (t + k + 1) ∧
      knuthQhat x B t (t + k + 1) ≤ x / (B * radix ^ k) + 1 := by
  have hs := radix_pow_pos t
  have hk := radix_pow_pos k
  have hxi : x < radix ^ (t + k + 2) := by
    calc x < B * radix ^ (k + 1) := hx
      _ ≤ radix ^ (t + 1) * radix ^ (k + 1) := Nat.mul_le_mul_right _ (Nat.le_of_lt hB)
      _ = radix ^ (t + k + 2) := by rw [← Nat.pow_add]; congr 1; omega
  have hXdiv : x / radix ^ k / radix ^ t = x / radix ^ (t + k) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_comm k t]
  -- the windows
  have hX2 : x / radix ^ k / radix ^ t = natDigit x (t + k + 1) * radix + natDigit x (t + k) := by
    rw [hXdiv]; exact div_top2 hxi
  have hyt' : B / radix ^ t = natDigit B t := div_top1 hB
  have hq : x / radix ^ k < B * radix := by
    rw [Nat.div_lt_iff_lt_mul hk, Nat.mul_assoc, ← Nat.pow_succ']; exact hx
  have hytt : radix ≤ natDigit B t * natDigit B t := by
    have := Nat.mul_le_mul hyt hyt
    simp only [radix_eq] at this ⊢; omega
  -- Y2
  have hY2 : knuthY2 B t * radix ^ t ≤ B * radix ∧ B * radix < (knuthY2 B t + 1) * radix ^ t := by
    unfold knuthY2
    cases t with
    | zero =>
      simp only [Nat.pow_zero, Nat.mul_one, ite_false, show ¬ 1 ≤ 0 by omega, Nat.add_zero]
      rw [← hyt', Nat.pow_zero, Nat.div_one]; omega
    | succ t =>
      simp only [show 1 ≤ t + 1 by omega, ite_true, Nat.add_sub_cancel]
      rw [← div_top2 (j := t) hB, Nat.pow_succ]
      obtain ⟨h1, h2⟩ := div_bracket B (radix ^ t) (radix_pow_pos t)
      constructor
      · rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ h1
      · rw [← Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_right h2 radix_pos
  -- X3
  have hX3 : knuthX3 x (t + k + 1) * radix ^ t < (x / radix ^ k + 1) * radix ∧
      x / radix ^ k * radix < (knuthX3 x (t + k + 1) + 1) * radix ^ t := by
    cases t with
    | zero =>
      simp only [Nat.zero_add, Nat.pow_zero, Nat.div_one] at hX2 ⊢
      unfold knuthX3
      simp only [Nat.add_sub_cancel]
      exact x3_t0 hX2 (by split <;> first | exact natDigit_lt _ _ | exact radix_pos)
    | succ t =>
      have e : x / radix ^ k / radix ^ t = knuthX3 x (t + 1 + k + 1) := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_comm k t, show t + 1 + k + 1 = t + k + 2 by omega,
          knuthX3_eq (by rw [show t + k + 3 = t + 1 + k + 2 by omega]; exact hxi)]
      rw [← e, Nat.pow_succ]
      obtain ⟨h1, h2⟩ := div_bracket (x / radix ^ k) (radix ^ t) (radix_pow_pos t)
      constructor
      · rw [← Nat.mul_assoc]
        exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h1) (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) radix_pos)
      · rw [← Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_right h2 radix_pos
  have hX3c : natDigit x (t + k + 1) * radix ^ 2 ≤ knuthX3 x (t + k + 1) := by
    unfold knuthX3; omega
  obtain ⟨h2a, h2b⟩ := div_bracket (x / radix ^ k) (radix ^ t) hs
  obtain ⟨hya, hyb⟩ := div_bracket B (radix ^ t) hs
  rw [hX2] at h2a h2b
  rw [hyt'] at hya hyb
  have := est_bounds (X := x / radix ^ k) (Y := B) hs (natDigit_lt _ _) h2a h2b hya hyb hY2.1 hY2.2 hX3.1 hX3.2 hX3c hq hytt
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm (radix ^ k)] at this
  unfold knuthQhat
  rw [show t + k + 1 - 1 = t + k by omega]
  exact this

/-! ## Step 3.3–3.4: subtract and add back -/

/-- Subtracting `q̂ * D` and adding `D` back once if negative gives the true digit and
remainder when `q ≤ q̂ ≤ q + 1`. -/
theorem addBack_spec {x D qh : Nat} (hD : 0 < D) (h1 : x / D ≤ qh) (h2 : qh ≤ x / D + 1) :
    (if (x : Int) - ((qh * D : Nat) : Int) < 0 then qh - 1 else qh) = x / D ∧
    (if (x : Int) - ((qh * D : Nat) : Int) < 0 then (x : Int) - ((qh * D : Nat) : Int) + D
      else (x : Int) - ((qh * D : Nat) : Int)) = ((x % D : Nat) : Int) := by
  have e := Nat.div_add_mod x D
  have hm := Nat.mod_lt x hD
  generalize x / D = Q at e h1 h2
  generalize x % D = R at e hm
  rw [Nat.mul_comm] at e
  rcases Nat.lt_or_eq_of_le h2 with h | h
  · have hq : qh = Q := by omega
    subst hq
    have : ¬ ((x : Int) - ((qh * D : Nat) : Int) < 0) := by omega
    exact ⟨by rw [if_neg this], by rw [if_neg this]; omega⟩
  · subst h
    have hx : (Q + 1) * D = Q * D + D := Nat.succ_mul _ _
    have : (x : Int) - (((Q + 1) * D : Nat) : Int) < 0 := by omega
    exact ⟨by rw [if_pos this]; rfl, by rw [if_pos this]; omega⟩

/-- The digit `mp_div` writes at position `i - t - 1` (after step 3.4). -/
def knuthQd (x B t i : Nat) : Nat :=
  if (x : Int) - ((knuthQhat x B t i * (B * radix ^ (i - t - 1)) : Nat) : Int) < 0 then knuthQhat x B t i - 1
  else knuthQhat x B t i

/-- `x` after step 3.4. -/
def knuthXn (x B t i : Nat) : Int :=
  if (x : Int) - ((knuthQhat x B t i * (B * radix ^ (i - t - 1)) : Nat) : Int) < 0 then
    (x : Int) - ((knuthQhat x B t i * (B * radix ^ (i - t - 1)) : Nat) : Int) + ((B * radix ^ (i - t - 1) : Nat) : Int)
  else (x : Int) - ((knuthQhat x B t i * (B * radix ^ (i - t - 1)) : Nat) : Int)

/-- **One iteration of step 3**: the digit written is `x / (B b^k)` and the new `x` is
`x % (B b^k)`. -/
theorem knuth_step {x B t k : Nat} (hB : B < radix ^ (t + 1)) (hyt : 2 ^ 26 ≤ natDigit B t)
    (hx : x < B * radix ^ (k + 1)) :
    knuthQd x B t (t + k + 1) = x / (B * radix ^ k) ∧
      knuthXn x B t (t + k + 1) = ((x % (B * radix ^ k) : Nat) : Int) := by
  have hb := knuthQhat_bounds hB hyt hx
  have hBpos : 0 < B := Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.two_pow_pos 26) (radix_pow_pos t))
    (Nat.le_trans (Nat.mul_le_mul_right _ hyt) natDigit_top_le)
  have := addBack_spec (Nat.mul_pos hBpos (radix_pow_pos k)) hb.1 hb.2
  unfold knuthQd knuthXn
  rw [show t + k + 1 - t - 1 = k by omega]
  exact this

/-- Step 3 skips `i > x.used`: then `x < b^(i-1)`, the digit is `0` and `x` stays. -/
theorem knuth_skip {x B t k : Nat} (hBt : radix ^ t ≤ B) (hx : x < radix ^ (t + k)) :
    x / (B * radix ^ k) = 0 ∧ x % (B * radix ^ k) = x := by
  have : x < B * radix ^ k := by
    rw [Nat.pow_add] at hx; exact Nat.lt_of_lt_of_le hx (Nat.mul_le_mul_right _ hBt)
  exact ⟨Nat.div_eq_of_lt this, Nat.mod_eq_of_lt this⟩

/-! ## The `mp_digit` / `mp_word` steps of 3.1–3.2 -/

/-- Step 3.1 as the C computes it: `x[i] == y[t] ? MP_MASK : min(tmp, MP_MASK) & MP_MASK`
with `tmp = ((x[i] << 28) | x[i-1]) / y[t]` (`__udivdi3`; `x[i] b + x[i-1] < 2^56`). -/
theorem knuthEst_c (xi xi1 yt : Nat) (hxi : xi < radix) (hxi1 : xi1 < radix) :
    (if xi = yt then Layout.mpMask else
      (if ((xi <<< Layout.digitBits) ||| xi1) / yt > Layout.mpMask then Layout.mpMask
        else ((xi <<< Layout.digitBits) ||| xi1) / yt) &&& Layout.mpMask) = knuthEst xi xi1 yt ∧
    xi * radix + xi1 < 2 ^ 56 := by
  rw [shiftOr_digit_c _ _ hxi1, and_mpMask, mpMask_eq]
  unfold knuthEst
  refine ⟨?_, ?_⟩
  · split
    · rfl
    · split
      · rename_i h; rw [Nat.mod_eq_of_lt (by have := radix_pos; omega), Nat.min_eq_right (by omega)]
      · rename_i h; rw [Nat.mod_eq_of_lt (by have := radix_pos; omega), Nat.min_eq_left (by omega)]
  · have : (xi + 1) * radix ≤ radix * radix := Nat.mul_le_mul_right _ hxi
    rw [Nat.succ_mul] at this
    simp only [radix_eq, Nat.reducePow] at this hxi hxi1 ⊢; omega

/-- The do-while's start: `q = (q̂₀ + 1) & MP_MASK`, then `q = (q - 1) & MP_MASK` (in
`mp_word`) is `q̂₀` again, also for `q̂₀ = MP_MASK`. -/
theorem knuthStart_c (q : Nat) (hq : q < radix) :
    ((((q + 1) &&& Layout.mpMask) + 2 ^ 64 - 1) % 2 ^ 64) &&& Layout.mpMask = q := by
  rw [and_mpMask, and_mpMask]
  simp only [radix_eq, Nat.reducePow] at hq ⊢
  omega

/-- A later decrement `q = (q - 1) & MP_MASK` with `0 < q < radix` (the test held, so
`q > 0`: `knuthTest_pos`) is `q - 1`. -/
theorem knuthDec_c (q : Nat) (h0 : 0 < q) (hq : q < radix) : ((q + 2 ^ 64 - 1) % 2 ^ 64) &&& Layout.mpMask = q - 1 := by
  rw [and_mpMask]; simp only [radix_eq] at hq ⊢; omega

/-- `mp_cmp_mag(t1, t2)` for a valid `t1 < b^3` and a shaped `t2` with `used = 3`:
`MP_GT` exactly when `knuthTest` holds. -/
theorem cmpMag_three {t1 t2 : MpInt} (h1 : t1.Valid) (h1m : t1.mag < radix ^ 3) (h2 : t2.Shape)
    (hu : t2.used = 3) : cmpMag t1 t2 = .gt ↔ (radix ^ 2 ≤ t1.mag ∧ t2.mag < t1.mag) := by
  have hle : t1.used ≤ 3 := by
    rcases Nat.lt_or_ge 3 t1.used with h | h
    · have := MpInt.mag_ge h1 (by omega)
      have : radix ^ 3 ≤ radix ^ (t1.used - 1) := Nat.pow_le_pow_right radix_pos (by omega)
      omega
    · exact h
  unfold cmpMag
  rw [hu]
  rcases Nat.lt_or_eq_of_le hle with h | h
  · have hm := MpInt.mag_lt h1.toShape
    have : radix ^ t1.used ≤ radix ^ 2 := Nat.pow_le_pow_right radix_pos (by omega)
    simp only [show ¬ t1.used > 3 by omega, h, ite_true, ite_false]
    constructor
    · intro h; cases h
    · intro ⟨h', _⟩; omega
  · simp only [h, Nat.lt_irrefl, gt_iff_lt, ite_false]
    rw [cmpTop_eq _ _ h1.digit_lt h2.digit_lt]
    have e1 : natUpTo t1.digit 3 = t1.mag := by unfold MpInt.mag; rw [h]
    have e2 : natUpTo t2.digit 3 = t2.mag := by unfold MpInt.mag; rw [hu]
    rw [e1, e2, Nat.compare_eq_gt]
    have := MpInt.mag_ge h1 (by omega)
    rw [h] at this
    exact ⟨fun h' => ⟨this, h'⟩, fun h' => h'.2⟩

/-- Two digits `[d0, d1]` (`t1` before `mp_mul_d`) are `d0 + d1 b`. -/
theorem natUpTo_two (f : Nat → Nat) : natUpTo f 2 = f 1 * radix + f 0 := by
  simp only [natUpTo, Nat.pow_zero, Nat.pow_one, Nat.one_mul, Nat.zero_add]; rw [Nat.mul_comm radix]; omega

/-- `t1 = q̂ * Y2` has at most three digits (so `cmpMag_three` applies). -/
theorem knuthT1_lt (B t : Nat) {q : Nat} (hq : q < radix) : q * knuthY2 B t < radix ^ 3 := by
  have hY : knuthY2 B t < radix ^ 2 := by
    unfold knuthY2
    have h1 := natDigit_lt B t
    have h2 : (if 1 ≤ t then natDigit B (t - 1) else 0) < radix := by
      split
      · exact natDigit_lt _ _
      · exact radix_pos
    have : (natDigit B t + 1) * radix ≤ radix * radix := Nat.mul_le_mul_right _ h1
    rw [Nat.succ_mul] at this
    rw [Nat.pow_two]; omega
  calc q * knuthY2 B t < radix * radix ^ 2 := Nat.mul_lt_mul'' hq hY
    _ = radix ^ 3 := by rw [Nat.pow_succ radix 2, Nat.mul_comm]

/-- Step 3.3's subtrahend: `mp_mul_d(&y, q̂, &t1)` then `mp_lshd(&t1, k)` is `q̂ * (B b^k)`. -/
theorem knuth_t1_val (B q k : Nat) : B * q * radix ^ k = q * (B * radix ^ k) := by
  rw [Nat.mul_comm B q, Nat.mul_assoc]

/-- Three digits `[d0, d1, d2]` (`t2`) are `d0 + d1 b + d2 b²`. -/
theorem natUpTo_three (f : Nat → Nat) : natUpTo f 3 = f 2 * radix ^ 2 + f 1 * radix + f 0 := by
  simp only [natUpTo, Nat.pow_zero, Nat.pow_one, Nat.one_mul, Nat.zero_add]; rw [Nat.mul_comm (radix ^ 2),
    Nat.mul_comm radix]; omega

/-! ## The invariant of the main loop -/

/-- `qd` with digit `k` set to `v` (`q.dp[k] = v`). -/
def setDigit (qd : Nat → Nat) (k v : Nat) (j : Nat) : Nat := if j = k then v else qd j

/-- **The invariant** before iteration `i` of step 3 (and after step 2 with `i = n`):
`x` is `A` reduced modulo `B b^(i-t)`, the quotient digits at and above `i - t` are
final (those of `A / B`), the ones below are still `0` (`mp_init_size`'s zeros). -/
structure DivInv (A B t i x : Nat) (qd : Nat → Nat) : Prop where
  rem : x = A % (B * radix ^ (i - t))
  done : ∀ k, i - t ≤ k → qd k = natDigit (A / B) k
  todo : ∀ k, k < i - t → qd k = 0

theorem natDigit_quot_step {A D : Nat} (k : Nat) :
    A % (D * radix ^ (k + 1)) / (D * radix ^ k) = natDigit (A / D) k := by
  unfold natDigit
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul]

/-- After step 2 (`i = n`): `q[n-t] = A / (B b^(n-t))` (below `4`, `step2_lt`) and
`x = A % (B b^(n-t))`. -/
theorem DivInv.init {A B n t : Nat} (hA : A < radix ^ (n + 1)) (hBt : radix ^ t ≤ B) (htn : t ≤ n)
    (hlt : A / (B * radix ^ (n - t)) < radix) :
    DivInv A B t n (A % (B * radix ^ (n - t))) (fun j => if j = n - t then A / (B * radix ^ (n - t)) else 0) := by
  have hB : 0 < B := Nat.lt_of_lt_of_le (radix_pow_pos t) hBt
  have hQ : A / B < radix ^ (n - t + 1) := by
    rw [Nat.div_lt_iff_lt_mul hB]
    calc A < radix ^ (n + 1) := hA
      _ = radix ^ (n - t + 1) * radix ^ t := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ radix ^ (n - t + 1) * B := Nat.mul_le_mul_left _ hBt
  refine ⟨rfl, fun k hk => ?_, fun k hk => by simp [show k ≠ n - t by omega]⟩
  by_cases h : k = n - t
  · subst h
    simp only [ite_true]
    unfold natDigit
    rw [Nat.div_div_eq_div_mul, Nat.mod_eq_of_lt hlt]
  · simp only [h, ite_false]
    exact (natDigit_high hQ (by omega)).symm

/-- One iteration keeps the invariant: write digit `x / (B b^k)` at `k = i - t - 1`
and reduce `x` modulo `B b^k` (what `knuth_step` computes, or `knuth_skip`). -/
theorem DivInv.step {A B t i x : Nat} {qd : Nat → Nat} (h : DivInv A B t i x qd) (hti : t + 1 ≤ i) :
    DivInv A B t (i - 1) (x % (B * radix ^ (i - t - 1)))
      (setDigit qd (i - t - 1) (x / (B * radix ^ (i - t - 1)))) := by
  have hk : i - t = (i - t - 1) + 1 := by omega
  have hrem := h.rem
  rw [hk] at hrem
  refine ⟨?_, fun k hk' => ?_, fun k hk' => ?_⟩
  · rw [hrem, show i - 1 - t = i - t - 1 by omega]
    exact Nat.mod_mod_of_dvd _ (Nat.mul_dvd_mul_left _ (Nat.pow_dvd_pow _ (by omega)))
  · unfold setDigit
    split
    · rename_i he; subst he; rw [hrem]; exact natDigit_quot_step _
    · exact h.done k (by omega)
  · unfold setDigit
    rw [if_neg (by omega)]
    exact h.todo k (by omega)

/-- A skipped iteration (`i > x.used`) writes nothing: digit `k` is already `0`. -/
theorem setDigit_self {qd : Nat → Nat} {k v : Nat} (h : qd k = v) : setDigit qd k v = qd := by
  funext j; unfold setDigit; split
  · rename_i hj; rw [hj, h]
  · rfl

/-- After the loop (`i = t`): `x = A % B` and the digits of `q` are those of `A / B`. -/
theorem DivInv.finish {A B t x : Nat} {qd : Nat → Nat} (h : DivInv A B t t x qd) :
    x = A % B ∧ qd = natDigit (A / B) := by
  refine ⟨?_, funext fun k => h.done k (by omega)⟩
  have := h.rem
  rwa [Nat.sub_self, Nat.pow_zero, Nat.mul_one] at this

/-- The invariant bounds `x` as `knuth_step` needs. -/
theorem DivInv.rem_lt {A B t i x : Nat} {qd : Nat → Nat} (h : DivInv A B t i x qd) (hB : 0 < B) (hti : t + 1 ≤ i) :
    x < B * radix ^ ((i - t - 1) + 1) := by
  rw [h.rem, show i - t - 1 + 1 = i - t by omega]
  exact Nat.mod_lt _ (Nat.mul_pos hB (radix_pow_pos _))

/-! ## Undoing the normalisation -/

theorem norm_quot (a b m : Nat) (hm : 0 < m) : a * m / (b * m) = a / b := Nat.mul_div_mul_right _ _ hm

/-- The remainder of the normalised operands, shifted back (`mp_div_2d(&x, norm, &x, NULL)`). -/
theorem norm_rem (a b m : Nat) (hm : 0 < m) : a * m % (b * m) / m = a % b := by
  rw [Nat.mul_mod_mul_right, Nat.mul_div_cancel _ hm]

end Tom
