import Tom.Spec.Div2d

/-!
# Division by a digit: `mp_div_d` and `s_mp_div_3`

`mp_div_d(a, v, c, d)` (`bn_mp_div_d.c`, `0 < v < radix`) has four paths:

| condition (in order) | C | quotient `c` | remainder `*d` |
|---|---|---|---|
| `v == 0` | `return MP_VAL` | — | — |
| `v == 1` or `a == 0` | `mp_copy(a, c)` | `a` | `0` |
| `(v & (v - 1)) == 0` | `mp_div_2d(a, ix, c, NULL)`, `v = 1 << ix` | `Div2dPost` | `a->dp[0] & (v - 1)` |
| `v == 3` | `s_mp_div_3(a, c, d)` | long division | long division |
| otherwise | the digit loop below | long division | long division |

The long division (both `s_mp_div_3` and the digit loop) runs from the top digit
down with an `mp_word` remainder `w < v`: `w = (w << 28) | a->dp[ix]`, then the
digit `w / v` and the new remainder `w % v`. `ldR da v n i` is the remainder carried
into position `i` (`w` before iteration `ix = i - 1`; `ldR_top`: `0` at the start,
`ldR_step`: one iteration) and `ldQ da v n i` the quotient digit at `i`;
`natUpTo_ldQ`: the digits are `|a| / v`, `ldR_zero`: the last remainder is `|a| % v`.

* The digit loop computes `t = w / v` by `__udivdi3` and `w -= t * v` by `__muldi3`
  when `w ≥ v` (else `t = 0`): `ldStep_div_lt`, `ldStep_sub_c`, `ldStep_lt64`,
  `shiftOr_digit_c`.
* `s_mp_div_3` multiplies by the reciprocal `b = 2^28 / 3` (`div3_recip`):
  `t = (w * b) >> 28`, `w -= 3 t`, then `while (w >= 3) { t++; w -= 3; }`;
  `div3Est_c`: `3 t ≤ w < 3 t + 6` and no overflow, so the fix-up loop runs at most
  once; `repSub_spec`: on exit `t = w / 3` and `w = w % 3`.

Both leave the quotient `q` from `mp_init_size(&q, a->used)` (`alloc = max 3 used`,
`MP_MIN_PREC = 3`), `q.used = a->used`, `q.sign = a->sign`, then `mp_clamp(&q)` and
`mp_exch(&q, c)`. The remainder is `|a| mod v` also for negative `a` (it is an
`mp_digit`): `mp_div_d(-7, 2)` gives `c = -3`, `*d = 1`. The quotient truncates
toward zero.

The `…Quot` and `…Rem` structures are what the C leaves through a non-`NULL` `c` and
`d` (each output separately, so a call with one of them `NULL` meets the other).
-/

namespace Tom

open MpInt

/-! ## Signed values -/

/-- The value of sign `s` and magnitude `m` (`MpInt.val`). -/
def sval (s m : Nat) : Int := if s = Layout.mpNeg then -(m : Int) else m

theorem MpInt.val_sval (a : MpInt) : a.val = sval a.sign a.mag := rfl

/-- Truncated division of a signed value by a positive number. -/
theorem sval_tdiv (s m v : Nat) : (sval s m).tdiv (v : Int) = sval s (m / v) := by
  unfold sval; split
  · rw [Int.neg_tdiv, ← Int.ofNat_tdiv]
  · rw [← Int.ofNat_tdiv]

/-! ## Long division by a digit -/

theorem natUpTo_cons (f : Nat → Nat) (m : Nat) :
    natUpTo f (m + 1) = f 0 + radix * natUpTo (fun j => f (j + 1)) m := by
  rw [Nat.add_comm m 1, natUpTo_split f 1 m]
  simp only [natUpTo, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.pow_one]
  rw [show (fun i => f (1 + i)) = (fun j => f (j + 1)) from funext fun j => by rw [Nat.add_comm]]

/-- The value of the digits from position `i` up (of `n`). -/
def ldV (da : Nat → Nat) (n i : Nat) : Nat := natUpTo (fun j => da (i + j)) (n - i)

/-- The remainder carried into position `i`. -/
def ldR (da : Nat → Nat) (v n i : Nat) : Nat := ldV da n i % v

/-- The quotient digit at position `i`: `(w * radix + a[i]) / v` with `w` the
remainder carried in. -/
def ldQ (da : Nat → Nat) (v n i : Nat) : Nat := (ldR da v n (i + 1) * radix + da i) / v

theorem ldV_cons (da : Nat → Nat) {n i : Nat} (hi : i < n) : ldV da n i = da i + radix * ldV da n (i + 1) := by
  unfold ldV
  rw [show n - i = (n - (i + 1)) + 1 by omega, natUpTo_cons]
  simp only [Nat.add_zero]
  rw [show (fun j => da (i + (j + 1))) = (fun j => da (i + 1 + j)) from funext fun j => by
    congr 1; omega]

/-- Before the loop: `w = 0`. -/
theorem ldR_top (da : Nat → Nat) (v n : Nat) : ldR da v n n = 0 := by
  simp [ldR, ldV, natUpTo]

theorem ldR_lt (da : Nat → Nat) {v : Nat} (hv : 0 < v) (n i : Nat) : ldR da v n i < v := Nat.mod_lt _ hv

/-- One iteration: the remainder out of position `i` is `(w * radix + a[i]) % v`. -/
theorem ldR_step (da : Nat → Nat) (v : Nat) {n i : Nat} (hi : i < n) :
    ldR da v n i = (ldR da v n (i + 1) * radix + da i) % v := by
  unfold ldR
  rw [ldV_cons da hi]
  generalize ldV da n (i + 1) = V
  have e := Nat.mod_add_div V v
  calc (da i + radix * V) % v = ((V % v * radix + da i) + v * (radix * (V / v))) % v := by
        congr 1
        conv => lhs; rw [← e]
        rw [Nat.mul_add, Nat.mul_comm radix (V % v), Nat.mul_left_comm radix v]; omega
    _ = (V % v * radix + da i) % v := Nat.add_mul_mod_self_left _ _ _

/-- After the loop: the remainder is `|a| % v`. -/
theorem ldR_zero (da : Nat → Nat) (v n : Nat) : ldR da v n 0 = natUpTo da n % v := by
  simp [ldR, ldV]

theorem ldQ_lt (da : Nat → Nat) {v : Nat} (hv : 0 < v) (n i : Nat) (hd : da i < radix) : ldQ da v n i < radix := by
  unfold ldQ
  have hr := ldR_lt da hv n (i + 1)
  rw [Nat.div_lt_iff_lt_mul hv]
  have : (ldR da v n (i + 1) + 1) * radix ≤ v * radix := Nat.mul_le_mul_right _ hr
  rw [Nat.succ_mul] at this
  rw [Nat.mul_comm radix v]; omega

/-- **Long division**: the quotient digits are `|a| / v`. -/
theorem natUpTo_ldQ (da : Nat → Nat) {v : Nat} (hv : 0 < v) (n : Nat) :
    natUpTo (ldQ da v n) n = natUpTo da n / v := by
  have key : ∀ m i, i + m = n → natUpTo (fun j => ldQ da v n (i + j)) m = ldV da n i / v := by
    intro m
    induction m with
    | zero => intro i hi; subst hi; simp [natUpTo, ldV]
    | succ m ih =>
      intro i hi
      rw [natUpTo_cons, ldV_cons da (by omega)]
      have ih' := ih (i + 1) (by omega)
      rw [show (fun j => ldQ da v n (i + (j + 1))) = (fun j => ldQ da v n (i + 1 + j)) by
        funext j; congr 1; omega, ih']
      simp only [Nat.add_zero]
      unfold ldQ ldR
      generalize ldV da n (i + 1) = V
      have e := Nat.mod_add_div V v
      have : da i + radix * V = (V % v * radix + da i) + v * (radix * (V / v)) := by
        conv => lhs; rw [← e]
        rw [Nat.mul_add, Nat.mul_comm radix (V % v), Nat.mul_left_comm radix v]; omega
      rw [this, Nat.add_mul_div_left _ _ hv]
  have := key n 0 (Nat.zero_add n)
  simp only [Nat.zero_add] at this
  rw [this]; simp [ldV]

/-! ## The C's steps -/

/-- `w = (w << MP_DIGIT_BIT) | a->dp[ix]` is `w * radix + a[ix]`. -/
theorem shiftOr_digit_c (w d : Nat) (hd : d < radix) : (w <<< Layout.digitBits) ||| d = w * radix + d := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hd, Nat.shiftLeft_eq]

/-- The `mp_word` does not overflow: `w < v < 2^32` gives `w * radix + d < 2^60`. -/
theorem ldStep_lt64 {w d v : Nat} (hw : w < v) (hv : v ≤ 2 ^ 32) (hd : d < radix) :
    w * radix + d < 2 ^ 64 := by
  have : (w + 1) * radix ≤ 2 ^ 32 * radix := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at this
  simp only [radix_eq] at this hd ⊢
  omega

/-- The digit `t = w / v` fits in an `mp_digit` (below the radix). -/
theorem ldStep_div_lt {w d v : Nat} (hw : w < v) (hd : d < radix) : (w * radix + d) / v < radix := by
  have hv : 0 < v := by omega
  rw [Nat.div_lt_iff_lt_mul hv]
  have : (w + 1) * radix ≤ v * radix := Nat.mul_le_mul_right _ hw
  rw [Nat.succ_mul] at this
  rw [Nat.mul_comm radix v]; omega

/-- `w -= (mp_word)t * (mp_word)b` (no wrap) leaves `w % v`. -/
theorem ldStep_sub_c (W v : Nat) : W / v * v ≤ W ∧ W - W / v * v = W % v := by
  have := Nat.div_add_mod W v
  rw [Nat.mul_comm] at this
  constructor <;> omega

/-- The `w < v` branch (`t = 0`, `w` unchanged) is the same step. -/
theorem ldStep_small {W v : Nat} (h : W < v) : W / v = 0 ∧ W % v = W :=
  ⟨Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h⟩

/-- Repeated subtraction: if `k` subtractions of `Y` took `A` to `x < Y`, then
`k = A / Y` and `x = A % Y` (`s_mp_div_3`'s fix-up loop, `mp_div`'s first loop). -/
theorem repSub_spec {x k Y A : Nat} (h : x + k * Y = A) (hx : x < Y) : k = A / Y ∧ x = A % Y := by
  have hY : 0 < Y := by omega
  subst h
  rw [Nat.mul_comm, Nat.add_mul_div_left _ _ hY, Nat.div_eq_of_lt hx, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  exact ⟨rfl, rfl⟩

/-- `b = ((mp_word)1 << MP_DIGIT_BIT) / 3`. -/
theorem div3_recip : (1 <<< Layout.digitBits) / 3 = 89478485 := by decide

/-- `s_mp_div_3`'s estimate `t = (w * b) >> MP_DIGIT_BIT` for `w < 3 * radix`: the
product fits in an `mp_word`, `w - 3t` does not wrap and is below `6`. -/
theorem div3Est_c {W : Nat} (hW : W < 3 * radix) :
    W * 89478485 < 2 ^ 64 ∧ 3 * ((W * 89478485) >>> Layout.digitBits) ≤ W ∧
      W < 3 * ((W * 89478485) >>> Layout.digitBits) + 6 := by
  rw [Nat.shiftRight_eq_div_pow]
  simp only [radix_eq, digitBits_eq] at hW ⊢
  have h1 := Nat.div_add_mod (W * 89478485) (2 ^ 28)
  have h2 := Nat.mod_lt (W * 89478485) (show 0 < 2 ^ 28 by decide)
  generalize W * 89478485 / 2 ^ 28 = t0 at *
  generalize W * 89478485 % 2 ^ 28 = r at *
  simp only [Nat.reducePow] at h1 h2 ⊢
  have h3 : 268435456 * (3 * t0) ≤ 268435456 * W := by omega
  have h4 : 268435456 * W < 268435456 * (3 * t0 + 6) := by omega
  exact ⟨by omega, Nat.le_of_mul_le_mul_left h3 (by decide), Nat.lt_of_mul_lt_mul_left h4⟩

/-- `s_mp_div_3`'s step: from `w < 3`, `w * radix + d < 3 * radix`. -/
theorem div3_window {w d : Nat} (hw : w < 3) (hd : d < radix) : w * radix + d < 3 * radix := by
  have : (w + 1) * radix ≤ 3 * radix := Nat.mul_le_mul_right _ hw
  rw [Nat.succ_mul] at this; omega

/-! ## Powers of two -/

/-- `(b & (b - 1)) == 0` with `b > 0` means `b = 2^ix`, `ix = log2 b`. -/
theorem pow2_of_and {v : Nat} (hv : 0 < v) (h : v &&& (v - 1) = 0) : v = 2 ^ Nat.log2 v := by
  have h1 := Nat.log2_self_le (Nat.ne_of_gt hv)
  have h2 := Nat.lt_log2_self (n := v)
  generalize Nat.log2 v = k at h1 h2
  rcases Nat.lt_or_eq_of_le h1 with hlt | heq
  · exfalso
    obtain ⟨r, rfl⟩ : ∃ r, v = 2 ^ k + r := ⟨v - 2 ^ k, by omega⟩
    have hr : r < 2 ^ k := by rw [Nat.pow_succ] at h2; omega
    have e1 : (2 ^ k + r).testBit k = true := by
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr]; rfl
    have e2 : (2 ^ k + r - 1).testBit k = true := by
      rw [show 2 ^ k + r - 1 = 2 ^ k + (r - 1) by omega, Nat.testBit_two_pow_add_eq,
        Nat.testBit_lt_two_pow (by omega)]; rfl
    have := Nat.testBit_and (2 ^ k + r) (2 ^ k + r - 1) k
    rw [h, Nat.zero_testBit, e1, e2] at this
    exact absurd this (by decide)
  · exact heq.symm

theorem and_pow2 (k : Nat) : 2 ^ k &&& (2 ^ k - 1) = 0 := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]

/-- `mp_div_d`'s loop `while ((ix < MP_DIGIT_BIT) && (b != 1 << ix)) ix++` finds
`ix = log2 b`. -/
theorem log2_pow2 (k : Nat) : Nat.log2 (2 ^ k) = k := Nat.log2_two_pow

/-- `|a| mod 2^k` is digit `0` mod `2^k` (`*d = a->dp[0] & (b - 1)`). -/
theorem mag_mod_pow2 {a : MpInt} (ha : a.Shape) {k : Nat} (hk : k ≤ Layout.digitBits) :
    a.digit 0 &&& (2 ^ k - 1) = a.mag % 2 ^ k := by
  rw [Nat.and_two_pow_sub_one_eq_mod, ha.digit_eq]
  unfold natDigit
  rw [Nat.pow_zero, Nat.div_one, Nat.mod_mod_of_dvd _ (two_pow_dvd_radix hk)]

/-! ## The contracts -/

/-- `mp_copy(a, c)` of a valid `a` (`used = a->used`, `sign = a->sign`, `a`'s digits)
is a `ClampedTo` result. -/
theorem ClampedTo.of_copy {a c' : MpInt} {al : Nat} (ha : a.Valid) (halloc : c'.alloc = al)
    (hlen : c'.digits.length = al) (hdig : c'.digit = a.digit) (hused : c'.used = a.used)
    (hsign : c'.sign = a.sign) : ClampedTo c' al a.digit a.used a.sign := by
  refine ⟨halloc, hlen, hdig, by rw [hused, ha.clampUsed_self], ?_⟩
  rw [hsign, hused]
  split
  · exact ha.zero_pos (by assumption)
  · rfl

/-- The quotient digits of the long division of `a` by `v`. -/
def divDDigit (a : MpInt) (v : Nat) (i : Nat) : Nat := if i < a.used then ldQ a.digit v a.used i else 0

/-- What the long division (`s_mp_div_3`, or `mp_div_d`'s loop) leaves in `c`. -/
def DivLongQuot (a : MpInt) (v : Nat) (c' : MpInt) : Prop :=
  ClampedTo c' (max 3 a.used) (divDDigit a v) a.used a.sign

/-- What `mp_div_d(a, v, c, d)` leaves in `c` (non-`NULL`), by path. The copy path
assumes `c->alloc ≥ a->used` (D5). -/
structure DivDQuot (a : MpInt) (v : Nat) (c c' : MpInt) : Prop where
  copy : (v = 1 ∨ a.used = 0) → ClampedTo c' c.alloc a.digit a.used a.sign
  pow2 : v ≠ 1 → a.used ≠ 0 → v &&& (v - 1) = 0 → Div2dPost a (Nat.log2 v) c c'
  long : v ≠ 1 → a.used ≠ 0 → v &&& (v - 1) ≠ 0 → DivLongQuot a v c'

/-- What `mp_div_d(a, v, c, d)` stores in `*d` (non-`NULL`), by path. -/
structure DivDRem (a : MpInt) (v : Nat) (d' : Nat) : Prop where
  copy : (v = 1 ∨ a.used = 0) → d' = 0
  pow2 : v ≠ 1 → a.used ≠ 0 → v &&& (v - 1) = 0 → d' = a.digit 0 &&& (2 ^ Nat.log2 v - 1)
  long : v ≠ 1 → a.used ≠ 0 → v &&& (v - 1) ≠ 0 → d' = ldR a.digit v a.used 0

/-- `s_mp_div_3(a, c, d)`: the long division by `3`. -/
def Div3Quot (a c' : MpInt) : Prop := DivLongQuot a 3 c'

/-- `s_mp_div_3(a, c, d)` stores the last remainder in `*d`. -/
def Div3Rem (a : MpInt) (d' : Nat) : Prop := d' = ldR a.digit 3 a.used 0

theorem divDDigit_lt (a : MpInt) (ha : a.Shape) {v : Nat} (hv : 0 < v) (i : Nat) : divDDigit a v i < radix := by
  unfold divDDigit; split
  · exact ldQ_lt _ hv _ _ (ha.digit_lt i)
  · exact radix_pos

/-- The long division computes `|c| = |a| / v`, `c = a / v` truncated. -/
theorem DivLongQuot.spec {a c' : MpInt} {v : Nat} (ha : a.Valid) (hv : 0 < v) (h : DivLongQuot a v c') :
    c'.Valid ∧ c'.mag = a.mag / v ∧ c'.val = a.val.tdiv v := by
  have hn : natUpTo (divDDigit a v) a.used = a.mag / v := by
    rw [natUpTo_congr _ (e := ldQ a.digit v a.used) (fun i hi => by simp [divDDigit, hi])]
    exact natUpTo_ldQ _ hv _
  have hal : max 3 a.used < 2 ^ 31 := by have := ha.alloc_lt; have := ha.used_le; omega
  obtain ⟨hv', hm, hval⟩ := ClampedTo.spec h (divDDigit_lt a ha.toShape hv)
    (fun i hi => by simp [divDDigit, show ¬ i < a.used by omega]) (Nat.le_max_right _ _) hal ha.sign_ok
  rw [hn] at hm hval
  exact ⟨hv', hm, by rw [hval, MpInt.val_sval, sval_tdiv]; rfl⟩

/-- The long division's remainder is `|a| % v`. -/
theorem ldR_mag (a : MpInt) (v : Nat) : ldR a.digit v a.used 0 = a.mag % v := ldR_zero _ _ _

/-- `mp_div_d` computes `|c| = |a| / v` and `c = a / v` truncated toward zero. -/
theorem DivDQuot.spec {a c c' : MpInt} {v : Nat} (ha : a.Valid) (hv : 0 < v)
    (hroom : a.used ≤ c.alloc) (hc : c.alloc < 2 ^ 31) (h : DivDQuot a v c c') :
    c'.Valid ∧ c'.mag = a.mag / v ∧ c'.val = a.val.tdiv v := by
  by_cases h1 : v = 1 ∨ a.used = 0
  · obtain ⟨hv', hm, hval⟩ := ClampedTo.spec (h.copy h1) ha.digit_lt ha.high_zero hroom hc ha.sign_ok
    have hq : a.mag / v = a.mag := by
      rcases h1 with h1 | h1
      · rw [h1, Nat.div_one]
      · rw [MpInt.mag_used_zero h1, Nat.zero_div]
    refine ⟨hv', ?_, ?_⟩
    · rw [hm, hq]; rfl
    · rw [hval, MpInt.val_sval, sval_tdiv, hq]; rfl
  · have hv1 : v ≠ 1 := fun e => h1 (Or.inl e)
    have hu : a.used ≠ 0 := fun e => h1 (Or.inr e)
    by_cases h2 : v &&& (v - 1) = 0
    · have hp := pow2_of_and hv h2
      obtain ⟨hv', hm, hval⟩ := Div2dPost.spec ha hroom hc (h.pow2 hv1 hu h2)
      rw [← hp] at hm hval
      exact ⟨hv', hm, by rw [hval, MpInt.val_sval, sval_tdiv]; rfl⟩
    · exact DivLongQuot.spec ha hv (h.long hv1 hu h2)

/-- `mp_div_d` stores `|a| % v` in `*d` (for negative `a` too). -/
theorem DivDRem.spec {a : MpInt} {v d' : Nat} (ha : a.Valid) (hv : 0 < v) (hvr : v < radix)
    (h : DivDRem a v d') : d' = a.mag % v := by
  by_cases h1 : v = 1 ∨ a.used = 0
  · rw [h.copy h1]
    rcases h1 with h1 | h1
    · rw [h1, Nat.mod_one]
    · rw [MpInt.mag_used_zero h1, Nat.zero_mod]
  · have hv1 : v ≠ 1 := fun e => h1 (Or.inl e)
    have hu : a.used ≠ 0 := fun e => h1 (Or.inr e)
    by_cases h2 : v &&& (v - 1) = 0
    · have hp := pow2_of_and hv h2
      have hk : Nat.log2 v ≤ Layout.digitBits := by
        have : 2 ^ Nat.log2 v < 2 ^ (Layout.digitBits + 1) := by
          rw [← hp]; exact Nat.lt_of_lt_of_le hvr (Nat.pow_le_pow_right (by decide) (by omega))
        exact Nat.lt_succ_iff.1 ((Nat.pow_lt_pow_iff_right (by decide)).1 this)
      rw [h.pow2 hv1 hu h2, mag_mod_pow2 ha.toShape hk, ← hp]
    · rw [h.long hv1 hu h2, ldR_mag]

/-- `s_mp_div_3` computes `c = a / 3` truncated and `*d = |a| % 3`. -/
theorem Div3Quot.spec {a c' : MpInt} (ha : a.Valid) (h : Div3Quot a c') :
    c'.Valid ∧ c'.mag = a.mag / 3 ∧ c'.val = a.val.tdiv 3 :=
  DivLongQuot.spec ha (by decide) h

theorem Div3Rem.spec {a : MpInt} {d' : Nat} (h : Div3Rem a d') : d' = a.mag % 3 := by
  rw [h, ldR_mag]

end Tom
