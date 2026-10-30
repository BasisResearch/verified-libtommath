import Tom.Spec.Mul

/-!
# Montgomery reduction (`bn_mp_montgomery_*.c`, `bn_s_mp_montgomery_reduce_fast.c`)

`MP_32BIT`: digits of 28 bits in `uint32_t`, `mp_word = uint64_t`, `radix = 2^28`.

* `mp_montgomery_setup(n, &rho)`: `rho = -1/n[0] mod radix` by Newton's iteration in
  `uint32_t` (`setupRho`; `setupRho_spec`: `(n0 * rho + 1) % radix = 0` for odd `n0`).
* `mp_montgomery_reduce(x, n, rho)` (row by row, carries propagated in place) and
  `s_mp_montgomery_reduce_fast(x, n, rho)` (comba columns `W[]` of `mp_word`, one
  carry fixed per row) compute the same numbers: row `j` adds `mu_j * n * radix^j` with
  `mu_j = (digit j of the running value) * rho mod radix` (`redcT`), then shift right by
  `n->used` digits and subtract `n` once if the result is not below `n` (`montOut`).
  `redc_spec`: for `x < n * R` (`R = radix ^ n->used`), the result `r` has `r < n` and
  `r * R ≡ x (mod n)`.
* `mp_montgomery_calc_normalization(a, b)`: `a = R mod b` by doubling with conditional
  subtraction (`normLoop`; `NormPost.spec`).

The loop models (`cstep`, `rowInner`, the propagation invariant, the `W[]` invariant of the
fast routine) are stated the way the C computes them, with the invariants a machine proof
carries through the loops.
-/

namespace Tom

open MpInt

namespace Mont

/-! ## Modular helpers -/

/-- `a ≡ 1 (mod M)` from an integer witness. -/
theorem natmod_one_of_int {a M : Nat} {Q : Int} (h : (a : Int) = 1 + M * Q) (hM : 1 < M) :
    a % M = 1 := by
  have h1 : ((a % M : Nat) : Int) = 1 := by
    rw [Int.natCast_emod, h, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by decide) (by omega)
  omega

/-- `a ≡ 0 (mod M)` from an integer witness. -/
theorem natmod_zero_of_int {a M : Nat} {Q : Int} (h : (a : Int) = M * Q) : a % M = 0 := by
  have h1 : ((a % M : Nat) : Int) = 0 := by
    rw [Int.natCast_emod, h, Int.mul_emod_right]
  omega

theorem mul_mod_mod_of_dvd {M N : Nat} (h : M ∣ N) (a b : Nat) : a * (b % N) % M = a * b % M := by
  rw [Nat.mul_mod, Nat.mod_mod_of_dvd _ h, ← Nat.mul_mod]

/-! ## `mp_montgomery_setup` -/

/-- One Newton step `x *= 2u - (b * x)` in `uint32_t`. -/
def newton (b x : Nat) : Nat := x * ((2 + 2 ^ 32 - b * x % 2 ^ 32) % 2 ^ 32) % 2 ^ 32

/-- The start `x = (((b + 2u) & 4u) << 1) + b` (no wrap: `b < 2^28`). -/
def setupX0 (b : Nat) : Nat := (((b + 2) &&& 4) <<< 1) + b

/-- `x` after the three Newton steps of `MP_32BIT` (`mod 2^8`, `2^16`, `2^32`). -/
def setupX (b : Nat) : Nat := newton b (newton b (newton b (setupX0 b)))

/-- `*rho = (mp_digit)(((mp_word)1 << MP_DIGIT_BIT) - x) & MP_MASK`: the subtraction in
`uint64_t`, the cast to `uint32_t`, the mask. -/
def setupRho (b : Nat) : Nat := (2 ^ 28 + 2 ^ 64 - setupX b) % 2 ^ 64 % 2 ^ 32 &&& Layout.mpMask

/-- The Newton step doubles the precision: `s ≡ 1 (mod K)` gives
`s * (2 - s) ≡ 1 (mod K^2)`, with `2 - s` taken in `uint32_t`-like wrap modulo `N`. -/
theorem newton_core (s K N : Nat) (hK : 1 < K) (hN : K * K ∣ N) (hN0 : 0 < N) (h : s % K = 1) :
    s * (2 + N - s % N) % (K * K) = 1 := by
  obtain ⟨c, hc⟩ := hN
  have hs := Nat.mod_add_div s K
  have hq := Nat.mod_add_div s N
  have hlt : s % N < N := Nat.mod_lt _ hN0
  rw [h] at hs
  apply natmod_one_of_int (Q := -(((s / K : Nat) : Int) * ((s / K : Nat) : Int)) +
    c * (s + (s : Int) * ((s / N : Nat) : Int))) _
    (Nat.lt_of_lt_of_le hK (Nat.le_mul_of_pos_left K (by omega)))
  have e : ((2 + N - s % N : Nat) : Int) = 2 + N - ((s % N : Nat) : Int) := by omega
  have e2 : ((s % N : Nat) : Int) = s - N * ((s / N : Nat) : Int) := by omega
  have e3 : (s : Int) = 1 + K * ((s / K : Nat) : Int) := by omega
  rw [Int.natCast_mul, e, e2, Int.natCast_mul, hc, Int.natCast_mul]
  generalize ((s / K : Nat) : Int) = m at *
  generalize ((s / N : Nat) : Int) = q at *
  rw [e3]
  grind

theorem newton_spec (b x k : Nat) (hk : 2 * k ≤ 32) (hk0 : 0 < k) (h : b * x % 2 ^ k = 1) :
    b * newton b x % 2 ^ (2 * k) = 1 := by
  have hd : 2 ^ (2 * k) ∣ 2 ^ 32 := Nat.pow_dvd_pow 2 hk
  unfold newton
  rw [mul_mod_mod_of_dvd hd, ← Nat.mul_assoc, mul_mod_mod_of_dvd hd]
  have := newton_core (b * x) (2 ^ k) (2 ^ 32) (Nat.one_lt_two_pow (by omega))
    (by rw [← Nat.pow_add, ← Nat.two_mul]; exact hd) (by decide) h
  rwa [← Nat.pow_add, ← Nat.two_mul] at this

/-- `n &&& 4` reads bit 2. -/
theorem and_four (n : Nat) : n &&& 4 = (n % 8) &&& 4 := by
  have h1 : (n &&& 4) % 2 ^ 3 = (n % 2 ^ 3) &&& (4 % 2 ^ 3) := Nat.and_mod_two_pow
  have h2 : n &&& 4 < 2 ^ 3 := Nat.and_lt_two_pow n (by decide)
  rw [Nat.mod_eq_of_lt h2] at h1
  exact h1

/-- The start is right modulo `2^4` for odd `b`. -/
theorem setupX0_spec (b : Nat) (hb : b % 2 = 1) : b * setupX0 b % 2 ^ 4 = 1 := by
  unfold setupX0
  rw [and_four, Nat.shiftLeft_eq, Nat.mul_mod, Nat.add_mod]
  have h8 : (b + 2) % 8 = (b % 16 + 2) % 8 := by omega
  have h16 : b % 2 ^ 4 = b % 16 := rfl
  rw [h8, h16]
  have hr : b % 16 < 16 := Nat.mod_lt _ (by decide)
  have hodd : (b % 16) % 2 = 1 := by omega
  generalize b % 16 = r at hr hodd
  revert hodd
  revert r
  decide

theorem setupX_spec (b : Nat) (hb : b % 2 = 1) : b * setupX b % 2 ^ 32 = 1 :=
  newton_spec _ _ 16 (by decide) (by decide)
    (newton_spec _ _ 8 (by decide) (by decide) (newton_spec _ _ 4 (by decide) (by decide) (setupX0_spec b hb)))

/-- `rho` as the C computes it is `-x mod radix`. -/
theorem setupRho_eq (b : Nat) : setupRho b = (radix - setupX b % radix) % radix := by
  have hx : setupX b < 2 ^ 32 := Nat.mod_lt _ (by decide)
  unfold setupRho
  rw [and_mpMask, Nat.mod_mod_of_dvd _ (by decide : radix ∣ 2 ^ 32),
    Nat.mod_mod_of_dvd _ (by decide : radix ∣ 2 ^ 64)]
  simp only [radix, Layout.digitBits]
  omega

theorem setupRho_lt (b : Nat) : setupRho b < radix := by
  rw [setupRho_eq]; exact Nat.mod_lt _ radix_pos

/-- **`mp_montgomery_setup`**: for an odd low digit `b`, `b * rho ≡ -1 (mod radix)`. -/
theorem setupRho_spec (b : Nat) (hb : b % 2 = 1) : (b * setupRho b + 1) % radix = 0 := by
  have hx := setupX_spec b hb
  have hx28 : b * setupX b % radix = 1 := by
    rw [← Nat.mod_mod_of_dvd _ (by decide : radix ∣ 2 ^ 32), hx]; decide
  rw [setupRho_eq]
  generalize setupX b = x at hx28
  have hxr := Nat.mod_add_div x radix
  have hlt : x % radix < radix := Nat.mod_lt _ radix_pos
  have hne : x % radix ≠ 0 := by
    intro h0
    rw [Nat.mul_mod, h0, Nat.mul_zero, Nat.zero_mod] at hx28
    exact absurd hx28 (by decide)
  rw [Nat.mod_eq_of_lt (by omega : radix - x % radix < radix)]
  have hbx := Nat.mod_add_div (b * x) radix
  rw [hx28] at hbx
  apply natmod_zero_of_int (Q := b + b * ((x / radix : Nat) : Int) - ((b * x / radix : Nat) : Int))
  have e : ((radix - x % radix : Nat) : Int) = radix - ((x % radix : Nat) : Int) := by omega
  have e2 : ((x % radix : Nat) : Int) = x - radix * ((x / radix : Nat) : Int) := by omega
  have e3 : ((b * x : Nat) : Int) = 1 + radix * ((b * x / radix : Nat) : Int) := by omega
  rw [Int.natCast_add, Int.natCast_mul, e, e2]
  rw [Int.natCast_mul] at e3
  generalize ((x / radix : Nat) : Int) = q at *
  generalize ((b * x / radix : Nat) : Int) = q' at *
  generalize ((radix : Nat) : Int) = R at *
  grind

/-- What `mp_montgomery_setup(n, &rho)` leaves: `MP_VAL` and nothing written for an
even `n->dp[0]`; otherwise `MP_OKAY` and `rho = setupRho n->dp[0]`. -/
structure SetupPost (n : MpInt) (ret : Int) (rho : Nat) : Prop where
  even : n.digit 0 % 2 = 0 → ret = Layout.mpVal
  odd : n.digit 0 % 2 = 1 → ret = Layout.mpOkay ∧ rho = setupRho (n.digit 0)

theorem mod_mul_mod' (a b M : Nat) : a % M * b % M = a * b % M := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem mul_add_one_mod (a b : Nat) : (a * b + 1) % radix = (a % radix * b + 1) % radix := by
  rw [Nat.add_mod, ← mod_mul_mod', ← Nat.add_mod]

/-- The low digit decides the magnitude modulo the radix. -/
theorem natUpTo_mod_radix (f : Nat → Nat) (hf : f 0 < radix) : ∀ n, 0 < n → natUpTo f n % radix = f 0
  | n + 1, _ => by
    rw [Nat.add_comm, natUpTo_split f 1 n]
    simp only [natUpTo, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.pow_one]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hf]

theorem MpInt.mag_mod_radix {a : MpInt} (ha : a.Shape) : a.mag % radix = a.digit 0 := by
  rcases Nat.eq_zero_or_pos a.used with h | h
  · rw [MpInt.mag_used_zero h, ha.high_zero 0 (by omega), Nat.zero_mod]
  · exact natUpTo_mod_radix _ (ha.digit_lt 0) _ h

/-- `mp_montgomery_setup` gives `rho = -1/n mod radix` for odd `n`. -/
theorem SetupPost.spec {n : MpInt} {ret : Int} {rho : Nat} (hn : n.Shape) (h : SetupPost n ret rho)
    (hodd : n.mag % 2 = 1) :
    ret = Layout.mpOkay ∧ rho < radix ∧ (n.mag * rho + 1) % radix = 0 := by
  have hm := MpInt.mag_mod_radix hn
  have h0 : n.digit 0 % 2 = 1 := by
    rw [← hm, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ radix)]; exact hodd
  obtain ⟨hr, hrho⟩ := h.odd h0
  refine ⟨hr, hrho ▸ setupRho_lt _, ?_⟩
  rw [mul_add_one_mod, hm, hrho]
  exact setupRho_spec _ h0

/-! ## REDC on values: what both reduction loops compute -/

/-- `mu = x->dp[ix] * rho mod radix`, the digit `j` of the running value `T`. -/
def redcMu (rho T j : Nat) : Nat := T / radix ^ j % radix * rho % radix

/-- The running value after `j` rows: row `j` adds `mu_j * n * radix^j`. -/
def redcT (x n rho : Nat) : Nat → Nat
  | 0 => x
  | j + 1 => redcT x n rho j + redcMu rho (redcT x n rho j) j * n * radix ^ j

/-- The multiplier `Σ_{i<j} mu_i * radix^i`. -/
def redcM (x n rho : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => redcM x n rho j + redcMu rho (redcT x n rho j) j * radix ^ j

/-- The final conditional subtraction (`if mp_cmp_mag(x, n) != MP_LT then s_mp_sub`). -/
def montOut (t n : Nat) : Nat := if n ≤ t then t - n else t

/-- The REDC result for `n->used = nu` rows. -/
def redc (x n rho nu : Nat) : Nat := montOut (redcT x n rho nu / radix ^ nu) n

theorem redcMu_lt (rho T j : Nat) : redcMu rho T j < radix := Nat.mod_lt _ radix_pos

theorem redcT_eq (x n rho : Nat) : ∀ j, redcT x n rho j = x + redcM x n rho j * n
  | 0 => by simp [redcT, redcM]
  | j + 1 => by
    simp only [redcT, redcM, redcT_eq x n rho j, Nat.add_mul, Nat.mul_right_comm _ (radix ^ j) n]
    omega

theorem redcM_lt (x n rho : Nat) : ∀ j, redcM x n rho j < radix ^ j
  | 0 => by simp [redcM]
  | j + 1 => by
    have ih := redcM_lt x n rho j
    have hm := redcMu_lt rho (redcT x n rho j) j
    simp only [redcM, Nat.pow_succ]
    have : redcMu rho (redcT x n rho j) j * radix ^ j ≤ (radix - 1) * radix ^ j :=
      Nat.mul_le_mul_right _ (by omega)
    have e : (radix - 1) * radix ^ j + radix ^ j = radix ^ j * radix := by
      rw [Nat.mul_comm (radix ^ j) radix, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel radix_pos]
    omega

/-- The digit choice: `d + (d * rho mod radix) * n ≡ 0 (mod radix)` when `n * rho ≡ -1`. -/
theorem mu_kills (c n rho : Nat) (hrho : (n % radix * rho + 1) % radix = 0) :
    (c + (c % radix * rho % radix) * n) % radix = 0 := by
  rw [Nat.add_mod, mod_mul_mod', Nat.add_mod_mod, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have e : c % radix + c % radix * rho * n = c % radix * (n * rho + 1) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm rho]; omega
  rw [← Nat.mod_add_mod, e, Nat.mul_mod, mul_add_one_mod n rho, hrho, Nat.mul_zero, Nat.zero_mod]

/-- Every row clears one more low digit: `radix^j ∣ T_j`. -/
theorem redcT_dvd (x n rho : Nat) (hrho : (n % radix * rho + 1) % radix = 0) :
    ∀ j, radix ^ j ∣ redcT x n rho j
  | 0 => Nat.one_dvd _
  | j + 1 => by
    obtain ⟨c, hc⟩ := redcT_dvd x n rho hrho j
    have hk : radix ∣ c + (c % radix * rho % radix) * n := Nat.dvd_of_mod_eq_zero (mu_kills c n rho hrho)
    obtain ⟨d, hd⟩ := hk
    refine ⟨d, ?_⟩
    have hmu : redcMu rho (redcT x n rho j) j = c % radix * rho % radix := by
      unfold redcMu; rw [hc, Nat.mul_div_cancel_left _ (Nat.pow_pos radix_pos)]
    simp only [redcT, hmu]
    rw [hc, Nat.mul_comm (c % radix * rho % radix * n) (radix ^ j), ← Nat.mul_add, hd, Nat.pow_succ,
      Nat.mul_assoc]

/-- **REDC** (`mp_montgomery_reduce`, `s_mp_montgomery_reduce_fast`): with
`n * rho ≡ -1 (mod radix)` and `x < n * R` (`R = radix^nu`), the result is below `n`
and `r * R ≡ x (mod n)`. -/
theorem redc_spec (x n rho nu : Nat) (hrho : (n % radix * rho + 1) % radix = 0) (hx : x < n * radix ^ nu) :
    redc x n rho nu < n ∧ (redc x n rho nu * radix ^ nu) % n = x % n := by
  have hR : 0 < radix ^ nu := Nat.pow_pos radix_pos
  obtain ⟨t, ht⟩ := redcT_dvd x n rho hrho nu
  have hT := redcT_eq x n rho nu
  have hM := redcM_lt x n rho nu
  have htd : redcT x n rho nu / radix ^ nu = t := by rw [ht, Nat.mul_div_cancel_left _ hR]
  have hMn : redcM x n rho nu * n < radix ^ nu * n := Nat.mul_lt_mul_of_pos_right hM (by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, Nat.zero_mul] at hx; omega
    · exact h)
  have h2 : radix ^ nu * t < radix ^ nu * (2 * n) := by
    rw [← ht, hT, Nat.mul_comm 2 n, ← Nat.mul_assoc, Nat.mul_two, Nat.mul_comm (radix ^ nu) n]
    rw [Nat.mul_comm (radix ^ nu) n] at hMn; omega
  have ht2 := Nat.lt_of_mul_lt_mul_left h2
  unfold redc montOut
  rw [htd]
  have hmod : (t * radix ^ nu) % n = x % n := by
    rw [Nat.mul_comm, ← ht, hT, Nat.add_mul_mod_self_right]
  split
  · refine ⟨by omega, ?_⟩
    have e : (t - n) * radix ^ nu + n * radix ^ nu = t * radix ^ nu := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    rw [← hmod, ← e, Nat.add_mul_mod_self_left]
  · exact ⟨by omega, hmod⟩

/-! ## Digit arrays and the carry step -/

/-- `f` with entry `i` overwritten by `v` (a store `*p = v`). -/
def upd (f : Nat → Nat) (i v : Nat) : Nat → Nat := fun j => if j = i then v else f j

@[simp] theorem upd_same (f : Nat → Nat) (i v : Nat) : upd f i v i = v := by simp [upd]

theorem upd_ne (f : Nat → Nat) {i j : Nat} (v : Nat) (h : j ≠ i) : upd f i v j = f j := by simp [upd, h]

/-- A store below `n` changes the value by the difference of the entries. -/
theorem natUpTo_upd (f : Nat → Nat) (i v : Nat) :
    ∀ n, i < n → natUpTo (upd f i v) n + radix ^ i * f i = natUpTo f n + radix ^ i * v
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    simp only [natUpTo]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | rfl
    · have ih := natUpTo_upd f i v n h'
      rw [upd_ne f v (by omega)]; omega
    · rw [natUpTo_congr i (e := f) (fun j hj => upd_ne f v (by omega)), upd_same]; omega

/-- A store at or above `n` does not change the value of the first `n` entries. -/
theorem natUpTo_upd_ge (f : Nat → Nat) (i v n : Nat) (h : n ≤ i) : natUpTo (upd f i v) n = natUpTo f n :=
  natUpTo_congr n (fun j hj => upd_ne f v (by omega))

/-- Entry `i` of a digit vector, read back from its value. -/
theorem natUpTo_digit (f : Nat → Nat) (hf : ∀ i, f i < radix) :
    ∀ n i, i < n → natUpTo f n / radix ^ i % radix = f i := by
  intro n i hi
  obtain ⟨m, rfl⟩ : ∃ m, n = i + (m + 1) := ⟨n - i - 1, by omega⟩
  rw [natUpTo_split f i (m + 1), Nat.add_comm m 1, natUpTo_split _ 1 m]
  simp only [natUpTo, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.pow_one, Nat.add_zero]
  rw [Nat.add_mul_div_left _ _ (Nat.pow_pos radix_pos),
    Nat.div_eq_of_lt (natUpTo_lt f hf i), Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf i)]

/-- The state of a carry loop: the digit array and the carry `u`. -/
structure CSt where
  dig : Nat → Nat
  u : Nat

/-- One carry step at position `k` with addend `t`:
`r = t + u + x[k]; x[k] = r & MP_MASK; u = r >> MP_DIGIT_BIT`. -/
def cstep (s : CSt) (k t : Nat) : CSt :=
  ⟨upd s.dig k ((t + s.u + s.dig k) % radix), (t + s.u + s.dig k) / radix⟩

/-- The carry step keeps `value + radix^k * carry` up to the addend. -/
theorem cstep_val (s : CSt) (k t D : Nat) (hk : k < D) :
    natUpTo (cstep s k t).dig D + radix ^ (k + 1) * (cstep s k t).u = natUpTo s.dig D + radix ^ k * (t + s.u) := by
  have h := natUpTo_upd s.dig k ((t + s.u + s.dig k) % radix) D hk
  have hdm := Nat.mod_add_div (t + s.u + s.dig k) radix
  show natUpTo (upd s.dig k _) D + radix ^ (k + 1) * ((t + s.u + s.dig k) / radix) = _
  have e : radix ^ (k + 1) * ((t + s.u + s.dig k) / radix) =
      radix ^ k * (radix * ((t + s.u + s.dig k) / radix)) := by rw [Nat.pow_succ, Nat.mul_assoc]
  have e2 : radix ^ k * ((t + s.u + s.dig k) % radix) + radix ^ k * (radix * ((t + s.u + s.dig k) / radix)) =
      radix ^ k * (t + s.u) + radix ^ k * s.dig k := by rw [← Nat.mul_add, hdm, Nat.mul_add]
  omega

theorem cstep_dig_lt (s : CSt) (k t : Nat) (h : ∀ i, s.dig i < radix) : ∀ i, (cstep s k t).dig i < radix := by
  intro i; unfold cstep upd; simp only; split
  · exact Nat.mod_lt _ radix_pos
  · exact h i

theorem cstep_dig_ne (s : CSt) {k i : Nat} (t : Nat) (h : i ≠ k) : (cstep s k t).dig i = s.dig i :=
  upd_ne _ _ h

/-- The carry stays a digit when the addend is a digit product, and the sum fits in
`mp_word` (`< radix^2 ≤ 2^64`). -/
theorem cstep_bound (s : CSt) (k t : Nat) (hu : s.u < radix) (hd : s.dig k < radix)
    (ht : t ≤ (radix - 1) * (radix - 1)) :
    t + s.u + s.dig k < radix * radix ∧ (cstep s k t).u < radix := by
  have e : (radix - 1) * (radix - 1) + (radix - 1) + (radix - 1) + 1 = radix * radix := by
    simp only [radix, Layout.digitBits]
  have h1 : t + s.u + s.dig k < radix * radix := by omega
  exact ⟨h1, Nat.div_lt_of_lt_mul h1⟩

/-! ## `mp_montgomery_reduce`: the rows -/

/-- The inner loop of row `ix` after `iy` steps: `r = mu * n[iy] + u + x[ix + iy]`. -/
def rowAt (nd : Nat → Nat) (mu ix : Nat) (s0 : CSt) : Nat → CSt
  | 0 => s0
  | iy + 1 => cstep (rowAt nd mu ix s0 iy) (ix + iy) (mu * nd iy)

theorem rowAt_val (nd : Nat → Nat) (mu ix : Nat) (s0 : CSt) (D : Nat) :
    ∀ iy, ix + iy ≤ D →
      natUpTo (rowAt nd mu ix s0 iy).dig D + radix ^ (ix + iy) * (rowAt nd mu ix s0 iy).u =
        natUpTo s0.dig D + radix ^ ix * s0.u + radix ^ ix * (mu * natUpTo nd iy)
  | 0, _ => by simp [rowAt, natUpTo]
  | iy + 1, h => by
    have ih := rowAt_val nd mu ix s0 D iy (by omega)
    simp only [rowAt]
    rw [show ix + (iy + 1) = ix + iy + 1 by omega, cstep_val _ _ _ D (by omega)]
    simp only [natUpTo, Nat.mul_add]
    have e : radix ^ ix * (mu * (radix ^ iy * nd iy)) = radix ^ (ix + iy) * (mu * nd iy) := by
      rw [Nat.pow_add]; ac_rfl
    omega

theorem rowAt_dig_lt (nd : Nat → Nat) (mu ix : Nat) (s0 : CSt) (h : ∀ i, s0.dig i < radix) :
    ∀ iy i, (rowAt nd mu ix s0 iy).dig i < radix
  | 0 => h
  | iy + 1 => cstep_dig_lt _ _ _ (rowAt_dig_lt nd mu ix s0 h iy)

/-- Row `ix` writes only positions `ix .. ix + iy - 1`. -/
theorem rowAt_dig_out (nd : Nat → Nat) (mu ix : Nat) (s0 : CSt) :
    ∀ iy i, (i < ix ∨ ix + iy ≤ i) → (rowAt nd mu ix s0 iy).dig i = s0.dig i
  | 0, _, _ => rfl
  | iy + 1, i, h => by
    simp only [rowAt]
    rw [cstep_dig_ne _ _ (by omega), rowAt_dig_out nd mu ix s0 iy i (by omega)]

/-- The carries of a row stay digits (so `u` is an `mp_digit` and `r` an `mp_word`). -/
theorem rowAt_u_lt (nd : Nat → Nat) (hn : ∀ i, nd i < radix) (mu ix : Nat) (hmu : mu < radix) (s0 : CSt)
    (h : ∀ i, s0.dig i < radix) (hu : s0.u < radix) : ∀ iy, (rowAt nd mu ix s0 iy).u < radix
  | 0 => hu
  | iy + 1 => by
    have ih := rowAt_u_lt nd hn mu ix hmu s0 h hu iy
    have hd := rowAt_dig_lt nd mu ix s0 h iy (ix + iy)
    have ht : mu * nd iy ≤ (radix - 1) * (radix - 1) :=
      Nat.mul_le_mul (by omega) (by have := hn iy; omega)
    exact (cstep_bound _ _ _ ih hd ht).2

/-! ## The carry propagation `while (u != 0) { *tmpx += u; u = *tmpx >> 28; *tmpx++ &= MP_MASK; }` -/

/-- The propagation loop with fuel: stops when the carry is zero. Returns the state and
the final position. -/
def propLoop : CSt → Nat → Nat → CSt × Nat
  | s, k, 0 => (s, k)
  | s, k, fuel + 1 => if s.u = 0 then (s, k) else propLoop (cstep s k 0) (k + 1) fuel

/-- While the carry is nonzero the position is inside the array (the loop stays in
bounds): `value + radix^k * u < radix^D` forces `k < D`. -/
theorem prop_in_bounds (s : CSt) (k D : Nat) (hv : natUpTo s.dig D + radix ^ k * s.u < radix ^ D)
    (hu : s.u ≠ 0) : k < D := by
  rcases Nat.lt_or_ge k D with h | h
  · exact h
  · have : radix ^ D ≤ radix ^ k * s.u :=
      Nat.le_trans (Nat.pow_le_pow_right radix_pos h) (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu))
    omega

/-- The propagation ends with no carry, `value` grown by `radix^k * u`, within the array. -/
theorem propLoop_spec (D : Nat) :
    ∀ fuel (s : CSt) k, (∀ i, s.dig i < radix) → natUpTo s.dig D + radix ^ k * s.u < radix ^ D →
      D ≤ k + fuel →
      (propLoop s k fuel).1.u = 0 ∧
        natUpTo (propLoop s k fuel).1.dig D = natUpTo s.dig D + radix ^ k * s.u ∧
        (∀ i, (propLoop s k fuel).1.dig i < radix) ∧
        (∀ i, D ≤ i → (propLoop s k fuel).1.dig i = s.dig i)
  | 0, s, k, hd, hv, hf => by
    simp only [propLoop]
    by_cases hu : s.u = 0
    · simp [hu, hd]
    · have := prop_in_bounds s k D hv hu; omega
  | fuel + 1, s, k, hd, hv, hf => by
    simp only [propLoop]
    by_cases hu : s.u = 0
    · simp [hu, hd]
    · simp only [hu, ite_false]
      have hk := prop_in_bounds s k D hv hu
      have hc := cstep_val s k 0 D hk
      rw [Nat.zero_add] at hc
      obtain ⟨h1, h2, h3, h4⟩ := propLoop_spec D fuel (cstep s k 0) (k + 1) (cstep_dig_lt _ _ _ hd)
        (by omega) (by omega)
      refine ⟨h1, by omega, h3, fun i hi => ?_⟩
      rw [h4 i hi, cstep_dig_ne _ _ (by omega)]

/-! ## A whole row of `mp_montgomery_reduce` -/

theorem redcT_mono (x n rho : Nat) : ∀ {i j}, i ≤ j → redcT x n rho i ≤ redcT x n rho j := by
  intro i j h
  induction j with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · have := ih (by omega); simp only [redcT]; omega
    · exact Nat.le_refl _

/-- The running value stays below `2 * n * R ≤ radix^(2 nu + 1)`: the array of
`digs = 2 * n->used + 1` digits holds every row. -/
theorem redcT_lt (x n rho nu : Nat) (hn : n < radix ^ nu) (hx : x < n * radix ^ nu) (j : Nat) (hj : j ≤ nu) :
    redcT x n rho j < radix ^ (2 * nu + 1) := by
  have h1 := redcT_mono x n rho hj
  have h2 := redcT_eq x n rho nu
  have h3 := redcM_lt x n rho nu
  have h4 : redcM x n rho nu * n ≤ radix ^ nu * n := Nat.mul_le_mul_right _ (Nat.le_of_lt h3)
  have h5 : n * radix ^ nu + radix ^ nu * n ≤ radix ^ (2 * nu + 1) := by
    rw [Nat.pow_succ, Nat.two_mul, Nat.pow_add, Nat.mul_comm n]
    have : radix ^ nu * n ≤ radix ^ nu * radix ^ nu := Nat.mul_le_mul_left _ (Nat.le_of_lt hn)
    have h2r : 2 ≤ radix := by simp [radix, Layout.digitBits]
    have : 2 * (radix ^ nu * radix ^ nu) ≤ radix ^ nu * radix ^ nu * radix := by
      rw [Nat.mul_comm _ radix]; exact Nat.mul_le_mul_right _ h2r
    omega
  omega

/-- What row `ix` leaves: with `x->dp` holding `T_ix` (digits, `D` of them, `T_(ix+1)`
fitting in `D` digits), `mu = x->dp[ix] * rho mod radix`, the inner loop
(`rowAt`, `n->used` steps) and the propagation (`propLoop`) leave `T_(ix+1)` with no
carry, digits below the radix, and the digits from `D` on unchanged. -/
structure RowOut (x n rho ix D : Nat) (f f' : Nat → Nat) : Prop where
  val : natUpTo f' D = redcT x n rho (ix + 1)
  dig_lt : ∀ i, f' i < radix
  high : ∀ i, D ≤ i → f' i = f i

theorem row_spec (x n rho nu ix D : Nat) (nd f : Nat → Nat) (hn : natUpTo nd nu = n)
    (hf : ∀ i, f i < radix) (hv : natUpTo f D = redcT x n rho ix) (hix : ix < D) (hD : ix + nu ≤ D)
    (hfit : redcT x n rho (ix + 1) < radix ^ D) :
    RowOut x n rho ix D f
      (propLoop (rowAt nd (f ix * rho % radix) ix ⟨f, 0⟩ nu) (ix + nu) (D - (ix + nu))).1.dig := by
  have hmu : f ix * rho % radix = redcMu rho (redcT x n rho ix) ix := by
    unfold redcMu; rw [← hv, natUpTo_digit f hf D ix hix]
  have hr := rowAt_val nd (f ix * rho % radix) ix ⟨f, 0⟩ D nu hD
  simp only [Nat.mul_zero, Nat.add_zero] at hr
  rw [hn] at hr
  have hT : redcT x n rho (ix + 1) = redcT x n rho ix + radix ^ ix * (f ix * rho % radix * n) := by
    simp only [redcT, hmu]; rw [Nat.mul_comm (radix ^ ix), Nat.mul_assoc]
  have hdl := rowAt_dig_lt nd (f ix * rho % radix) ix ⟨f, 0⟩ hf nu
  obtain ⟨_, h2, h3, h4⟩ := propLoop_spec D (D - (ix + nu)) _ (ix + nu) hdl (by omega) (by omega)
  refine ⟨by omega, h3, fun i hi => ?_⟩
  rw [h4 i hi, rowAt_dig_out nd _ ix ⟨f, 0⟩ nu i (by omega)]

/-- All rows: the array after `j` rows of `mp_montgomery_reduce`. -/
def slowRows (nd : Nat → Nat) (rho nu D : Nat) (f : Nat → Nat) : Nat → (Nat → Nat)
  | 0 => f
  | j + 1 =>
    let g := slowRows nd rho nu D f j
    (propLoop (rowAt nd (g j * rho % radix) j ⟨g, 0⟩ nu) (j + nu) (D - (j + nu))).1.dig

/-- **The rows of `mp_montgomery_reduce`**: after `j ≤ n->used` rows the array of
`D = 2 * n->used + 1` digits holds `T_j`. -/
theorem slowRows_spec (x n rho nu : Nat) (nd f : Nat → Nat) (hn : natUpTo nd nu = n)
    (hnr : n < radix ^ nu) (hx : x < n * radix ^ nu)
    (hf : ∀ i, f i < radix) (hv : natUpTo f (2 * nu + 1) = x) :
    ∀ j, j ≤ nu → natUpTo (slowRows nd rho nu (2 * nu + 1) f j) (2 * nu + 1) = redcT x n rho j ∧
      ∀ i, slowRows nd rho nu (2 * nu + 1) f j i < radix
  | 0, _ => ⟨hv, hf⟩
  | j + 1, h => by
    obtain ⟨ih1, ih2⟩ := slowRows_spec x n rho nu nd f hn hnr hx hf hv j (by omega)
    have r := row_spec x n rho nu j (2 * nu + 1) nd _ hn ih2 ih1 (by omega) (by omega)
      (redcT_lt x n rho nu hnr hx (j + 1) h)
    exact ⟨r.val, r.dig_lt⟩

/-- `mp_rshd(x, n->used)` after the rows: the value divided by `R`. -/
theorem natUpTo_shift_down (f : Nat → Nat) (nu m : Nat) (hz : ∀ i, i < nu → f i = 0) :
    natUpTo (fun i => f (nu + i)) m = natUpTo f (nu + m) / radix ^ nu := by
  rw [natUpTo_split f nu m, natUpTo_congr nu (e := fun _ => 0) hz, natUpTo_zero_fun, Nat.zero_add,
    Nat.mul_div_cancel_left _ (Nat.pow_pos radix_pos)]

/-! ## `s_mp_montgomery_reduce_fast`: the `W[]` columns

`W[0 .. 2 n->used]` (`mp_word`) starts as the digits of `x`. Row `ix` sets
`mu = ((W[ix] & MP_MASK) * rho) & MP_MASK`, adds `mu * n[iy]` to `W[ix + iy]`
(`wRow`) and then carries `W[ix + 1] += W[ix] >> MP_DIGIT_BIT` (`wFix`). After the rows
the carries are fixed for `ix = n->used .. 2 n->used - 1` (`wFix` again) and
`x[i] = W[n->used + i] & MP_MASK` for `i ≤ n->used`.

`wVal W lo hi D` reads the columns the way the algorithm means them: below `lo`
nothing (those digits are zero), from `lo` to `hi` the carried digits `W[i] % radix`,
from `hi` on the full columns. -/

/-- The value of the column array: `Σ_{lo ≤ i < hi} (W i % radix) radix^i + Σ_{hi ≤ i < D} W i radix^i`. -/
def wVal (W : Nat → Nat) (lo hi D : Nat) : Nat :=
  natUpTo (fun i => if i < lo then 0 else if i < hi then W i % radix else W i) D

/-- The inner loop `*_W++ += (mp_word)mu * (mp_word)*tmpn++` of row `ix` after `iy` steps. -/
def wRow (nd : Nat → Nat) (mu ix : Nat) (W : Nat → Nat) : Nat → (Nat → Nat)
  | 0 => W
  | iy + 1 => upd (wRow nd mu ix W iy) (ix + iy) (wRow nd mu ix W iy (ix + iy) + mu * nd iy)

/-- The carry fix `W[ix + 1] += W[ix] >> MP_DIGIT_BIT`. -/
def wFix (W : Nat → Nat) (ix : Nat) : Nat → Nat := upd W (ix + 1) (W (ix + 1) + W ix / radix)

/-- The rows of `s_mp_montgomery_reduce_fast`. -/
def fastRows (nd : Nat → Nat) (rho nu : Nat) (W0 : Nat → Nat) : Nat → (Nat → Nat)
  | 0 => W0
  | j + 1 =>
    let W := fastRows nd rho nu W0 j
    wFix (wRow nd (W j % radix * rho % radix) j W nu) j

/-- The final carry loop `for (; ix < 2 n->used + 1; ix++) W[ix + 1] += W[ix] >> 28` after `k`
steps (from `ix = n->used`). -/
def fastTail (nu : Nat) (W : Nat → Nat) : Nat → (Nat → Nat)
  | 0 => W
  | k + 1 => wFix (fastTail nu W k) (nu + k)

theorem wRow_out (nd : Nat → Nat) (mu ix : Nat) (W : Nat → Nat) :
    ∀ iy i, (i < ix ∨ ix + iy ≤ i) → wRow nd mu ix W iy i = W i
  | 0, _, _ => rfl
  | iy + 1, i, h => by
    simp only [wRow]; rw [upd_ne _ _ (by omega), wRow_out nd mu ix W iy i (by omega)]

theorem wRow_val (nd : Nat → Nat) (mu ix lo D : Nat) (W : Nat → Nat) (hlo : lo ≤ ix) :
    ∀ iy, ix + iy ≤ D → wVal (wRow nd mu ix W iy) lo lo D = wVal W lo lo D + radix ^ ix * (mu * natUpTo nd iy)
  | 0, _ => by simp [wRow, natUpTo]
  | iy + 1, h => by
    have ih := wRow_val nd mu ix lo D W hlo iy (by omega)
    unfold wVal at ih ⊢
    have hf : (fun i => if i < lo then 0 else if i < lo then wRow nd mu ix W (iy + 1) i % radix
        else wRow nd mu ix W (iy + 1) i) =
        upd (fun i => if i < lo then 0 else if i < lo then wRow nd mu ix W iy i % radix else wRow nd mu ix W iy i)
          (ix + iy) (wRow nd mu ix W iy (ix + iy) + mu * nd iy) := by
      funext i; simp only [wRow, upd]
      by_cases hi : i = ix + iy
      · subst hi; simp [show ¬ ix + iy < lo by omega]
      · simp [hi]
    rw [hf]
    have hu := natUpTo_upd (fun i => if i < lo then 0 else if i < lo then wRow nd mu ix W iy i % radix
        else wRow nd mu ix W iy i) (ix + iy) (wRow nd mu ix W iy (ix + iy) + mu * nd iy) D (by omega)
    simp only [show ¬ ix + iy < lo by omega, ite_false] at hu
    simp only [natUpTo, Nat.mul_add] at hu ⊢
    have e : radix ^ ix * (mu * (radix ^ iy * nd iy)) = radix ^ (ix + iy) * (mu * nd iy) := by
      rw [Nat.pow_add]; ac_rfl
    omega

/-- The carry fix moves column `ix` into the carried digits. -/
theorem wFix_val (W : Nat → Nat) (lo ix D : Nat) (hlo : lo ≤ ix) (hD : ix + 1 < D) :
    wVal (wFix W ix) lo (ix + 1) D = wVal W lo ix D := by
  unfold wVal wFix
  have hf : (fun i => if i < lo then 0 else if i < ix + 1 then upd W (ix + 1) (W (ix + 1) + W ix / radix) i % radix
      else upd W (ix + 1) (W (ix + 1) + W ix / radix) i) =
      upd (upd (fun i => if i < lo then 0 else if i < ix then W i % radix else W i) ix (W ix % radix))
        (ix + 1) (W (ix + 1) + W ix / radix) := by
    funext i; simp only [upd]
    by_cases h1 : i = ix + 1
    · subst h1; simp [show ¬ ix + 1 < lo by omega]
    · by_cases h2 : i = ix
      · subst h2; simp [show ¬ i < lo by omega]
      · simp only [h1, h2, ite_false]
        by_cases h3 : i < lo
        · simp [h3]
        · simp only [h3, ite_false]
          by_cases h4 : i < ix
          · simp [h4, show i < ix + 1 by omega]
          · simp [h4, show ¬ i < ix + 1 by omega]
  rw [hf]
  have h1 := natUpTo_upd (upd (fun i => if i < lo then 0 else if i < ix then W i % radix else W i) ix (W ix % radix))
    (ix + 1) (W (ix + 1) + W ix / radix) D hD
  have h2 := natUpTo_upd (fun i => if i < lo then 0 else if i < ix then W i % radix else W i) ix (W ix % radix) D
    (by omega)
  rw [upd_ne _ _ (by omega)] at h1
  simp only [show ¬ ix + 1 < lo by omega, show ¬ ix + 1 < ix by omega, show ¬ ix < lo by omega,
    Nat.lt_irrefl, ite_false] at h1 h2
  have hdm := Nat.mod_add_div (W ix) radix
  have e : radix ^ (ix + 1) * (W (ix + 1) + W ix / radix) =
      radix ^ (ix + 1) * W (ix + 1) + radix ^ ix * (radix * (W ix / radix)) := by
    simp only [Nat.mul_add, Nat.pow_succ, Nat.mul_assoc]
  have e2 : radix ^ ix * (W ix % radix) + radix ^ ix * (radix * (W ix / radix)) = radix ^ ix * W ix := by
    rw [← Nat.mul_add, hdm]
  omega

/-- A carried digit that is zero can be dropped from the bottom. -/
theorem wVal_lo_succ (W : Nat → Nat) (lo hi D : Nat) (hlo : lo < hi) (h0 : W lo % radix = 0) :
    wVal W (lo + 1) hi D = wVal W lo hi D := by
  unfold wVal; apply natUpTo_congr; intro i _
  by_cases h : i = lo
  · subst h; simp [h0, hlo]
  · by_cases h' : i < lo
    · simp [h', show i < lo + 1 by omega]
    · simp [h', show ¬ i < lo + 1 by omega]

/-- The column at `lo` is the digit `lo` of the value. -/
theorem wVal_digit (W : Nat → Nat) (lo D : Nat) (hD : lo < D) :
    wVal W lo lo D / radix ^ lo % radix = W lo % radix := by
  unfold wVal
  obtain ⟨m, rfl⟩ : ∃ m, D = lo + (m + 1) := ⟨D - lo - 1, by omega⟩
  rw [natUpTo_split _ lo (m + 1), natUpTo_congr lo (e := fun _ => 0) (fun i hi => by simp [hi]),
    natUpTo_zero_fun, Nat.zero_add, Nat.mul_div_cancel_left _ (Nat.pow_pos radix_pos), Nat.add_comm m 1,
    natUpTo_split _ 1 m]
  simp only [natUpTo, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.pow_one, Nat.add_zero, Nat.lt_irrefl,
    ite_false]
  rw [Nat.add_mul_mod_self_left]

/-- **The rows of `s_mp_montgomery_reduce_fast`**: after `j ≤ n->used` rows the columns from
`j` on hold `T_j`, and the low digit of column `j` is digit `j` of `T_j` (so `mu` is
`redcMu`). -/
theorem fastRows_spec (x n rho nu : Nat) (nd W0 : Nat → Nat) (hn : natUpTo nd nu = n)
    (hrho : (n % radix * rho + 1) % radix = 0) (hv : wVal W0 0 0 (2 * nu + 1) = x) :
    ∀ j, j ≤ nu → wVal (fastRows nd rho nu W0 j) j j (2 * nu + 1) = redcT x n rho j
  | 0, _ => hv
  | j + 1, h => by
    have ih := fastRows_spec x n rho nu nd W0 hn hrho hv j (by omega)
    simp only [fastRows]
    generalize hW : fastRows nd rho nu W0 j = W at ih
    have hmu : W j % radix * rho % radix = redcMu rho (redcT x n rho j) j := by
      unfold redcMu; rw [← ih, wVal_digit W j _ (by omega)]
    have hr := wRow_val nd (W j % radix * rho % radix) j j (2 * nu + 1) W (Nat.le_refl _) nu (by omega)
    rw [ih, hn, hmu] at hr
    have hT : redcT x n rho (j + 1) = redcT x n rho j + radix ^ j * (redcMu rho (redcT x n rho j) j * n) := by
      simp only [redcT]; rw [Nat.mul_comm (radix ^ j), Nat.mul_assoc]
    rw [← hT] at hr
    rw [hmu]
    generalize hV : wRow nd (redcMu rho (redcT x n rho j) j) j W nu = V at hr
    have hz : V j % radix = 0 := by
      have hd := wVal_digit V j (2 * nu + 1) (by omega)
      rw [hr] at hd
      obtain ⟨c, hc⟩ := redcT_dvd x n rho hrho (j + 1)
      rw [hc, Nat.pow_succ, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.pow_pos radix_pos),
        Nat.mul_mod_right] at hd
      exact hd.symm
    have hf := wFix_val V j j (2 * nu + 1) (Nat.le_refl _) (by omega)
    have hl := wVal_lo_succ (wFix V j) j (j + 1) (2 * nu + 1) (by omega)
      (by unfold wFix; rw [upd_ne _ _ (by omega)]; exact hz)
    rw [hl, hf, hr]

/-- The final carries: after `k` steps from `ix = n->used` the columns `nu .. nu + k - 1`
are carried digits. -/
theorem fastTail_val (nu : Nat) (W : Nat → Nat) (D : Nat) :
    ∀ k, nu + k < D → wVal (fastTail nu W k) nu (nu + k) D = wVal W nu nu D
  | 0, _ => rfl
  | k + 1, h => by
    simp only [fastTail]
    rw [show nu + (k + 1) = nu + k + 1 by omega, wFix_val _ nu (nu + k) D (by omega) (by omega),
      fastTail_val nu W D k (by omega)]

/-- The copy-out `x[i] = W[n->used + i] & MP_MASK` (`i ≤ n->used`) reads `T / R`, which is
below `2 n < radix^(nu+1)`, so the top column is already a digit. -/
theorem fastOut_val (x n rho nu : Nat) (W : Nat → Nat) (hnr : n < radix ^ nu) (hx : x < n * radix ^ nu)
    (hW : wVal W nu (2 * nu) (2 * nu + 1) = redcT x n rho nu) :
    natUpTo (fun i => W (nu + i) % radix) (nu + 1) = redcT x n rho nu / radix ^ nu := by
  have hR : 0 < radix ^ nu := Nat.pow_pos radix_pos
  unfold wVal at hW
  rw [show 2 * nu + 1 = nu + (nu + 1) by omega, natUpTo_split _ nu (nu + 1),
    natUpTo_congr nu (e := fun _ => 0) (fun i hi => by simp [hi]), natUpTo_zero_fun, Nat.zero_add] at hW
  rw [← hW, Nat.mul_div_cancel_left _ hR]
  -- the top column: value < 2 n R ≤ 2 radix^(2 nu), so it is at most 1
  have hT := redcT_lt x n rho nu hnr hx nu (Nat.le_refl _)
  simp only [natUpTo] at hW ⊢
  have htop : W (nu + nu) < radix := by
    have h2 : radix ^ nu * (radix ^ nu * W (nu + nu)) ≤ redcT x n rho nu := by
      rw [← hW]; simp only [show ¬ nu + nu < nu by omega, show ¬ nu + nu < 2 * nu by omega, ite_false]
      exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
    have h3 := redcT_eq x n rho nu
    have h4 := redcM_lt x n rho nu
    have h5 : redcM x n rho nu * n ≤ radix ^ nu * n := Nat.mul_le_mul_right _ (Nat.le_of_lt h4)
    have h6 : redcT x n rho nu < radix ^ nu * (radix ^ nu * 2) := by
      have : radix ^ nu * n ≤ radix ^ nu * radix ^ nu := Nat.mul_le_mul_left _ (Nat.le_of_lt hnr)
      rw [Nat.mul_comm n] at hx
      rw [Nat.mul_two, Nat.mul_add]; omega
    have h7 : radix ^ nu * (radix ^ nu * W (nu + nu)) < radix ^ nu * (radix ^ nu * 2) := by omega
    have := Nat.lt_of_mul_lt_mul_left (Nat.lt_of_mul_lt_mul_left h7)
    simp only [radix, Layout.digitBits]; omega
  rw [Nat.mod_eq_of_lt htop]
  congr 1
  · apply natUpTo_congr; intro i hi
    simp only [show ¬ nu + i < nu by omega, show nu + i < 2 * nu by omega, ite_false, ite_true]
  · simp only [show ¬ nu + nu < nu by omega, show ¬ nu + nu < 2 * nu by omega, ite_false]

/-! ## `s_mp_montgomery_reduce_fast`: no `mp_word` overflow

Before row `j` every column holds at most a digit, `j` products `mu * n[iy]` and — up to
position `c` — one carry below `2^36`: `wBound c j i`. With `n->used ≤ 255`
(`n->used < MP_MAXFAST = 256`) that is below `2^64`. -/

/-- The column bound: a digit, the carry if `i ≤ c`, `j` digit products. -/
def wBound (c j i : Nat) : Nat := (radix - 1) + (if i ≤ c then 2 ^ 36 else 0) + j * ((radix - 1) * (radix - 1))

theorem wBound_le (c j i : Nat) (hj : j ≤ 255) :
    wBound c j i ≤ (radix - 1) + 2 ^ 36 + 255 * ((radix - 1) * (radix - 1)) := by
  unfold wBound
  have : j * ((radix - 1) * (radix - 1)) ≤ 255 * ((radix - 1) * (radix - 1)) := Nat.mul_le_mul_right _ hj
  have : (if i ≤ c then 2 ^ 36 else 0) ≤ 2 ^ 36 := by split <;> omega
  omega

theorem wBound_lt (c j i : Nat) (hj : j ≤ 255) : wBound c j i < 2 ^ 64 := by
  have := wBound_le c j i hj
  have h2 : (radix - 1) + 2 ^ 36 + 255 * ((radix - 1) * (radix - 1)) < 2 ^ 64 := by
    simp only [radix, Layout.digitBits]; omega
  omega

/-- The carry out of a column within the bound is below `2^36`. -/
theorem wBound_carry (c j i : Nat) (hj : j ≤ 255) (w : Nat) (hw : w ≤ wBound c j i) : w / radix < 2 ^ 36 := by
  apply Nat.div_lt_of_lt_mul
  have := wBound_le c j i hj
  have h2 : (radix - 1) + 2 ^ 36 + 255 * ((radix - 1) * (radix - 1)) < radix * 2 ^ 36 := by
    simp only [radix, Layout.digitBits]; omega
  omega

/-- The inner loop adds at most one digit product to each column it touches. -/
theorem wRow_le (nd : Nat → Nat) (hnd : ∀ i, nd i < radix) (mu ix : Nat) (hmu : mu < radix) (W : Nat → Nat) :
    ∀ iy i, wRow nd mu ix W iy i ≤ W i + (if ix ≤ i ∧ i < ix + iy then (radix - 1) * (radix - 1) else 0)
  | 0, i => by simp [wRow]
  | iy + 1, i => by
    have ih := wRow_le nd hnd mu ix hmu W iy
    simp only [wRow]
    by_cases h : i = ix + iy
    · subst h
      rw [upd_same]
      have h1 := ih (ix + iy)
      have h2 : mu * nd iy ≤ (radix - 1) * (radix - 1) := Nat.mul_le_mul (by omega) (by have := hnd iy; omega)
      rw [wRow_out nd mu ix W iy (ix + iy) (Or.inr (Nat.le_refl _)),
        (ite_eq_left (show ix ≤ ix + iy ∧ ix + iy < ix + (iy + 1) by omega))]
      omega
    · rw [upd_ne _ _ h]
      refine Nat.le_trans (ih i) (Nat.add_le_add_left ?_ _)
      by_cases h' : ix ≤ i ∧ i < ix + iy
      · simp [h', show i < ix + (iy + 1) by omega]
      · simp [h']

/-- **Rows within the bound**: before row `j ≤ n->used ≤ 255` every column is at most
`wBound j j i` (so below `2^64`, and every carry below `2^36`). -/
theorem fastRows_bound (nd W0 : Nat → Nat) (rho nu : Nat) (hnd : ∀ i, nd i < radix) (hW0 : ∀ i, W0 i < radix)
    (hnu : nu ≤ 255) : ∀ j, j ≤ nu → ∀ i, fastRows nd rho nu W0 j i ≤ wBound j j i
  | 0, _, i => by
    show W0 i ≤ wBound 0 0 i
    have := hW0 i; unfold wBound; omega
  | j + 1, h, i => by
    have ih := fastRows_bound nd W0 rho nu hnd hW0 hnu j (by omega)
    simp only [fastRows]
    generalize fastRows nd rho nu W0 j = W at ih
    have hmu : W j % radix * rho % radix < radix := Nat.mod_lt _ radix_pos
    have hV := wRow_le nd hnd (W j % radix * rho % radix) j hmu W nu
    generalize wRow nd (W j % radix * rho % radix) j W nu = V at hV
    have hVb : ∀ i, V i ≤ wBound j (j + 1) i := by
      intro i
      have h1 := hV i; have h2 := ih i
      have h3 : (if j ≤ i ∧ i < j + nu then (radix - 1) * (radix - 1) else 0) ≤ (radix - 1) * (radix - 1) := by
        split <;> omega
      unfold wBound at *; rw [Nat.succ_mul]; omega
    have hc := wBound_carry j (j + 1) j (by omega) (V j) (hVb j)
    unfold wFix
    by_cases hi : i = j + 1
    · subst hi; rw [upd_same]
      have := hVb (j + 1); unfold wBound at *
      rw [(ite_eq_right (show ¬ j + 1 ≤ j by omega))] at this
      rw [(ite_eq_left (Nat.le_refl _))]
      omega
    · rw [upd_ne _ _ hi]
      have := hVb i; unfold wBound at *
      by_cases h1 : i ≤ j
      · rw [(ite_eq_left h1)] at this; rw [(ite_eq_left (show i ≤ j + 1 by omega))]; omega
      · rw [(ite_eq_right h1)] at this; rw [(ite_eq_right (show ¬ i ≤ j + 1 by omega))]; omega

/-- **The final carries within the bound**: after `k` steps from `ix = n->used` the columns are
at most `wBound (nu + k) nu i`. -/
theorem fastTail_bound (nu : Nat) (W : Nat → Nat) (hnu : nu ≤ 255) (hW : ∀ i, W i ≤ wBound nu nu i) :
    ∀ k i, fastTail nu W k i ≤ wBound (nu + k) nu i
  | 0, i => hW i
  | k + 1, i => by
    have ih := fastTail_bound nu W hnu hW k
    simp only [fastTail]
    generalize fastTail nu W k = V at ih
    have hc := wBound_carry (nu + k) nu (nu + k) hnu (V (nu + k)) (ih (nu + k))
    unfold wFix
    by_cases hi : i = nu + k + 1
    · subst hi; rw [upd_same]
      have := ih (nu + k + 1); unfold wBound at *
      rw [(ite_eq_right (show ¬ nu + k + 1 ≤ nu + k by omega))] at this
      rw [(ite_eq_left (show nu + k + 1 ≤ nu + (k + 1) by omega))]
      omega
    · rw [upd_ne _ _ hi]
      have := ih i; unfold wBound at *
      by_cases h1 : i ≤ nu + k
      · rw [(ite_eq_left h1)] at this; rw [(ite_eq_left (show i ≤ nu + (k + 1) by omega))]; omega
      · rw [(ite_eq_right h1)] at this; rw [(ite_eq_right (show ¬ i ≤ nu + (k + 1) by omega))]; omega

/-! ## The contracts of the two reductions -/

/-- What `mp_montgomery_reduce(x, n, rho)` and `s_mp_montgomery_reduce_fast(x, n, rho)`
leave in `x` (with `x->alloc ≥ 2 n->used + 1`, resp. `≥ n->used + 1`, so no `mp_grow`, D5;
the fast one also needs `x->used ≤ MP_WARRAY`, else `MP_VAL` and `x` unchanged): the REDC
result `redc |x| |n| rho n->used`, valid, the sign of `x` (reset if zero). The rows
(`slowRows_spec` resp. `fastRows_spec`, `fastTail_val`, `fastOut_val`) give `T / R`; `mp_clamp`,
`mp_rshd` (slow) and the conditional `s_mp_sub` give `montOut`. -/
structure RedcPost (x n : MpInt) (rho : Nat) (x' : MpInt) : Prop where
  valid : x'.Valid
  alloc : x'.alloc = x.alloc
  mag : x'.mag = redc x.mag n.mag rho n.used
  sign : x'.sign = if x'.used = 0 then Layout.mpZpos else x.sign

/-- **Montgomery reduction**: `|x'| < |n|` and `|x'| * R ≡ |x| (mod |n|)`, `R = radix^n->used`,
for `rho` from `mp_montgomery_setup` (`n * rho ≡ -1 (mod radix)`) and `|x| < |n| * R`. -/
theorem RedcPost.spec {x n x' : MpInt} {rho : Nat} (hrho : (n.mag * rho + 1) % radix = 0)
    (hx : x.mag < n.mag * radix ^ n.used) (h : RedcPost x n rho x') :
    x'.Valid ∧ x'.mag < n.mag ∧ (x'.mag * radix ^ n.used) % n.mag = x.mag % n.mag := by
  have hr : (n.mag % radix * rho + 1) % radix = 0 := by rw [← mul_add_one_mod]; exact hrho
  obtain ⟨h1, h2⟩ := redc_spec x.mag n.mag rho n.used hr hx
  exact ⟨h.valid, h.mag ▸ h1, h.mag ▸ h2⟩

theorem mod_eq_of_dvd_sub' {a b P : Nat} (hab : b ≤ a) (h : P ∣ a - b) : a % P = b % P := by
  obtain ⟨c, hc⟩ := h
  rw [show a = b + P * c by omega, Nat.add_mul_mod_self_left]

/-- Cancelling a factor coprime to the modulus. -/
theorem mod_cancel {P R a b : Nat} (hc : Nat.Coprime P R) (h : (a * R) % P = (b * R) % P) : a % P = b % P := by
  rcases Nat.le_total b a with hab | hab
  · have hd : P ∣ (a - b) * R := by
      rw [Nat.sub_mul]; exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h)
    exact mod_eq_of_dvd_sub' hab (hc.dvd_of_dvd_mul_right hd)
  · have hd : P ∣ (b - a) * R := by
      rw [Nat.sub_mul]; exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm)
    exact (mod_eq_of_dvd_sub' hab (hc.dvd_of_dvd_mul_right hd)).symm

theorem coprime_odd_radix_pow {P : Nat} (hP : P % 2 = 1) (nu : Nat) : Nat.Coprime P (radix ^ nu) := by
  have h2 : Nat.Coprime P 2 := by
    show Nat.gcd P 2 = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, hP]; rfl
  exact (h2.pow_right Layout.digitBits).pow_right nu

/-- REDC as a function of `x` alone: the unique `r < n` with `r * R ≡ x`, for every
`x ≤ (n - 1)^2` (every product of two reduced values). This is the shape the window
loop of `s_mp_exptmod_fast` needs (`Tom.Window.Red`). -/
theorem redc_red (n rho nu : Nat) (hrho : (n % radix * rho + 1) % radix = 0) (hn : 0 < n)
    (hnr : n ≤ radix ^ nu) (x : Nat) (hx : x ≤ (n - 1) * (n - 1)) :
    redc x n rho nu < n ∧ (redc x n rho nu * radix ^ nu) % n = x % n := by
  apply redc_spec x n rho nu hrho
  have : (n - 1) * (n - 1) < n * radix ^ nu :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) hn) (Nat.mul_le_mul_left _ hnr)
  omega

/-! ## `mp_montgomery_calc_normalization` -/

/-- `mp_count_bits` by meaning: `0` for `0`, else `⌊log2 m⌋ + 1`. -/
def nbits (m : Nat) : Nat := if m = 0 then 0 else Nat.log2 m + 1

theorem nbits_lt (m : Nat) : m < 2 ^ nbits m := by
  unfold nbits; split
  · subst m; decide
  · exact Nat.lt_log2_self

theorem nbits_le (m : Nat) (h : 0 < m) : 2 ^ (nbits m - 1) ≤ m := by
  unfold nbits; simp only [show m ≠ 0 by omega, ite_false, Nat.add_sub_cancel]; exact Nat.log2_self_le (by omega)

/-- The start of `mp_montgomery_calc_normalization(a, b)`: the exponent `e` of the first
`a = 2^e` (`mp_2expt` for `b->used > 1`, `mp_set(a, 1)` else) and the number of doublings
(`for (x = bits - 1; x < MP_DIGIT_BIT; x++)`), with `bits = mp_count_bits(b) % MP_DIGIT_BIT`
(set to `1` in the one-digit case). -/
def normE0 (b : MpInt) : Nat :=
  if 1 < b.used then (b.used - 1) * Layout.digitBits + nbits b.mag % Layout.digitBits - 1 else 0

def normCnt (b : MpInt) : Nat :=
  if 1 < b.used then Layout.digitBits + 1 - nbits b.mag % Layout.digitBits else Layout.digitBits

/-- One pass: `mp_mul_2(a, a)`, then `s_mp_sub(a, b, a)` unless `mp_cmp_mag(a, b) == MP_LT`. -/
def normStep (b a : Nat) : Nat := if b ≤ 2 * a then 2 * a - b else 2 * a

def normLoop (b : Nat) : Nat → Nat → Nat
  | a, 0 => a
  | a, k + 1 => normLoop b (normStep b a) k

theorem normLoop_spec (b : Nat) : ∀ k a, a < b → normLoop b a k = (a * 2 ^ k) % b
  | 0, a, h => by simp [normLoop, Nat.mod_eq_of_lt h]
  | k + 1, a, h => by
    simp only [normLoop]
    have hs : normStep b a = (2 * a) % b := by
      unfold normStep; split
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      · rw [Nat.mod_eq_of_lt (by omega)]
    have hlt : normStep b a < b := by rw [hs]; exact Nat.mod_lt _ (by omega)
    rw [normLoop_spec b k _ hlt, hs, Nat.mod_mul_mod, Nat.pow_succ]
    congr 1; ac_rfl

theorem normE0_add (b : MpInt) (hb : 0 < b.used) : normE0 b + normCnt b = Layout.digitBits * b.used := by
  unfold normE0 normCnt
  have h28 : nbits b.mag % Layout.digitBits < Layout.digitBits := Nat.mod_lt _ (by decide)
  split
  · simp only [Layout.digitBits] at *
    have : 28 ≤ (b.used - 1) * 28 := Nat.le_mul_of_pos_left 28 (by omega)
    rw [Nat.sub_mul] at *; omega
  · rw [show b.used = 1 by omega]; rfl


/-- The first power is below `b` for odd `b > 1` (for `b = 2^e` with more than one digit it
would equal `b`, and the loop would leave `b`, not `0`). -/
theorem normE0_lt (b : MpInt) (hb : b.Valid) (hodd : b.mag % 2 = 1) (h1 : 1 < b.mag) :
    2 ^ normE0 b < b.mag := by
  unfold normE0
  split
  · rename_i hu
    have hlo := MpInt.mag_ge hb (by omega)
    have hhi := MpInt.mag_lt hb.toShape
    have hn1 := nbits_le b.mag (by omega)
    have hn2 := nbits_lt b.mag
    simp only [radix, ← Nat.pow_mul] at hlo hhi
    have hA : Layout.digitBits * (b.used - 1) < nbits b.mag :=
      (Nat.pow_lt_pow_iff_right (by decide)).1 (Nat.lt_of_le_of_lt hlo hn2)
    have hB : nbits b.mag - 1 < Layout.digitBits * b.used :=
      (Nat.pow_lt_pow_iff_right (by decide)).1 (Nat.lt_of_le_of_lt hn1 hhi)
    simp only [Layout.digitBits] at *
    have e1 : 28 * (b.used - 1) + 28 = 28 * b.used := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
    rw [Nat.mul_comm (b.used - 1)]
    by_cases h0 : nbits b.mag % 28 = 0
    · rw [h0, Nat.add_zero]
      have : nbits b.mag = 28 * b.used := by omega
      exact Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) (by omega)) hn1
    · have hq : nbits b.mag / 28 = b.used - 1 := by omega
      have he : 28 * (b.used - 1) + nbits b.mag % 28 - 1 = nbits b.mag - 1 := by
        have := Nat.mod_add_div (nbits b.mag) 28; rw [hq] at this; omega
      rw [he]
      rcases Nat.lt_or_eq_of_le hn1 with h | h
      · exact h
      · exfalso
        have : 2 ^ (nbits b.mag - 1) % 2 = 0 := by
          rw [show nbits b.mag - 1 = (nbits b.mag - 2) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left]
        omega
  · simp only [Nat.pow_zero]; exact h1

/-- What `mp_montgomery_calc_normalization(a, b)` leaves in `a` (allocation not failing):
`2^normE0` doubled `normCnt` times with one conditional subtraction each. -/
structure NormPost (b a' : MpInt) : Prop where
  valid : a'.Valid
  mag : a'.mag = normLoop b.mag (2 ^ normE0 b) (normCnt b)
  sign : a'.sign = Layout.mpZpos

/-- **`mp_montgomery_calc_normalization`**: `a = R mod b`, `R = radix^b->used`, for odd `b > 1`. -/
theorem NormPost.spec {b a' : MpInt} (hb : b.Valid) (hodd : b.mag % 2 = 1) (h1 : 1 < b.mag)
    (h : NormPost b a') : a'.Valid ∧ a'.mag = radix ^ b.used % b.mag ∧ a'.val = (radix ^ b.used % b.mag : Nat) := by
  have hu : 0 < b.used := by
    rcases Nat.eq_zero_or_pos b.used with h0 | h0
    · rw [MpInt.mag_used_zero h0] at h1; omega
    · exact h0
  have hm : a'.mag = radix ^ b.used % b.mag := by
    rw [h.mag, normLoop_spec _ _ _ (normE0_lt b hb hodd h1), ← Nat.pow_add, normE0_add b hu, radix,
      Nat.pow_mul]
  refine ⟨h.valid, hm, ?_⟩
  unfold MpInt.val; rw [h.sign, hm]; simp [Layout.mpZpos, Layout.mpNeg]

end Mont

end Tom
