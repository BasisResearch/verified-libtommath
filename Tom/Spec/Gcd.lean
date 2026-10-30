import Tom.Spec.Signed

/-!
# `mp_gcd` and `mp_invmod`: binary gcd and the binary extended Euclid

Value-level models of the C loops (`vendor/libtommath/bn_mp_gcd.c`,
`bn_mp_invmod.c`, `bn_s_mp_invmod_fast.c`, `bn_s_mp_invmod_slow.c`). The
`mp_int` temporaries the C keeps (`u`, `v`, `A`, `B`, `C`, `D`) are held as
their values (`Nat` for `u`, `v`, which stay nonnegative, `Int` for the
coefficients); one step function per C loop body, invariant structures with
their preservation lemmas, a termination measure, and the final lemma. The
callees appear by meaning only:

* `mp_cnt_lsb(n)` is `Gcd.lsb n` (trailing zero bits, `0` for `0`);
* `mp_div_2d(n, k)` is `n / 2 ^ k`, `mp_mul_2d(n, k)` is `n * 2 ^ k`;
* `mp_div_2(X)` on an even signed `X` is the exact half `X / 2`
  (`Gcd.half_exact`: the C halves the magnitude and keeps the sign);
* `mp_mod(a, b)` for `b > 0` is `a.val % b.val` (Lean's `Int` `%` is the
  Euclidean remainder, in `[0, b)`).

**Two quirks of the C** that the specs below state as they are:

* `s_mp_invmod_fast` (odd modulus) ends with `c->sign = a->sign`: for a
  negative `a` the result is the *negated* inverse. Checked by running the
  real library (MP_32BIT): `mp_invmod(-3, 7) = -2`, and `(-3)·(-2) ≡ -1`
  (mod 7). `InvmodPost.spec_neg_odd` states this behaviour; the even-modulus
  path (`s_mp_invmod_slow`) returns the true inverse for every sign.
* `s_mp_invmod_slow` called directly with an odd `b` and `a ≡ 0 (mod b)`
  does not terminate (`u = 0` is halved forever; checked: `s_mp_invmod_slow(14, 7)`
  on the real library runs until killed); `mp_invmod` only calls it
  with an even `b`, where that case is the `MP_VAL` error (`x`, `y` both
  even). The slow model's guard `u ≠ 0` is not in the C.

Allocation (`mp_init_multi`, `mp_grow` inside the callees) is assumed not
to fail (D5); no `MP_MEM` cases are modelled.
-/

namespace Tom

open MpInt

namespace Gcd

/-! ## Arithmetic helpers -/

theorem dvd_of_dvd_two_mul {k n : Nat} (hk : k % 2 = 1) (h : k ∣ 2 * n) : k ∣ n := by
  have h1 : k ∣ k * n := Nat.dvd_mul_right k n
  have h2 : k ∣ (k / 2) * (2 * n) := Nat.dvd_mul_left_of_dvd h (k / 2)
  have hk' : k = 2 * (k / 2) + 1 := by omega
  have e : k * n - (k / 2) * (2 * n) = n := by
    have : k * n = (k / 2) * (2 * n) + n := by
      conv => lhs; rw [hk']
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.mul_left_comm]
    omega
  rw [← e]; exact Nat.dvd_sub h1 h2

theorem int_dvd_of_dvd_two_mul {k : Nat} {t : Int} (hk : k % 2 = 1) (h : (k : Int) ∣ 2 * t) :
    (k : Int) ∣ t := by
  have hk' : (k : Int) = 2 * ((k / 2 : Nat) : Int) + 1 := by omega
  have e : t = (k : Int) * t - ((k / 2 : Nat) : Int) * (2 * t) := by
    rw [hk']; grind
  rw [e]
  exact Int.dvd_sub (Int.dvd_mul_right _ _) (Int.dvd_trans h (Int.dvd_mul_left _ _))

theorem coprime_two_of_odd {k : Nat} (hk : k % 2 = 1) : Nat.Coprime 2 k := by
  unfold Nat.Coprime
  have h1 : Nat.gcd 2 k ∣ 2 := Nat.gcd_dvd_left 2 k
  have h2 : Nat.gcd 2 k ∣ k := Nat.gcd_dvd_right 2 k
  have hle : Nat.gcd 2 k ≤ 2 := Nat.le_of_dvd (by decide) h1
  have hpos : 0 < Nat.gcd 2 k := Nat.gcd_pos_of_pos_left k (by decide)
  rcases (show Nat.gcd 2 k = 1 ∨ Nat.gcd 2 k = 2 by omega) with e | e
  · exact e
  · rw [e] at h2; omega

/-- A common divisor of `u` and `v` that is odd divides `u / 2` when `u` is even. -/
theorem gcd_half {u v : Nat} (hu : u % 2 = 0) (hg : Nat.gcd u v % 2 = 1) :
    Nat.gcd (u / 2) v = Nat.gcd u v := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) ⟨2, by omega⟩
    · exact Nat.gcd_dvd_right _ _
  · apply Nat.dvd_gcd
    · apply dvd_of_dvd_two_mul hg
      rw [show 2 * (u / 2) = u by omega]; exact Nat.gcd_dvd_left _ _
    · exact Nat.gcd_dvd_right _ _

theorem gcd_sub_left {u v : Nat} (h : v ≤ u) : Nat.gcd (u - v) v = Nat.gcd u v := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have := Nat.dvd_add (Nat.gcd_dvd_left (u - v) v) (Nat.gcd_dvd_right (u - v) v)
      rwa [Nat.sub_add_cancel h] at this
    · exact Nat.gcd_dvd_right _ _
  · exact Nat.dvd_gcd (Nat.dvd_sub (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)) (Nat.gcd_dvd_right _ _)

theorem gcd_sub_right {u v : Nat} (h : u ≤ v) : Nat.gcd u (v - u) = Nat.gcd u v := by
  rw [Nat.gcd_comm, gcd_sub_left h, Nat.gcd_comm]

/-- `mp_div_2` on an even signed value (halve the magnitude, keep the sign) is
the exact half. -/
theorem half_exact (X : Int) (h : X % 2 = 0) :
    (if X < 0 then -((X.natAbs / 2 : Nat) : Int) else ((X.natAbs / 2 : Nat) : Int)) = X / 2 := by
  split <;> omega

/-- `MP_IS_ODD` reads the low bit of the magnitude. -/
theorem odd_natAbs (X : Int) : X.natAbs % 2 = 1 ↔ X % 2 = 1 := by omega

/-! ## `mp_cnt_lsb` by meaning: trailing zero bits -/

/-- The number of trailing zero bits of `n` (`0` for `n = 0`, as `mp_cnt_lsb`). -/
def lsb (n : Nat) : Nat := if h : n ≠ 0 ∧ n % 2 = 0 then lsb (n / 2) + 1 else 0
termination_by n
decreasing_by omega

/-- `n` with its trailing zero bits shifted out. -/
def oddPart (n : Nat) : Nat := n / 2 ^ lsb n

theorem pow_lsb_dvd (n : Nat) : 2 ^ lsb n ∣ n := by
  rw [lsb]
  split
  · rename_i h
    have ih := pow_lsb_dvd (n / 2)
    obtain ⟨m, hm⟩ := ih
    exact ⟨m, by rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2, ← Nat.mul_assoc, ← hm]; omega⟩
  · exact Nat.one_dvd n
termination_by n
decreasing_by omega

theorem oddPart_odd (n : Nat) (hn : n ≠ 0) : oddPart n % 2 = 1 := by
  unfold oddPart
  rw [lsb]
  split
  · rename_i h
    have ih := oddPart_odd (n / 2) (by omega)
    unfold oddPart at ih
    rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
    exact ih
  · rename_i h
    simp only [Nat.pow_zero, Nat.div_one]
    omega
termination_by n
decreasing_by omega

theorem oddPart_mul (n : Nat) : 2 ^ lsb n * oddPart n = n := Nat.mul_div_cancel' (pow_lsb_dvd n)

theorem oddPart_le (n : Nat) : oddPart n ≤ n := Nat.div_le_self _ _

theorem oddPart_zero : oddPart 0 = 0 := by simp [oddPart]

theorem oddPart_pos {n : Nat} (hn : n ≠ 0) : 0 < oddPart n := by
  have := oddPart_odd n hn; omega

/-- `mp_gcd` divides by `2 ^ k` and then by `2 ^ (lsb - k)`: together the odd part. -/
theorem div_div_lsb (n k : Nat) (hk : k ≤ lsb n) : n / 2 ^ k / 2 ^ (lsb n - k) = oddPart n := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_cancel' hk]; rfl

/-- Removing factors of two does not change a gcd with an odd number. -/
theorem gcd_oddPart {k : Nat} (hk : k % 2 = 1) (n : Nat) : Nat.gcd k (oddPart n) = Nat.gcd k n := by
  conv => rhs; rw [← oddPart_mul n]
  exact (Nat.Coprime.gcd_mul_left_cancel_right (oddPart n) (Nat.Coprime.pow_left _ (coprime_two_of_odd hk))).symm

theorem gcd_pow_mul {i j om on : Nat} (hom : om % 2 = 1) (hon : on % 2 = 1) (hle : i ≤ j) :
    Nat.gcd (2 ^ i * om) (2 ^ j * on) = 2 ^ i * Nat.gcd om on := by
  have : 2 ^ j * on = 2 ^ i * (2 ^ (j - i) * on) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' hle]
  rw [this, Nat.gcd_mul_left]
  congr 1
  exact Nat.Coprime.gcd_mul_left_cancel_right _ (Nat.Coprime.pow_left _ (coprime_two_of_odd hom))

/-- `gcd m n = gcd (odd m) (odd n) * 2 ^ min (lsb m) (lsb n)`. -/
theorem gcd_split {m n : Nat} (hm : m ≠ 0) (hn : n ≠ 0) :
    Nat.gcd m n = Nat.gcd (oddPart m) (oddPart n) * 2 ^ min (lsb m) (lsb n) := by
  have hom := oddPart_odd m hm
  have hon := oddPart_odd n hn
  have e : Nat.gcd m n = Nat.gcd (2 ^ lsb m * oddPart m) (2 ^ lsb n * oddPart n) := by
    rw [oddPart_mul, oddPart_mul]
  rw [e]
  by_cases hle : lsb m ≤ lsb n
  · rw [Nat.min_eq_left hle, gcd_pow_mul hom hon hle, Nat.mul_comm]
  · rw [Nat.min_eq_right (by omega), Nat.gcd_comm, gcd_pow_mul hon hom (by omega), Nat.gcd_comm, Nat.mul_comm]

/-! ## `mp_gcd`: the loop -/

/-- One pass of `mp_gcd`'s `while (!MP_IS_ZERO(&v))` body: swap so that
`u ≤ v` (`mp_cmp_mag(&u, &v) == MP_GT`), `v = v - u` (`s_mp_sub`), then
`v = v / 2 ^ cnt_lsb(v)` (`mp_div_2d`). -/
def gcdStep (u v : Nat) : Nat × Nat :=
  if v < u then (v, oddPart (u - v)) else (u, oddPart (v - u))

theorem gcdStep_lt {u v : Nat} (hu : u ≠ 0) (hv : v ≠ 0) :
    (gcdStep u v).1 + (gcdStep u v).2 < u + v := by
  unfold gcdStep; split
  · have := oddPart_le (u - v); simp only; omega
  · have := oddPart_le (v - u); simp only; omega

theorem gcdStep_le (u v : Nat) : (gcdStep u v).1 ≤ max u v ∧ (gcdStep u v).2 ≤ max u v := by
  unfold gcdStep; split
  · have := oddPart_le (u - v); simp only; omega
  · have := oddPart_le (v - u); simp only; omega

/-- The loop of `mp_gcd` from `(u, v)`. The guard `u = 0` is not in the C
(where `u` stays odd); it makes the model total. -/
def gcdLoop (u v : Nat) : Nat :=
  if h : v = 0 then u else if hu : u = 0 then v else gcdLoop (gcdStep u v).1 (gcdStep u v).2
termination_by u + v
decreasing_by exact gcdStep_lt hu h

theorem gcdLoop_zero (u : Nat) : gcdLoop u 0 = u := by rw [gcdLoop]; simp

/-- The C's loop: one more pass while `v ≠ 0`. -/
theorem gcdLoop_step {u v : Nat} (hu : u ≠ 0) (hv : v ≠ 0) :
    gcdLoop u v = gcdLoop (gcdStep u v).1 (gcdStep u v).2 := by
  rw [gcdLoop]; simp [hu, hv]

/-- The loop invariant of `mp_gcd`: `u` odd, `v` odd or zero, the gcd kept. -/
structure GcdInv (g u v : Nat) : Prop where
  u_odd : u % 2 = 1
  v_odd : v ≠ 0 → v % 2 = 1
  gcd : Nat.gcd u v = g

theorem GcdInv.step {g u v : Nat} (h : GcdInv g u v) (hv : v ≠ 0) :
    GcdInv g (gcdStep u v).1 (gcdStep u v).2 := by
  have hvo := h.v_odd hv
  have hu := h.u_odd
  unfold gcdStep
  split
  · rename_i hlt
    refine ⟨hvo, fun hne => oddPart_odd _ (by intro e; rw [e, oddPart_zero] at hne; exact hne rfl), ?_⟩
    rw [gcd_oddPart hvo, Nat.gcd_comm, gcd_sub_left (by omega), h.gcd]
  · rename_i hlt
    refine ⟨hu, fun hne => oddPart_odd _ (by intro e; rw [e, oddPart_zero] at hne; exact hne rfl), ?_⟩
    rw [gcd_oddPart hu, gcd_sub_right (by omega), h.gcd]

theorem GcdInv.exit {g u : Nat} (h : GcdInv g u 0) : u = g := by
  have := h.gcd; rwa [Nat.gcd_zero_right] at this

/-- The loop computes the gcd from an odd `u`. -/
theorem gcdLoop_eq (u v : Nat) (h : GcdInv (Nat.gcd u v) u v) : gcdLoop u v = Nat.gcd u v := by
  by_cases hv : v = 0
  · subst hv; rw [gcdLoop_zero, Nat.gcd_zero_right]
  · have hu : u ≠ 0 := by have := h.u_odd; omega
    have h' := h.step hv
    rw [gcdLoop_step hu hv, gcdLoop_eq _ _ (by rw [h'.gcd]; exact h')]
    exact h'.gcd
termination_by u + v
decreasing_by exact gcdStep_lt hu hv

/-- What `mp_gcd(a, b, c)` computes, as the C does: `|b|` if `a = 0`, `|a|`
if `b = 0`, else the loop on the odd parts, shifted back by the common power
of two. -/
def gcdC (m n : Nat) : Nat :=
  if m = 0 then n else if n = 0 then m
  else gcdLoop (oddPart m) (oddPart n) * 2 ^ min (lsb m) (lsb n)

theorem gcdC_eq (m n : Nat) : gcdC m n = Nat.gcd m n := by
  unfold gcdC
  by_cases hm : m = 0
  · simp [hm]
  · by_cases hn : n = 0
    · simp [hm, hn]
    · simp only [hm, hn, if_false]
      rw [gcd_split hm hn, gcdLoop_eq]
      exact ⟨oddPart_odd m hm, fun _ => oddPart_odd n hn, rfl⟩

/-- The loop's values stay below the larger odd part (no growth of `u`, `v`). -/
theorem gcdStep_bound {M u v : Nat} (hu : u ≤ M) (hv : v ≤ M) :
    (gcdStep u v).1 ≤ M ∧ (gcdStep u v).2 ≤ M := by
  have := gcdStep_le u v; omega

end Gcd

/-! ## `mp_gcd`: contract -/

/-- What `mp_gcd(a, b, c)` leaves in `c`: a valid, nonnegative `mp_int` whose
magnitude is the C's computation `gcdC |a| |b|`. -/
structure GcdPost (a b c' : MpInt) : Prop where
  valid : c'.Valid
  mag : c'.mag = Gcd.gcdC a.mag b.mag
  sign : c'.sign = Layout.mpZpos

theorem MpInt.natAbs_val (a : MpInt) : a.val.natAbs = a.mag := by
  unfold MpInt.val; split <;> simp

/-- `mp_gcd` computes `gcd(|a|, |b|)`, nonnegative. -/
theorem GcdPost.spec {a b c' : MpInt} (h : GcdPost a b c') :
    c'.Valid ∧ c'.mag = Nat.gcd a.mag b.mag ∧ c'.val = (Nat.gcd a.mag b.mag : Int) := by
  have hm : c'.mag = Nat.gcd a.mag b.mag := by rw [h.mag, Gcd.gcdC_eq]
  refine ⟨h.valid, hm, ?_⟩
  unfold MpInt.val; rw [h.sign, hm]; simp [Layout.mpZpos, Layout.mpNeg]

/-- The same against `Int.gcd` of the values. -/
theorem GcdPost.spec_int {a b c' : MpInt} (h : GcdPost a b c') : c'.val = (Int.gcd a.val b.val : Int) := by
  have hm : c'.mag = Nat.gcd a.mag b.mag := by rw [h.mag, Gcd.gcdC_eq]
  have hv : c'.val = (Nat.gcd a.mag b.mag : Int) := by
    unfold MpInt.val; rw [h.sign, hm]; simp [Layout.mpZpos, Layout.mpNeg]
  rw [hv]; simp only [Int.gcd, MpInt.natAbs_val]

/-! ## Normalisation loops (`while (X < 0) X += b; while (|X| ≥ b) X -= b;`) -/

namespace Gcd

/-- `while (X < 0) X += b` (the guard `0 < b` is not in the C). -/
def addUp (b : Nat) (X : Int) : Int := if h : X < 0 ∧ 0 < b then addUp b (X + b) else X
termination_by (-X).toNat
decreasing_by omega

/-- `while (mp_cmp_mag(X, b) != MP_LT) X -= b`, on a nonnegative `X`
(where `|X| ≥ b` is `X ≥ b`; the guard `0 < b` is not in the C). -/
def subDown (b : Nat) (X : Int) : Int := if h : (b : Int) ≤ X ∧ 0 < b then subDown b (X - b) else X
termination_by X.toNat
decreasing_by omega

/-- The two loops. -/
def norm (b : Nat) (X : Int) : Int := subDown b (addUp b X)

theorem addUp_eq (b : Nat) (hb : 0 < b) (X : Int) : 0 ≤ addUp b X ∧ (addUp b X - X) % b = 0 ∧
    (X < 0 → addUp b X < b) := by
  rw [addUp]
  split
  · rename_i h
    obtain ⟨h1, h2, h3⟩ := addUp_eq b hb (X + b)
    refine ⟨h1, ?_, fun _ => ?_⟩
    · have : addUp b (X + ↑b) - X = (addUp b (X + ↑b) - (X + b)) + 1 * b := by omega
      rw [this, Int.add_mul_emod_self_right]; exact h2
    · by_cases hx : X + b < 0
      · exact h3 hx
      · rw [addUp]; simp only [show ¬ (X + b < 0 ∧ 0 < b) by omega, dite_false]; omega
  · rename_i h
    refine ⟨by omega, by simp, fun hx => absurd ⟨hx, hb⟩ h⟩
termination_by (-X).toNat
decreasing_by omega

theorem subDown_eq (b : Nat) (hb : 0 < b) (X : Int) (hX : 0 ≤ X) :
    0 ≤ subDown b X ∧ subDown b X < b ∧ (subDown b X - X) % b = 0 := by
  rw [subDown]
  split
  · rename_i h
    obtain ⟨h1, h2, h3⟩ := subDown_eq b hb (X - b) (by omega)
    refine ⟨h1, h2, ?_⟩
    have : subDown b (X - ↑b) - X = (subDown b (X - ↑b) - (X - b)) + (-1) * b := by omega
    rw [this, Int.add_mul_emod_self_right]; exact h3
  · rename_i h
    refine ⟨hX, by omega, by simp⟩
termination_by X.toNat
decreasing_by omega

theorem emod_unique {b : Int} {r X : Int} (hb : 0 < b) (h0 : 0 ≤ r) (h1 : r < b) (h : (r - X) % b = 0) :
    r = X % b := by
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
  have e : X = r + (-k) * b := by grind
  rw [e, Int.add_mul_emod_self_right, Int.emod_eq_of_lt h0 h1]

/-- The normalisation loops compute the Euclidean remainder. -/
theorem norm_eq (b : Nat) (hb : 0 < b) (X : Int) : norm b X = X % (b : Int) := by
  obtain ⟨a1, a2, _⟩ := addUp_eq b hb X
  obtain ⟨s1, s2, s3⟩ := subDown_eq b hb (addUp b X) a1
  apply emod_unique (by omega) s1 s2
  have : subDown b (addUp b X) - X = (subDown b (addUp b X) - addUp b X) + (addUp b X - X) := by omega
  rw [this, Int.add_emod, s3, a2]; rfl

/-! ## Parity helpers -/

theorem par_odd (A B x y : Int) (h : (A * x + B * y) % 2 = 0) (hxy : x % 2 = 1 ∨ y % 2 = 1)
    (hodd : A % 2 = 1 ∨ B % 2 = 1) : (A + y) % 2 = 0 ∧ (B - x) % 2 = 0 := by
  rw [Int.add_emod, Int.mul_emod A, Int.mul_emod B] at h
  rcases Int.emod_two_eq A with ha | ha <;> rcases Int.emod_two_eq B with hb | hb <;>
    rcases Int.emod_two_eq x with hx | hx <;> rcases Int.emod_two_eq y with hy | hy <;>
    simp only [ha, hb, hx, hy] at h hxy hodd <;> omega

/-! ## `s_mp_invmod_slow`: the model (`x = a mod b`, `y = b`) -/

/-- The values of `u, v, A, B, C, D` in `s_mp_invmod_slow`. -/
structure SlowSt where
  u : Nat
  v : Nat
  A : Int
  B : Int
  C : Int
  D : Int

/-- Step 3: `u = x, v = y, A = 1, B = 0, C = 0, D = 1`. -/
def slowInit (x y : Nat) : SlowSt := ⟨x, y, 1, 0, 0, 1⟩

/-- One pass of step 4 (`u` even): `u /= 2`; if `A` or `B` is odd,
`A += y, B -= x`; then `A /= 2, B /= 2`. -/
def slowHalfU (x y : Nat) (s : SlowSt) : SlowSt :=
  if s.A % 2 = 1 ∨ s.B % 2 = 1 then { s with u := s.u / 2, A := (s.A + y) / 2, B := (s.B - x) / 2 }
  else { s with u := s.u / 2, A := s.A / 2, B := s.B / 2 }

/-- One pass of step 5 (`v` even): the same on `v, C, D`. -/
def slowHalfV (x y : Nat) (s : SlowSt) : SlowSt :=
  if s.C % 2 = 1 ∨ s.D % 2 = 1 then { s with v := s.v / 2, C := (s.C + y) / 2, D := (s.D - x) / 2 }
  else { s with v := s.v / 2, C := s.C / 2, D := s.D / 2 }

/-- Step 6: `u ≥ v` (`mp_cmp(&u, &v) != MP_LT`): `u -= v, A -= C, B -= D`;
else `v -= u, C -= A, D -= B`. -/
def slowSub (s : SlowSt) : SlowSt :=
  if s.v ≤ s.u then { s with u := s.u - s.v, A := s.A - s.C, B := s.B - s.D }
  else { s with v := s.v - s.u, C := s.C - s.A, D := s.D - s.B }

@[simp] theorem slowHalfU_u (x y : Nat) (s : SlowSt) : (slowHalfU x y s).u = s.u / 2 := by
  unfold slowHalfU; split <;> rfl
@[simp] theorem slowHalfU_v (x y : Nat) (s : SlowSt) : (slowHalfU x y s).v = s.v := by
  unfold slowHalfU; split <;> rfl
@[simp] theorem slowHalfV_u (x y : Nat) (s : SlowSt) : (slowHalfV x y s).u = s.u := by
  unfold slowHalfV; split <;> rfl
@[simp] theorem slowHalfV_v (x y : Nat) (s : SlowSt) : (slowHalfV x y s).v = s.v / 2 := by
  unfold slowHalfV; split <;> rfl

/-- Step 4's loop `while (MP_IS_EVEN(&u))` (guard `u ≠ 0` not in the C). -/
def slowLoopU (x y : Nat) (s : SlowSt) : SlowSt :=
  if h : s.u ≠ 0 ∧ s.u % 2 = 0 then slowLoopU x y (slowHalfU x y s) else s
termination_by s.u
decreasing_by simp only [slowHalfU_u]; omega

/-- Step 5's loop `while (MP_IS_EVEN(&v))` (guard `v ≠ 0` not in the C). -/
def slowLoopV (x y : Nat) (s : SlowSt) : SlowSt :=
  if h : s.v ≠ 0 ∧ s.v % 2 = 0 then slowLoopV x y (slowHalfV x y s) else s
termination_by s.v
decreasing_by simp only [slowHalfV_v]; omega

theorem slowLoopU_uv (x y : Nat) (s : SlowSt) :
    (slowLoopU x y s).u ≤ s.u ∧ (0 < s.u → 0 < (slowLoopU x y s).u) ∧ (slowLoopU x y s).v = s.v := by
  rw [slowLoopU]; split
  · rename_i h
    have := slowLoopU_uv x y (slowHalfU x y s)
    simp only [slowHalfU_u, slowHalfU_v] at this; omega
  · omega
termination_by s.u
decreasing_by simp only [slowHalfU_u]; omega

theorem slowLoopV_uv (x y : Nat) (s : SlowSt) :
    (slowLoopV x y s).v ≤ s.v ∧ (0 < s.v → 0 < (slowLoopV x y s).v) ∧ (slowLoopV x y s).u = s.u := by
  rw [slowLoopV]; split
  · rename_i h
    have := slowLoopV_uv x y (slowHalfV x y s)
    simp only [slowHalfV_u, slowHalfV_v] at this; omega
  · omega
termination_by s.v
decreasing_by simp only [slowHalfV_v]; omega

/-- One pass from `top:` to the test `if (!MP_IS_ZERO(&u)) goto top`. -/
def slowPass (x y : Nat) (s : SlowSt) : SlowSt := slowSub (slowLoopV x y (slowLoopU x y s))

/-- The termination measure: a pass from positive `u`, `v` lowers `u + v`. -/
theorem slowPass_lt (x y : Nat) (s : SlowSt) (hu : 0 < s.u) (hv : 0 < s.v) :
    (slowPass x y s).u + (slowPass x y s).v < s.u + s.v := by
  obtain ⟨u1, u2, u3⟩ := slowLoopU_uv x y s
  obtain ⟨v1, v2, v3⟩ := slowLoopV_uv x y (slowLoopU x y s)
  unfold slowPass slowSub; split <;> simp only <;> omega

theorem slowPass_pos (x y : Nat) (s : SlowSt) (hu : 0 < s.u) (hv : 0 < s.v) :
    0 < (slowPass x y s).v := by
  obtain ⟨u1, u2, u3⟩ := slowLoopU_uv x y s
  obtain ⟨v1, v2, v3⟩ := slowLoopV_uv x y (slowLoopU x y s)
  unfold slowPass slowSub; split <;> simp only <;> omega

/-- `top: … if (!MP_IS_ZERO(&u)) goto top;` (guard on `u`, `v` positive not
in the C, where it is an invariant). -/
def slowTop (x y : Nat) (s : SlowSt) : SlowSt :=
  if h : 0 < s.u ∧ 0 < s.v ∧ (slowPass x y s).u ≠ 0 then slowTop x y (slowPass x y s) else slowPass x y s
termination_by s.u + s.v
decreasing_by exact slowPass_lt x y s h.1 h.2.1

theorem slowTop_eq (x y : Nat) (s : SlowSt) (hu : 0 < s.u) (hv : 0 < s.v) :
    slowTop x y s = if (slowPass x y s).u = 0 then slowPass x y s else slowTop x y (slowPass x y s) := by
  rw [slowTop]; by_cases h : (slowPass x y s).u = 0 <;> simp [h, hu, hv]

/-- The result of `s_mp_invmod_slow` on `x = a mod b`, `y = b`: `none` for
`MP_VAL` (both even, or `v ≠ 1` at the end), else the normalised `C`. -/
def slowRes (x y : Nat) : Option Int :=
  if x % 2 = 0 ∧ y % 2 = 0 then none
  else if (slowTop x y (slowInit x y)).v = 1 then some (norm y (slowTop x y (slowInit x y)).C)
  else none

/-! ### Invariant -/

/-- The invariant of `s_mp_invmod_slow` (HAC 14.61): `A x + B y = u`,
`C x + D y = v`, the gcd kept, and `x`, `y` not both even. -/
structure SlowInv (x y : Nat) (s : SlowSt) : Prop where
  par : x % 2 = 1 ∨ y % 2 = 1
  eu : s.A * x + s.B * y = s.u
  ev : s.C * x + s.D * y = s.v
  gcd : Nat.gcd s.u s.v = Nat.gcd x y

theorem gcd_odd_of {x y : Nat} (h : x % 2 = 1 ∨ y % 2 = 1) : Nat.gcd x y % 2 = 1 := by
  have h1 := Nat.gcd_dvd_left x y
  have h2 := Nat.gcd_dvd_right x y
  rcases Nat.mod_two_eq_zero_or_one (Nat.gcd x y) with e | e
  · exfalso
    have hd : 2 ∣ Nat.gcd x y := Nat.dvd_of_mod_eq_zero e
    have := Nat.dvd_trans hd h1
    have := Nat.dvd_trans hd h2
    omega
  · exact e

theorem slowInit_inv {x y : Nat} (h : x % 2 = 1 ∨ y % 2 = 1) : SlowInv x y (slowInit x y) :=
  ⟨h, by simp [slowInit], by simp [slowInit], rfl⟩

/-- Halving with the coefficient fix-up keeps `A x + B y = u` exactly. -/
theorem half_coef {x y : Nat} {A B : Int} {u : Nat} (hxy : x % 2 = 1 ∨ y % 2 = 1)
    (he : A * x + B * y = u) (hu : u % 2 = 0) :
    (if A % 2 = 1 ∨ B % 2 = 1 then (A + y) / 2 else A / 2) * x +
      (if A % 2 = 1 ∨ B % 2 = 1 then (B - x) / 2 else B / 2) * y = ((u / 2 : Nat) : Int) := by
  have hu' : ((u / 2 : Nat) : Int) * 2 = u := by omega
  have hpar : (A * x + B * y) % 2 = 0 := by rw [he]; omega
  split
  · rename_i hodd
    obtain ⟨h1, h2⟩ := par_odd A B x y hpar (by omega) hodd
    have ea : A + y = 2 * ((A + y) / 2) := by omega
    have eb : B - x = 2 * ((B - x) / 2) := by omega
    have : 2 * ((A + y) / 2 * x + (B - x) / 2 * y) = 2 * ((u / 2 : Nat) : Int) := by
      rw [show 2 * ((A + y) / 2 * x + (B - x) / 2 * y) = (2 * ((A + y) / 2)) * x + (2 * ((B - x) / 2)) * y by grind,
        ← ea, ← eb]
      grind
    omega
  · rename_i hev
    have ea : A = 2 * (A / 2) := by omega
    have eb : B = 2 * (B / 2) := by omega
    have : 2 * (A / 2 * x + B / 2 * y) = 2 * ((u / 2 : Nat) : Int) := by
      rw [show 2 * (A / 2 * x + B / 2 * y) = (2 * (A / 2)) * x + (2 * (B / 2)) * y by grind, ← ea, ← eb]
      omega
    omega

theorem SlowInv.halfU {x y : Nat} {s : SlowSt} (h : SlowInv x y s) (he : s.u % 2 = 0) :
    SlowInv x y (slowHalfU x y s) := by
  have hc := half_coef h.par h.eu he
  refine ⟨h.par, ?_, ?_, ?_⟩
  · unfold slowHalfU; split <;> rename_i hh <;> simp only [hh, if_true, if_false] at hc ⊢ <;> exact hc
  · unfold slowHalfU; split <;> exact h.ev
  · rw [slowHalfU_u, slowHalfU_v, gcd_half he (by rw [h.gcd]; exact gcd_odd_of h.par), h.gcd]

theorem SlowInv.halfV {x y : Nat} {s : SlowSt} (h : SlowInv x y s) (he : s.v % 2 = 0) :
    SlowInv x y (slowHalfV x y s) := by
  have hc := half_coef h.par h.ev he
  refine ⟨h.par, ?_, ?_, ?_⟩
  · unfold slowHalfV; split <;> exact h.eu
  · unfold slowHalfV; split <;> rename_i hh <;> simp only [hh, if_true, if_false] at hc ⊢ <;> exact hc
  · rw [slowHalfV_u, slowHalfV_v, Nat.gcd_comm, gcd_half he (by rw [Nat.gcd_comm, h.gcd]; exact gcd_odd_of h.par),
      Nat.gcd_comm, h.gcd]

theorem SlowInv.sub {x y : Nat} {s : SlowSt} (h : SlowInv x y s) : SlowInv x y (slowSub s) := by
  have eu := h.eu
  have ev := h.ev
  unfold slowSub; split
  · rename_i hle
    refine ⟨h.par, ?_, ev, ?_⟩
    · simp only; rw [Int.ofNat_sub hle, ← eu, ← ev]; grind
    · simp only; rw [gcd_sub_left hle, h.gcd]
  · rename_i hlt
    refine ⟨h.par, eu, ?_, ?_⟩
    · simp only; rw [Int.ofNat_sub (by omega), ← eu, ← ev]; grind
    · simp only; rw [gcd_sub_right (by omega), h.gcd]

theorem SlowInv.loopU {x y : Nat} (s : SlowSt) (h : SlowInv x y s) : SlowInv x y (slowLoopU x y s) := by
  rw [slowLoopU]; split
  · rename_i hh; exact SlowInv.loopU _ (h.halfU hh.2)
  · exact h
termination_by s.u
decreasing_by simp only [slowHalfU_u]; omega

theorem SlowInv.loopV {x y : Nat} (s : SlowSt) (h : SlowInv x y s) : SlowInv x y (slowLoopV x y s) := by
  rw [slowLoopV]; split
  · rename_i hh; exact SlowInv.loopV _ (h.halfV hh.2)
  · exact h
termination_by s.v
decreasing_by simp only [slowHalfV_v]; omega

theorem SlowInv.pass {x y : Nat} {s : SlowSt} (h : SlowInv x y s) : SlowInv x y (slowPass x y s) :=
  ((h.loopU s).loopV _).sub

theorem SlowInv.top {x y : Nat} (s : SlowSt) (h : SlowInv x y s) (hu : 0 < s.u) (hv : 0 < s.v) :
    SlowInv x y (slowTop x y s) ∧ (slowTop x y s).u = 0 := by
  rw [slowTop_eq x y s hu hv]
  split
  · exact ⟨h.pass, by assumption⟩
  · exact SlowInv.top _ h.pass (by omega) (slowPass_pos x y s hu hv)
termination_by s.u + s.v
decreasing_by exact slowPass_lt x y s hu hv

/-- At the end (`u = 0`), `v` is the gcd and `C x + D y = v`. -/
theorem slowTop_final {x y : Nat} (hpar : x % 2 = 1 ∨ y % 2 = 1) (hx : 0 < x) (hy : 0 < y) :
    (slowTop x y (slowInit x y)).v = Nat.gcd x y ∧
      (slowTop x y (slowInit x y)).C * x + (slowTop x y (slowInit x y)).D * y = Nat.gcd x y := by
  obtain ⟨hi, hu⟩ := SlowInv.top _ (slowInit_inv hpar) hx hy
  have hv : (slowTop x y (slowInit x y)).v = Nat.gcd x y := by
    have := hi.gcd; rwa [hu, Nat.gcd_zero_left] at this
  exact ⟨hv, by rw [hi.ev, hv]⟩

/-- `d` is the inverse of `x` modulo `m`, in `(0, m)`. -/
structure IsInv (x m : Nat) (d : Int) : Prop where
  pos : 0 < d
  lt : d < m
  inv : ((x : Int) * d) % m = 1

theorem isInv_of {x m : Nat} {d : Int} (h0 : 0 ≤ d) (h1 : d < m) (h2 : ((x : Int) * d) % m = 1) : IsInv x m d := by
  refine ⟨?_, h1, h2⟩
  rcases Int.lt_or_eq_of_le h0 with h | h
  · exact h
  · exfalso; rw [← h, Int.mul_zero, Int.zero_emod] at h2; omega

/-- `s_mp_invmod_slow`'s result on `x > 0`, `y > 1` coprime: the inverse of
`x` mod `y` in `(0, y)`. -/
theorem slowRes_ok {x y : Nat} (hx : 0 < x) (hy : 1 < y) (hg : Nat.gcd x y = 1) :
    ∃ d, slowRes x y = some d ∧ IsInv x y d := by
  have hpar : x % 2 = 1 ∨ y % 2 = 1 := by
    have := gcd_odd_of (x := x) (y := y)
    by_cases h : x % 2 = 1
    · exact Or.inl h
    · right
      rcases Nat.mod_two_eq_zero_or_one y with e | e
      · exfalso
        have h2 : 2 ∣ Nat.gcd x y := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_of_mod_eq_zero e)
        rw [hg] at h2; omega
      · exact e
  obtain ⟨hv, he⟩ := slowTop_final hpar hx (by omega)
  rw [hg] at hv he
  refine ⟨norm y (slowTop x y (slowInit x y)).C, ?_, ?_⟩
  · unfold slowRes; rw [if_neg (by omega), if_pos hv]
  · rw [norm_eq y (by omega)]
    refine isInv_of (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ (by omega)) ?_
    rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod, Int.mul_comm]
    have : (slowTop x y (slowInit x y)).C * x = 1 + (-(slowTop x y (slowInit x y)).D) * y := by
      grind
    rw [this, Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by decide) (by omega)

theorem slowRes_err {x y : Nat} (hx : 0 < x) (hy : 0 < y) (hg : Nat.gcd x y ≠ 1) : slowRes x y = none := by
  unfold slowRes
  split
  · rfl
  · rename_i hpar
    have hpar' : x % 2 = 1 ∨ y % 2 = 1 := by omega
    rw [if_neg (by rw [(slowTop_final hpar' hx hy).1]; exact hg)]

/-! ## `s_mp_invmod_fast`: the model (`x = b` odd, `y = a mod b`) -/

/-- The values of `u, v, B, D` in `s_mp_invmod_fast`. -/
structure FastSt where
  u : Nat
  v : Nat
  B : Int
  D : Int

/-- `u = x, v = y, B = 0, D = 1`. -/
def fastInit (x y : Nat) : FastSt := ⟨x, y, 0, 1⟩

/-- One pass of step 4: `u /= 2`; if `B` odd, `B -= x`; `B /= 2`. -/
def fastHalfU (x : Nat) (s : FastSt) : FastSt :=
  { s with u := s.u / 2, B := (if s.B % 2 = 1 then s.B - x else s.B) / 2 }

/-- One pass of step 5: `v /= 2`; if `D` odd, `D -= x`; `D /= 2`. -/
def fastHalfV (x : Nat) (s : FastSt) : FastSt :=
  { s with v := s.v / 2, D := (if s.D % 2 = 1 then s.D - x else s.D) / 2 }

/-- Step 6: `u ≥ v`: `u -= v, B -= D`; else `v -= u, D -= B`. -/
def fastSub (s : FastSt) : FastSt :=
  if s.v ≤ s.u then { s with u := s.u - s.v, B := s.B - s.D } else { s with v := s.v - s.u, D := s.D - s.B }

@[simp] theorem fastHalfU_u (x : Nat) (s : FastSt) : (fastHalfU x s).u = s.u / 2 := rfl
@[simp] theorem fastHalfU_v (x : Nat) (s : FastSt) : (fastHalfU x s).v = s.v := rfl
@[simp] theorem fastHalfV_u (x : Nat) (s : FastSt) : (fastHalfV x s).u = s.u := rfl
@[simp] theorem fastHalfV_v (x : Nat) (s : FastSt) : (fastHalfV x s).v = s.v / 2 := rfl

def fastLoopU (x : Nat) (s : FastSt) : FastSt :=
  if h : s.u ≠ 0 ∧ s.u % 2 = 0 then fastLoopU x (fastHalfU x s) else s
termination_by s.u
decreasing_by simp only [fastHalfU_u]; omega

def fastLoopV (x : Nat) (s : FastSt) : FastSt :=
  if h : s.v ≠ 0 ∧ s.v % 2 = 0 then fastLoopV x (fastHalfV x s) else s
termination_by s.v
decreasing_by simp only [fastHalfV_v]; omega

theorem fastLoopU_uv (x : Nat) (s : FastSt) :
    (fastLoopU x s).u ≤ s.u ∧ (0 < s.u → 0 < (fastLoopU x s).u) ∧ (fastLoopU x s).v = s.v := by
  rw [fastLoopU]; split
  · rename_i h
    have := fastLoopU_uv x (fastHalfU x s)
    simp only [fastHalfU_u, fastHalfU_v] at this; omega
  · omega
termination_by s.u
decreasing_by simp only [fastHalfU_u]; omega

theorem fastLoopV_uv (x : Nat) (s : FastSt) :
    (fastLoopV x s).v ≤ s.v ∧ (0 < s.v → 0 < (fastLoopV x s).v) ∧ (fastLoopV x s).u = s.u := by
  rw [fastLoopV]; split
  · rename_i h
    have := fastLoopV_uv x (fastHalfV x s)
    simp only [fastHalfV_u, fastHalfV_v] at this; omega
  · omega
termination_by s.v
decreasing_by simp only [fastHalfV_v]; omega

def fastPass (x : Nat) (s : FastSt) : FastSt := fastSub (fastLoopV x (fastLoopU x s))

theorem fastPass_lt (x : Nat) (s : FastSt) (hu : 0 < s.u) (hv : 0 < s.v) :
    (fastPass x s).u + (fastPass x s).v < s.u + s.v := by
  obtain ⟨u1, u2, u3⟩ := fastLoopU_uv x s
  obtain ⟨v1, v2, v3⟩ := fastLoopV_uv x (fastLoopU x s)
  unfold fastPass fastSub; split <;> simp only <;> omega

theorem fastPass_pos (x : Nat) (s : FastSt) (hu : 0 < s.u) (hv : 0 < s.v) : 0 < (fastPass x s).v := by
  obtain ⟨u1, u2, u3⟩ := fastLoopU_uv x s
  obtain ⟨v1, v2, v3⟩ := fastLoopV_uv x (fastLoopU x s)
  unfold fastPass fastSub; split <;> simp only <;> omega

def fastTop (x : Nat) (s : FastSt) : FastSt :=
  if h : 0 < s.u ∧ 0 < s.v ∧ (fastPass x s).u ≠ 0 then fastTop x (fastPass x s) else fastPass x s
termination_by s.u + s.v
decreasing_by exact fastPass_lt x s h.1 h.2.1

theorem fastTop_eq (x : Nat) (s : FastSt) (hu : 0 < s.u) (hv : 0 < s.v) :
    fastTop x s = if (fastPass x s).u = 0 then fastPass x s else fastTop x (fastPass x s) := by
  rw [fastTop]; by_cases h : (fastPass x s).u = 0 <;> simp [h, hu, hv]

/-- The result of `s_mp_invmod_fast` on `x = b`, `y = a mod b`, before the
sign is set: `none` for `MP_VAL` (`b` even, `x` or `y` zero, `v ≠ 1`). -/
def fastRes (x y : Nat) : Option Int :=
  if x % 2 = 0 then none
  else if x = 0 ∨ y = 0 then none
  else if (fastTop x (fastInit x y)).v = 1 then some (norm x (fastTop x (fastInit x y)).D)
  else none

/-- The invariant of `s_mp_invmod_fast` (HAC 14.64): `u ≡ B y`, `v ≡ D y`
(mod `x`), the gcd kept, `x` odd. -/
structure FastInv (x y : Nat) (s : FastSt) : Prop where
  x_odd : x % 2 = 1
  eu : (x : Int) ∣ (s.u : Int) - s.B * y
  ev : (x : Int) ∣ (s.v : Int) - s.D * y
  gcd : Nat.gcd s.u s.v = Nat.gcd x y

theorem fastInit_inv {x y : Nat} (hx : x % 2 = 1) : FastInv x y (fastInit x y) :=
  ⟨hx, by simp [fastInit], by simp [fastInit], rfl⟩

theorem fast_half_coef {x y u : Nat} {B : Int} (hx : x % 2 = 1) (he : (x : Int) ∣ (u : Int) - B * y)
    (hu : u % 2 = 0) :
    (x : Int) ∣ ((u / 2 : Nat) : Int) - ((if B % 2 = 1 then B - x else B) / 2) * y := by
  apply int_dvd_of_dvd_two_mul hx
  split
  · have eb : B - x = 2 * ((B - x) / 2) := by omega
    have : 2 * (((u / 2 : Nat) : Int) - (B - ↑x) / 2 * ↑y) = ((u : Int) - B * y) + x * y := by
      have hu2 : 2 * ((u / 2 : Nat) : Int) = u := by omega
      rw [Int.mul_sub, hu2, ← Int.mul_assoc, ← eb]; grind
    rw [this]; exact Int.dvd_add he (Int.dvd_mul_right _ _)
  · rename_i hb
    have eb : B = 2 * (B / 2) := by omega
    have : 2 * (((u / 2 : Nat) : Int) - B / 2 * ↑y) = (u : Int) - B * y := by
      have hu2 : 2 * ((u / 2 : Nat) : Int) = u := by omega
      rw [Int.mul_sub, hu2, ← Int.mul_assoc, ← eb]
    rw [this]; exact he

theorem FastInv.halfU {x y : Nat} {s : FastSt} (h : FastInv x y s) (he : s.u % 2 = 0) :
    FastInv x y (fastHalfU x s) := by
  have hg : Nat.gcd x y % 2 = 1 := gcd_odd_of (Or.inl h.x_odd)
  refine ⟨h.x_odd, fast_half_coef h.x_odd h.eu he, h.ev, ?_⟩
  simp only [fastHalfU]; rw [gcd_half he (by rw [h.gcd]; exact hg), h.gcd]

theorem FastInv.halfV {x y : Nat} {s : FastSt} (h : FastInv x y s) (he : s.v % 2 = 0) :
    FastInv x y (fastHalfV x s) := by
  have hg : Nat.gcd x y % 2 = 1 := gcd_odd_of (Or.inl h.x_odd)
  refine ⟨h.x_odd, h.eu, fast_half_coef h.x_odd h.ev he, ?_⟩
  simp only [fastHalfV]
  rw [Nat.gcd_comm, gcd_half he (by rw [Nat.gcd_comm, h.gcd]; exact hg), Nat.gcd_comm, h.gcd]

theorem FastInv.sub {x y : Nat} {s : FastSt} (h : FastInv x y s) : FastInv x y (fastSub s) := by
  unfold fastSub; split
  · rename_i hle
    refine ⟨h.x_odd, ?_, h.ev, ?_⟩
    · simp only
      have : (((s.u - s.v : Nat)) : Int) - (s.B - s.D) * y = ((s.u : Int) - s.B * y) - ((s.v : Int) - s.D * y) := by
        rw [Int.ofNat_sub hle]; grind
      rw [this]; exact Int.dvd_sub h.eu h.ev
    · simp only; rw [gcd_sub_left hle, h.gcd]
  · rename_i hlt
    refine ⟨h.x_odd, h.eu, ?_, ?_⟩
    · simp only
      have : (((s.v - s.u : Nat)) : Int) - (s.D - s.B) * y = ((s.v : Int) - s.D * y) - ((s.u : Int) - s.B * y) := by
        rw [Int.ofNat_sub (by omega)]; grind
      rw [this]; exact Int.dvd_sub h.ev h.eu
    · simp only; rw [gcd_sub_right (by omega), h.gcd]

theorem FastInv.loopU {x y : Nat} (s : FastSt) (h : FastInv x y s) : FastInv x y (fastLoopU x s) := by
  rw [fastLoopU]; split
  · rename_i hh; exact FastInv.loopU _ (h.halfU hh.2)
  · exact h
termination_by s.u
decreasing_by simp only [fastHalfU_u]; omega

theorem FastInv.loopV {x y : Nat} (s : FastSt) (h : FastInv x y s) : FastInv x y (fastLoopV x s) := by
  rw [fastLoopV]; split
  · rename_i hh; exact FastInv.loopV _ (h.halfV hh.2)
  · exact h
termination_by s.v
decreasing_by simp only [fastHalfV_v]; omega

theorem FastInv.pass {x y : Nat} {s : FastSt} (h : FastInv x y s) : FastInv x y (fastPass x s) :=
  ((h.loopU s).loopV _).sub

theorem FastInv.top {x y : Nat} (s : FastSt) (h : FastInv x y s) (hu : 0 < s.u) (hv : 0 < s.v) :
    FastInv x y (fastTop x s) ∧ (fastTop x s).u = 0 := by
  rw [fastTop_eq x s hu hv]
  split
  · exact ⟨h.pass, by assumption⟩
  · exact FastInv.top _ h.pass (by omega) (fastPass_pos x s hu hv)
termination_by s.u + s.v
decreasing_by exact fastPass_lt x s hu hv

theorem fastTop_final {x y : Nat} (hx : x % 2 = 1) (hy : 0 < y) :
    (fastTop x (fastInit x y)).v = Nat.gcd x y ∧
      (x : Int) ∣ (Nat.gcd x y : Int) - (fastTop x (fastInit x y)).D * y := by
  obtain ⟨hi, hu⟩ := FastInv.top _ (fastInit_inv (y := y) hx) (by simp [fastInit]; omega) (by simp [fastInit]; omega)
  have hv : (fastTop x (fastInit x y)).v = Nat.gcd x y := by
    have := hi.gcd; rwa [hu, Nat.gcd_zero_left] at this
  exact ⟨hv, by have := hi.ev; rwa [hv] at this⟩

theorem fastRes_ok {x y : Nat} (hx : x % 2 = 1) (hx1 : 1 < x) (hy : 0 < y) (hg : Nat.gcd x y = 1) :
    ∃ d, fastRes x y = some d ∧ IsInv y x d := by
  obtain ⟨hv, he⟩ := fastTop_final hx hy
  rw [hg] at hv he
  have hmod : ((y : Int) * norm x (fastTop x (fastInit x y)).D) % x = 1 := by
    rw [norm_eq x (by omega), Int.mul_emod, Int.emod_emod, ← Int.mul_emod, Int.mul_comm]
    obtain ⟨k, hk⟩ := he
    have : (fastTop x (fastInit x y)).D * y = 1 + (-k) * x := by
      have : ((1 : Nat) : Int) = 1 := rfl
      grind
    rw [this, Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by decide) (by omega)
  refine ⟨norm x (fastTop x (fastInit x y)).D, ?_, ?_⟩
  · unfold fastRes; rw [if_neg (by omega), if_neg (by omega), if_pos hv]
  · refine isInv_of ?_ ?_ hmod
    · rw [norm_eq x (by omega)]; exact Int.emod_nonneg _ (by omega)
    · rw [norm_eq x (by omega)]; exact Int.emod_lt_of_pos _ (by omega)

theorem fastRes_err {x y : Nat} (hg : Nat.gcd x y ≠ 1) : fastRes x y = none := by
  unfold fastRes
  split
  · rfl
  · split
    · rfl
    · rename_i hx hxy
      rw [if_neg (by rw [(fastTop_final (by omega) (by omega)).1]; exact hg)]

/-! ## Bounds: `u`, `v` never grow -/

theorem slowPass_le (x y : Nat) (s : SlowSt) : (slowPass x y s).u ≤ s.u ∧ (slowPass x y s).v ≤ s.v := by
  obtain ⟨u1, _, u3⟩ := slowLoopU_uv x y s
  obtain ⟨v1, _, v3⟩ := slowLoopV_uv x y (slowLoopU x y s)
  unfold slowPass slowSub; split <;> simp only <;> omega

theorem fastPass_le (x : Nat) (s : FastSt) : (fastPass x s).u ≤ s.u ∧ (fastPass x s).v ≤ s.v := by
  obtain ⟨u1, _, u3⟩ := fastLoopU_uv x s
  obtain ⟨v1, _, v3⟩ := fastLoopV_uv x (fastLoopU x s)
  unfold fastPass fastSub; split <;> simp only <;> omega

end Gcd

/-! ## `mp_invmod`, `s_mp_invmod_fast`, `s_mp_invmod_slow`: contracts -/

/-- An `MP_VAL` exit: `c` untouched. -/
structure InvmodErr (c c' : MpInt) (ret : Int) : Prop where
  ret : ret = Layout.mpVal
  same : c' = c

/-- `y = a mod b` (`mp_mod(a, b, &y)`), as a `Nat` (`b > 0`). -/
def invmodRem (a b : MpInt) : Nat := (a.val % b.val).toNat

/-- What `s_mp_invmod_fast(a, b, c)` leaves (`b` positive): on `MP_VAL`
(`fastRes = none`) `c` untouched; otherwise `c` is `D` normalised
into `[0, b)` (an `mp_int` from `mp_add`/`mp_sub`: shaped and clamped) with
its sign then overwritten by `a->sign`. -/
structure InvmodFastPost (a b c c' : MpInt) (ret : Int) : Prop where
  err : Gcd.fastRes b.mag (invmodRem a b) = none → InvmodErr c c' ret
  ret_ok : ∀ d, Gcd.fastRes b.mag (invmodRem a b) = some d → ret = Layout.mpOkay
  shape : ∀ d, Gcd.fastRes b.mag (invmodRem a b) = some d → c'.Shape
  top : ∀ d, Gcd.fastRes b.mag (invmodRem a b) = some d → 0 < c'.used → c'.digit (c'.used - 1) ≠ 0
  mag : ∀ d, Gcd.fastRes b.mag (invmodRem a b) = some d → c'.mag = d.toNat
  sign : ∀ d, Gcd.fastRes b.mag (invmodRem a b) = some d → c'.sign = a.sign

/-- What `s_mp_invmod_slow(a, b, c)` leaves (`b` positive and even, the case
`mp_invmod` calls): on `MP_VAL` `c` untouched; otherwise `C` normalised into
`[0, b)`, valid. -/
structure InvmodSlowPost (a b c c' : MpInt) (ret : Int) : Prop where
  err : Gcd.slowRes (invmodRem a b) b.mag = none → InvmodErr c c' ret
  ret_ok : ∀ d, Gcd.slowRes (invmodRem a b) b.mag = some d → ret = Layout.mpOkay
  valid : ∀ d, Gcd.slowRes (invmodRem a b) b.mag = some d → c'.Valid
  val : ∀ d, Gcd.slowRes (invmodRem a b) b.mag = some d → c'.val = d

/-- What `mp_invmod(a, b, c)` leaves, by the branch it takes. -/
structure InvmodPost (a b c c' : MpInt) (ret : Int) : Prop where
  bad : (b.sign = Layout.mpNeg ∨ b.mag ≤ 1) → InvmodErr c c' ret
  fast : b.sign ≠ Layout.mpNeg → 1 < b.mag → b.mag % 2 = 1 → InvmodFastPost a b c c' ret
  slow : b.sign ≠ Layout.mpNeg → 1 < b.mag → b.mag % 2 = 0 → InvmodSlowPost a b c c' ret

theorem MpInt.val_of_pos {b : MpInt} (hb : b.sign ≠ Layout.mpNeg) : b.val = b.mag := by
  unfold MpInt.val; simp [hb]

theorem invmodRem_eq {a b : MpInt} (hb : b.sign ≠ Layout.mpNeg) (hb1 : 1 < b.mag) :
    (invmodRem a b : Int) = a.val % b.val := by
  unfold invmodRem
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by rw [MpInt.val_of_pos hb]; omega))]

theorem invmodRem_lt {a b : MpInt} (hb : b.sign ≠ Layout.mpNeg) (hb1 : 1 < b.mag) : invmodRem a b < b.mag := by
  have h := invmodRem_eq (a := a) hb hb1
  have : a.val % b.val < b.val := Int.emod_lt_of_pos _ (by rw [MpInt.val_of_pos hb]; omega)
  rw [MpInt.val_of_pos hb] at this h; omega

theorem mod_mul_congr (a d b y : Int) (hy : y = a % b) : (a * d) % b = (y * d) % b := by
  rw [Int.mul_emod, Int.mul_emod y, hy, Int.emod_emod]

theorem MpInt.sign_ne_neg_of_nonneg {a : MpInt} (ha : a.Valid) (h : 0 ≤ a.val) : a.sign ≠ Layout.mpNeg := by
  intro hn
  have hm0 : a.mag = 0 := by unfold MpInt.val at h; rw [if_pos hn] at h; omega
  rcases Nat.eq_zero_or_pos a.used with e | e
  · rw [ha.zero_pos e] at hn; simp [Layout.mpZpos, Layout.mpNeg] at hn
  · have h1 := MpInt.mag_ge ha e
    have h2 : 0 < radix ^ (a.used - 1) := Nat.pow_pos radix_pos
    omega

theorem MpInt.sign_neg_of_neg {a : MpInt} (h : a.val < 0) : a.sign = Layout.mpNeg := by
  unfold MpInt.val at h; split at h
  · assumption
  · omega

/-- The fast path's success: `c` valid with value `±d`, the sign of `a`. -/
theorem InvmodFastPost.result {a b c c' : MpInt} {ret d : Int} (ha : a.Valid) (hp : InvmodFastPost a b c c' ret)
    (hd : Gcd.fastRes b.mag (invmodRem a b) = some d) (hd0 : 0 < d) :
    ret = Layout.mpOkay ∧ c'.Valid ∧ c'.val = if a.sign = Layout.mpNeg then -d else d := by
  have hmag := hp.mag d hd
  have hused : 0 < c'.used := by
    rcases Nat.eq_zero_or_pos c'.used with e | e
    · exfalso; have := MpInt.mag_used_zero e; omega
    · exact e
  have hs : c'.sign = Layout.mpZpos ∨ c'.sign = Layout.mpNeg := by rw [hp.sign d hd]; exact ha.sign_ok
  have hv : c'.Valid :=
    { toShape := hp.shape d hd
      top := hp.top d hd
      sign_ok := hs
      zero_pos := fun e => absurd e (by omega) }
  refine ⟨hp.ret_ok d hd, hv, ?_⟩
  unfold MpInt.val; rw [hp.sign d hd, hmag, Int.toNat_of_nonneg (by omega)]

/-- `mp_invmod` on a modulus `b > 1` with `gcd(a mod b, b) = 1`, when `a ≥ 0`
or `b` even: success, and `c` is the inverse of `a` in `[0, b)`. -/
theorem InvmodPost.spec_ok {a b c c' : MpInt} {ret : Int} (ha : a.Valid)
    (hb1 : 1 < b.val) (hg : Nat.gcd (invmodRem a b) b.mag = 1)
    (hsg : 0 ≤ a.val ∨ b.mag % 2 = 0) (h : InvmodPost a b c c' ret) :
    ret = Layout.mpOkay ∧ c'.Valid ∧ 0 ≤ c'.val ∧ c'.val < b.val ∧ (a.val * c'.val) % b.val = 1 := by
  have hbs : b.sign ≠ Layout.mpNeg := by
    intro hn; unfold MpInt.val at hb1; rw [if_pos hn] at hb1; omega
  have hbv := MpInt.val_of_pos hbs
  have hbm : 1 < b.mag := by omega
  have hr := invmodRem_eq (a := a) hbs hbm
  have hrl := invmodRem_lt (a := a) hbs hbm
  have hx : 0 < invmodRem a b := by
    rcases Nat.eq_zero_or_pos (invmodRem a b) with e | e
    · exfalso; rw [e, Nat.gcd_zero_left] at hg; omega
    · exact e
  rcases Nat.mod_two_eq_zero_or_one b.mag with he | ho
  · have hp := h.slow hbs hbm he
    obtain ⟨d, hd, hi⟩ := Gcd.slowRes_ok hx hbm hg
    have d0 : 0 ≤ d := Int.le_of_lt hi.pos
    have d1 := hi.lt
    have d2 := hi.inv
    refine ⟨hp.ret_ok d hd, hp.valid d hd, by rw [hp.val d hd]; exact d0, by rw [hp.val d hd, hbv]; exact d1, ?_⟩
    rw [hp.val d hd, mod_mul_congr a.val d b.val _ hr, hbv]; exact d2
  · have hp := h.fast hbs hbm ho
    have hg' : Nat.gcd b.mag (invmodRem a b) = 1 := by rw [Nat.gcd_comm]; exact hg
    obtain ⟨d, hd, hi⟩ := Gcd.fastRes_ok ho hbm hx hg'
    have d0 := hi.pos
    have d1 := hi.lt
    have d2 := hi.inv
    have hapos : a.sign ≠ Layout.mpNeg := MpInt.sign_ne_neg_of_nonneg ha (by omega)
    obtain ⟨r1, r2, r3⟩ := hp.result ha hd d0
    rw [if_neg hapos] at r3
    refine ⟨r1, r2, by rw [r3]; omega, by rw [r3, hbv]; omega, ?_⟩
    rw [r3, mod_mul_congr a.val d b.val _ hr, hbv]; exact d2

/-- **The sign quirk of `s_mp_invmod_fast`**: for an odd modulus `b > 1` and
`a < 0` with `gcd(a mod b, b) = 1`, `mp_invmod` succeeds but returns the
*negated* inverse: `c ∈ (-b, 0)` and `a · (-c) ≡ 1 (mod b)`, i.e.
`a · c ≡ -1`. (`mp_invmod(-3, 7) = -2` on the real library.) -/
theorem InvmodPost.spec_neg_odd {a b c c' : MpInt} {ret : Int} (ha : a.Valid)
    (hb1 : 1 < b.val) (hg : Nat.gcd (invmodRem a b) b.mag = 1)
    (hneg : a.val < 0) (ho : b.mag % 2 = 1) (h : InvmodPost a b c c' ret) :
    ret = Layout.mpOkay ∧ c'.Valid ∧ -b.val < c'.val ∧ c'.val < 0 ∧ (a.val * -c'.val) % b.val = 1 ∧
      (a.val * c'.val + 1) % b.val = 0 := by
  have hbs : b.sign ≠ Layout.mpNeg := by
    intro hn; unfold MpInt.val at hb1; rw [if_pos hn] at hb1; omega
  have hbv := MpInt.val_of_pos hbs
  have hbm : 1 < b.mag := by omega
  have hr := invmodRem_eq (a := a) hbs hbm
  have hx : 0 < invmodRem a b := by
    rcases Nat.eq_zero_or_pos (invmodRem a b) with e | e
    · exfalso; rw [e, Nat.gcd_zero_left] at hg; omega
    · exact e
  have hp := h.fast hbs hbm ho
  have hg' : Nat.gcd b.mag (invmodRem a b) = 1 := by rw [Nat.gcd_comm]; exact hg
  obtain ⟨d, hd, hi⟩ := Gcd.fastRes_ok ho hbm hx hg'
  have d0 := hi.pos
  have d1 := hi.lt
  have d2 := hi.inv
  obtain ⟨r1, r2, r3⟩ := hp.result ha hd d0
  rw [if_pos (MpInt.sign_neg_of_neg hneg)] at r3
  have hinv : (a.val * -c'.val) % b.val = 1 := by
    rw [r3, Int.neg_neg, mod_mul_congr a.val d b.val _ hr, hbv]; exact d2
  refine ⟨r1, r2, by rw [r3, hbv]; omega, by rw [r3]; omega, hinv, ?_⟩
  have e : a.val * c'.val + 1 = -(a.val * -c'.val - 1) := by grind
  have hd1 : b.val ∣ a.val * -c'.val - 1 := Int.dvd_of_emod_eq_zero (by
    rw [Int.sub_emod, hinv, Int.emod_eq_of_lt (by decide) hb1]; simp)
  rw [e]; exact Int.emod_eq_zero_of_dvd (Int.dvd_neg.mpr hd1)

/-- `mp_invmod` fails with `MP_VAL`, leaving `c`, exactly when `b` is not a
positive modulus above `1` or `a mod b` is not invertible. -/
theorem InvmodPost.spec_err {a b c c' : MpInt} {ret : Int}
    (hbad : b.sign = Layout.mpNeg ∨ b.mag ≤ 1 ∨ Nat.gcd (invmodRem a b) b.mag ≠ 1)
    (h : InvmodPost a b c c' ret) : ret = Layout.mpVal ∧ c' = c := by
  by_cases h1 : b.sign = Layout.mpNeg ∨ b.mag ≤ 1
  · exact ⟨(h.bad h1).ret, (h.bad h1).same⟩
  · have hbs : b.sign ≠ Layout.mpNeg := fun e => h1 (Or.inl e)
    have hbm : 1 < b.mag := by omega
    have hg : Nat.gcd (invmodRem a b) b.mag ≠ 1 := by omega
    rcases Nat.mod_two_eq_zero_or_one b.mag with he | ho
    · have hp := h.slow hbs hbm he
      have hn : Gcd.slowRes (invmodRem a b) b.mag = none := by
        rcases Nat.eq_zero_or_pos (invmodRem a b) with e | e
        · unfold Gcd.slowRes; rw [if_pos (by omega)]
        · exact Gcd.slowRes_err e (by omega) hg
      exact ⟨(hp.err hn).ret, (hp.err hn).same⟩
    · have hp := h.fast hbs hbm ho
      have hn := Gcd.fastRes_err (x := b.mag) (y := invmodRem a b) (by rw [Nat.gcd_comm]; exact hg)
      exact ⟨(hp.err hn).ret, (hp.err hn).same⟩

end Tom
