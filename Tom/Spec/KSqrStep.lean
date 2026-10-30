import Tom.Spec.MpSqrStep
import Tom.Spec.Mont
import Tom.Spec.Set
import Tom.Spec.Init
import Tom.Spec.DigitShift
import Tom.Spec.Sub
import Tom.Spec.MpIntU

/-!
# `s_mp_karatsuba_sqr`'s model steps

At the level the assembly sees them (digit functions, magnitudes, `used` bounds):

* the copy loops: `lowF a i` (`x0.dp[j] = a->dp[j]`, `j < i`) and `highF a B k`
  (`x1.dp[j] = a->dp[B + j]`, `j < k`), one store a step (`lowF_upd`, `highF_upd`);
* the halves after the `used` stores: `x0r` (shaped, `|x0| = |a| mod R`), `x1r` (valid,
  `|x1| = |a| / R`), `R = radix^B`;
* bounds: a valid `t` with `|t| < radix^k` has `t.used ≤ k` (`used_le_of_lt`), used for every
  D5 room on the way;
* the recomposition (`ksqr_val`, from `karatsuba_sqr_val`).
-/

namespace Tom.KSqr

open MpInt

/-! ## The copy loops -/

/-- The low `i` digits of `a` (zero above). -/
def lowF (a : MpInt) (i : Nat) : Nat → Nat := fun j => if j < i then a.digit j else 0

/-- The digits `B, B + 1, …, B + k - 1` of `a`, shifted down (zero above). -/
def highF (a : MpInt) (B k : Nat) : Nat → Nat := fun j => if j < k then a.digit (B + j) else 0

theorem zero_lowF (a : MpInt) (n : Nat) : (MpInt.zeroN n).digit = lowF a 0 := by
  funext j; simp [lowF, MpInt.zeroN_digit]

theorem zero_highF (a : MpInt) (B n : Nat) : (MpInt.zeroN n).digit = highF a B 0 := by
  funext j; simp [highF, MpInt.zeroN_digit]

theorem lowF_upd (a : MpInt) (i : Nat) : Mont.upd (lowF a i) i (a.digit i) = lowF a (i + 1) := by
  funext j; unfold Mont.upd lowF
  by_cases h : j = i
  · subst h; simp
  · by_cases h' : j < i
    · simp [h, h', show j < i + 1 by omega]
    · simp [h, h', show ¬ j < i + 1 by omega]

theorem highF_upd (a : MpInt) (B k : Nat) :
    Mont.upd (highF a B k) k (a.digit (B + k)) = highF a B (k + 1) := by
  funext j; unfold Mont.upd highF
  by_cases h : j = k
  · subst h; simp
  · by_cases h' : j < k
    · simp [h, h', show j < k + 1 by omega]
    · simp [h, h', show ¬ j < k + 1 by omega]

/-! ## The halves -/

/-- `x0` after the copy and `x0.used := B` (before `mp_clamp`). -/
def x0r (a : MpInt) (B n : Nat) : MpInt := MpInt.ofDigits B n Layout.mpZpos (lowF a B)

/-- `x1` after the copy and `x1.used := a->used - B`. -/
def x1r (a : MpInt) (B n : Nat) : MpInt := MpInt.ofDigits (a.used - B) n Layout.mpZpos (highF a B (a.used - B))

theorem x0r_shape {a : MpInt} (ha : a.ShapeU) {B n : Nat} (hB : B ≤ n) (hn : n < 2 ^ 31) :
    (x0r a B n).Shape where
  len := MpInt.ofDigits_len _ _ _ _
  used_le := hB
  alloc_lt := hn
  digit_lt i := by
    rw [x0r, MpInt.ofDigits_digit]; unfold lowF
    split
    · split
      · exact ha.digit_lt i
      · exact radix_pos
    · exact radix_pos
  high_zero i hi := by
    rw [x0r, MpInt.ofDigits_digit]; unfold lowF
    simp only [x0r, MpInt.ofDigits] at hi
    split
    · rw [if_neg (by omega)]
    · rfl

theorem natUpTo_lowF (a : MpInt) (B : Nat) : natUpTo (lowF a B) B = natUpTo a.digit B :=
  natUpTo_congr B fun i hi => by simp [lowF, hi]

/-- `|a| = R |x1| + |x0|`. -/
theorem mag_split {a : MpInt} {B : Nat} (hB : B ≤ a.used) :
    a.mag = natUpTo a.digit B + radix ^ B * natUpTo (fun i => a.digit (B + i)) (a.used - B) := by
  unfold MpInt.mag
  conv => lhs; rw [show a.used = B + (a.used - B) by omega]
  exact natUpTo_split _ B _

theorem x0r_mag {a : MpInt} (ha : a.ShapeU) {B n : Nat} (hBu : B ≤ a.used) (hBn : B ≤ n) :
    (x0r a B n).mag = a.mag % radix ^ B := by
  have h1 : (x0r a B n).mag = natUpTo a.digit B := by
    show natUpTo (x0r a B n).digit B = _
    exact natUpTo_congr B fun i hi => by
      rw [x0r, MpInt.ofDigits_digit, if_pos (by omega)]; simp [lowF, hi]
  rw [h1, mag_split hBu, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (natUpTo_lt _ ha.digit_lt B)]

theorem x1r_mag {a : MpInt} (ha : a.ShapeU) {B n : Nat} (hBu : B ≤ a.used) (hn : a.used - B ≤ n) :
    (x1r a B n).mag = a.mag / radix ^ B := by
  have h1 : (x1r a B n).mag = natUpTo (fun i => a.digit (B + i)) (a.used - B) := by
    show natUpTo (x1r a B n).digit (a.used - B) = _
    exact natUpTo_congr _ fun i hi => by
      rw [x1r, MpInt.ofDigits_digit, if_pos (by omega)]; simp [highF, hi]
  rw [h1, mag_split hBu, Nat.add_mul_div_left _ _ (Nat.pow_pos radix_pos),
    Nat.div_eq_of_lt (natUpTo_lt _ ha.digit_lt B), Nat.zero_add]

theorem x1r_valid {a : MpInt} (ha : a.ValidU) {B n : Nat} (hB : B < a.used) (hn : a.used - B ≤ n)
    (hn' : n < 2 ^ 31) : (x1r a B n).Valid where
  len := MpInt.ofDigits_len _ _ _ _
  used_le := hn
  alloc_lt := hn'
  digit_lt i := by
    rw [x1r, MpInt.ofDigits_digit]; unfold highF
    split
    · split
      · exact ha.digit_lt _
      · exact radix_pos
    · exact radix_pos
  high_zero i hi := by
    rw [x1r, MpInt.ofDigits_digit]; unfold highF
    simp only [x1r, MpInt.ofDigits] at hi
    split
    · rw [if_neg (by omega)]
    · rfl
  top _ := by
    show (x1r a B n).digit (a.used - B - 1) ≠ 0
    rw [x1r, MpInt.ofDigits_digit, if_pos (by omega)]; unfold highF
    rw [if_pos (by omega), show B + (a.used - B - 1) = a.used - 1 by omega]
    exact ha.top (by omega)
  sign_ok := .inl rfl
  zero_pos _ := rfl

/-! ## Bounds -/

/-- A valid `t` below `radix^k` has at most `k` digits. -/
theorem used_le_of_lt {t : MpInt} (ht : t.Valid) {k : Nat} (h : t.mag < radix ^ k) : t.used ≤ k := by
  by_cases hu : t.used = 0
  · omega
  · have := MpInt.mag_ge ht (by omega)
    refine Nat.le_of_not_lt fun hk => ?_
    have : radix ^ k ≤ radix ^ (t.used - 1) := Nat.pow_le_pow_right radix_pos (by omega)
    omega

theorem mag_lt (t : MpInt) (ht : t.ShapeU) : t.mag < radix ^ t.used := natUpTo_lt _ ht.digit_lt _

/-- Valid and below in magnitude: below in `used`. -/
theorem used_mono {s t : MpInt} (hs : s.Valid) (ht : t.Valid) (h : s.mag ≤ t.mag) : s.used ≤ t.used :=
  used_le_of_lt hs (Nat.lt_of_le_of_lt h (mag_lt t ht.toShapeU))

/-- `mp_sqr`'s result, as a magnitude. -/
theorem sqr_mag {x y : MpInt} (h : SqrPost x y) (hs : y.sign = Layout.mpZpos) : y.mag = x.mag * x.mag := by
  have hv := h.val
  unfold MpInt.val at hv
  rw [if_neg (by rw [hs]; decide)] at hv
  have : (y.mag : Int) = (x.mag : Int) * x.mag := by
    rw [hv]; split <;> simp [Int.neg_mul_neg]
  exact_mod_cast this

/-- A valid result of nonnegative value: its magnitude. -/
theorem mag_of_val {c : MpInt} (hc : c.Valid) {n : Nat} (h : c.val = (n : Int)) : c.mag = n := by
  unfold MpInt.val at h
  split at h
  · have : (c.mag : Int) = 0 := by omega
    have : n = 0 := by omega
    omega
  · exact_mod_cast h

/-- The value of a nonnegative `mp_int`. -/
theorem val_zpos {c : MpInt} (hs : c.sign = Layout.mpZpos) : c.val = (c.mag : Int) := by
  unfold MpInt.val; rw [if_neg (by rw [hs]; decide)]

/-! ## The recomposition -/

/-- `x0x0 + ((x1 + x0)² − (x0x0 + x1x1)) R + x1x1 R² = |a|²` with `x0 = |a| mod R`,
`x1 = |a| / R`. -/
theorem ksqr_val (A R : Nat) :
    A % R * (A % R) + ((A / R + A % R) * (A / R + A % R) - (A % R * (A % R) + A / R * (A / R))) * R +
      A / R * (A / R) * (R * R) = A * A := by
  have hA : A = A / R * R + A % R := (Nat.div_add_mod' A R).symm
  have := karatsuba_sqr_val (A % R) (A / R) R
  rw [← hA] at this
  exact this.symm

/-- `s_mp_sub(&t1, &t2, &t1)` is defined. -/
theorem ksqr_ge (X0 X1 : Nat) : X0 * X0 + X1 * X1 ≤ (X1 + X0) * (X1 + X0) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega

/-! ## `x0` after `mp_clamp` -/

/-- `x0` clamped: `x0r` with `used` lowered past its zero top digits. -/
def x0c (a : MpInt) (B n : Nat) : MpInt := { x0r a B n with used := clampUsed (x0r a B n).digit B }

theorem x0c_clamp (a : MpInt) (B n : Nat) : ClampPost (x0r a B n) (x0c a B n) where
  digits := rfl
  alloc := rfl
  used := rfl
  sign := by show Layout.mpZpos = _; split <;> rfl

theorem x0c_eq {a : MpInt} {B n : Nat} {t : MpInt} (h : ClampPost (x0r a B n) t) : t = x0c a B n := by
  obtain ⟨u', al, sg, ds⟩ := t
  have hd := h.digits; have ha := h.alloc; have hu := h.used; have hs := h.sign
  simp only at hd ha hu hs
  simp only [x0c, MpInt.mk.injEq]
  refine ⟨hu, ha, ?_, hd⟩
  rw [hs]; split <;> rfl

theorem x0c_spec {a : MpInt} (ha : a.ShapeU) {B n : Nat} (hBu : B ≤ a.used) (hBn : B ≤ n) (hn : n < 2 ^ 31) :
    (x0c a B n).Valid ∧ (x0c a B n).mag = a.mag % radix ^ B := by
  have := ClampPost.spec (x0r_shape ha hBn hn) (.inl rfl) (x0c_clamp a B n)
  exact ⟨this.1, this.2.trans (x0r_mag ha hBu hBn)⟩

theorem x0c_used (a : MpInt) (B n : Nat) : (x0c a B n).used ≤ B := clampUsed_le _ _

/-! ## Digit bounds along the way -/

theorem lo_lt (A B : Nat) : A % radix ^ B < radix ^ B := Nat.mod_lt _ (Nat.pow_pos radix_pos)

theorem hi_lt {a : MpInt} (ha : a.ShapeU) {B : Nat} (hB : B ≤ a.used) : a.mag / radix ^ B < radix ^ (a.used - B) := by
  have h := mag_lt a ha
  rw [show a.used = B + (a.used - B) by omega, Nat.pow_add] at h
  exact Nat.div_lt_of_lt_mul h

theorem sq_lt {X k : Nat} (h : X < radix ^ k) : X * X < radix ^ (2 * k) := by
  rw [Nat.two_mul, Nat.pow_add]; exact Nat.mul_lt_mul_of_lt_of_le h (Nat.le_of_lt h) (by omega)

/-- A square below `radix^(2k)` has at most `2k` digits. -/
theorem sq_used {V : MpInt} (hv : V.Valid) {X k : Nat} (hm : V.mag = X * X) (hx : X < radix ^ k) :
    V.used ≤ 2 * k :=
  used_le_of_lt hv (hm ▸ sq_lt hx)

theorem pow_two_B (B : Nat) : radix ^ (2 * B) = radix ^ B * radix ^ B := by rw [Nat.two_mul, Nat.pow_add]

/-- `t1 = x1 + x0`. -/
theorem t1_add {a : MpInt} (ha : a.Valid) {B NX NY NT : Nat} (hB : B < a.used) (h2 : B ≤ a.used - B)
    (hNX : B ≤ NX) (hNX' : NX < 2 ^ 31) (hNY : a.used - B ≤ NY) (hNY' : NY < 2 ^ 31) (hNT : a.used - B + 1 ≤ NT)
    (hNT' : NT < 2 ^ 31) {t1 : MpInt} (h : SAddPost (x1r a B NY) (x0c a B NX) (MpInt.zeroN NT) t1) :
    t1.Valid ∧ t1.mag = a.mag / radix ^ B + a.mag % radix ^ B ∧ t1.used ≤ a.used - B + 1 := by
  have hx1 := x1r_valid ha.toU hB hNY hNY'
  have hx0 := x0c_spec ha.toShapeU (by omega) hNX hNX'
  have hu0 := x0c_used a B NX
  have hu1 : (x1r a B NY).used = a.used - B := rfl
  have := SAddPost.spec hx1.toShape hx0.1.toShape (by show _ ≤ NT; omega) hNT' (.inl rfl) h
  refine ⟨this.1, by rw [this.2, x1r_mag ha.toShapeU (by omega) hNY, hx0.2], ?_⟩
  rw [h.used]; exact Nat.le_trans (clampUsed_le _ _) (by omega)

/-- `t1 = (x1 + x0)² − (x0x0 + x1x1) = 2 x0 x1` has at most `a->used + 1` digits. -/
theorem t1_used {a T : MpInt} (ha : a.Shape) {B : Nat} (hB : B ≤ a.used) (hv : T.Valid)
    (hm : T.mag = (a.mag / radix ^ B + a.mag % radix ^ B) * (a.mag / radix ^ B + a.mag % radix ^ B) -
      (a.mag % radix ^ B * (a.mag % radix ^ B) + a.mag / radix ^ B * (a.mag / radix ^ B))) :
    T.used ≤ a.used + 1 := by
  refine used_le_of_lt hv ?_
  have h0 := lo_lt a.mag B
  have h1 := hi_lt ha.toShapeU hB
  generalize a.mag / radix ^ B = X1 at hm h1
  generalize a.mag % radix ^ B = X0 at hm h0
  have e : (X1 + X0) * (X1 + X0) - (X0 * X0 + X1 * X1) = 2 * (X0 * X1) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm X1 X0]; omega
  rw [hm, e]
  have h01 : X0 * X1 < radix ^ a.used := by
    rw [show a.used = B + (a.used - B) by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le h0 (Nat.le_of_lt h1) (by have := Nat.pow_pos (n := a.used - B) radix_pos; omega)
  rw [Nat.pow_succ]
  have : 2 ≤ radix := by decide
  calc 2 * (X0 * X1) < 2 * radix ^ a.used := by omega
    _ ≤ radix ^ a.used * radix := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ this

/-- After `mp_lshd(&t1, B)`: at most `a->used + 1 + B` digits. -/
theorem t1s_used {a T : MpInt} (ha : a.Shape) {B : Nat} (hB : B ≤ a.used) (hv : T.Valid)
    (hm : T.mag = ((a.mag / radix ^ B + a.mag % radix ^ B) * (a.mag / radix ^ B + a.mag % radix ^ B) -
      (a.mag % radix ^ B * (a.mag % radix ^ B) + a.mag / radix ^ B * (a.mag / radix ^ B))) * radix ^ B) :
    T.used ≤ a.used + 1 + B := by
  refine used_le_of_lt hv ?_
  have hpos : 0 < radix ^ B := Nat.pow_pos radix_pos
  -- the unshifted value is below radix^(u+1): reuse `t1_used`'s bound on a valid stand-in
  have h0 := lo_lt a.mag B
  have h1 := hi_lt ha.toShapeU hB
  generalize a.mag / radix ^ B = X1 at hm h1
  generalize a.mag % radix ^ B = X0 at hm h0
  have e : (X1 + X0) * (X1 + X0) - (X0 * X0 + X1 * X1) = 2 * (X0 * X1) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm X1 X0]; omega
  rw [hm, e, Nat.pow_add]
  have h01 : X0 * X1 < radix ^ a.used := by
    rw [show a.used = B + (a.used - B) by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le h0 (Nat.le_of_lt h1) (by have := Nat.pow_pos (n := a.used - B) radix_pos; omega)
  have h2 : 2 * (X0 * X1) < radix ^ (a.used + 1) := by
    rw [Nat.pow_succ]
    have : 2 ≤ radix := by decide
    calc 2 * (X0 * X1) < 2 * radix ^ a.used := by omega
      _ ≤ radix ^ a.used * radix := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ this
  exact Nat.mul_lt_mul_of_pos_right h2 hpos

/-- **The result**: `b = (x0x0 + t1 R) + x1x1 R² = |a|²`. -/
theorem fin_mag {A R : Nat} {V T W t1 b : MpInt} (hb : b.Valid) (hv : b.val = t1.val + W.val)
    (h1 : t1.val = V.val + T.val) (_hV : V.sign = Layout.mpZpos ∨ V.sign = Layout.mpNeg) (sV : V.sign = Layout.mpZpos)
    (sT : T.sign = Layout.mpZpos) (sW : W.sign = Layout.mpZpos) (mV : V.mag = A % R * (A % R))
    (mT : T.mag = ((A / R + A % R) * (A / R + A % R) - (A % R * (A % R) + A / R * (A / R))) * R)
    (mW : W.mag = A / R * (A / R) * (R * R)) : b.mag = A * A := by
  refine mag_of_val hb ?_
  rw [hv, h1, val_zpos sV, val_zpos sT, val_zpos sW, mV, mT, mW, ← ksqr_val A R]
  push_cast; rfl

/-! ## `mp_lshd` keeps the allocation and the sign -/

theorem lshd_alloc {a a' : MpInt} {k : Nat} (h : LshdPost a k a') : a'.alloc = a.alloc := by
  by_cases h0 : k = 0 ∨ a.used = 0
  · rw [h.noop h0]
  · exact (h.shift (by omega) (by omega)).alloc

theorem lshd_sign {a a' : MpInt} {k : Nat} (h : LshdPost a k a') : a'.sign = a.sign := by
  by_cases h0 : k = 0 ∨ a.used = 0
  · rw [h.noop h0]
  · exact (h.shift (by omega) (by omega)).sign

/-- A sum of two values below `radix^k`: at most `k + 1` digits. -/
theorem addv_used {a b c : MpInt} (hc : c.Valid) (ha : a.Valid) (hb : b.Valid) (sa : a.sign = Layout.mpZpos)
    (sb : b.sign = Layout.mpZpos) (h : c.val = a.val + b.val) {k : Nat} (hka : a.used ≤ k) (hkb : b.used ≤ k) :
    c.used ≤ k + 1 := by
  have hm : c.mag = a.mag + b.mag := mag_of_val hc (by rw [h, val_zpos sa, val_zpos sb]; push_cast; rfl)
  refine used_le_of_lt hc ?_
  have h1 := Nat.lt_of_lt_of_le (mag_lt a ha.toShapeU) (Nat.pow_le_pow_right radix_pos hka)
  have h2 := Nat.lt_of_lt_of_le (mag_lt b hb.toShapeU) (Nat.pow_le_pow_right radix_pos hkb)
  rw [hm, Nat.pow_succ]
  have : 2 ≤ radix := by decide
  calc a.mag + b.mag < 2 * radix ^ k := by omega
    _ ≤ radix ^ k * radix := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ this

/-- `x1x1 R²`: at most `2k + 2B` digits. -/
theorem shl_used {W : MpInt} (hv : W.Valid) {X k B : Nat} (hm : W.mag = X * X * (radix ^ B * radix ^ B))
    (hx : X < radix ^ k) : W.used ≤ 2 * k + 2 * B := by
  refine used_le_of_lt hv ?_
  rw [hm, Nat.pow_add, ← pow_two_B]
  exact Nat.mul_lt_mul_of_pos_right (sq_lt hx) (Nat.pow_pos radix_pos)

end Tom.KSqr
