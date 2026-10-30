import Tom.Spec.KSqrStep
import Tom.Spec.Ledger
import Tom.Spec.Shift

/-!
# `s_mp_toom_sqr`'s model steps

Over the Ledger (`Tom/Spec/Ledger.lean`): every temporary after its copy and clamp, and after
every call, is an account `Acct t 1 U V True` (valid, a live digit array, `used ≤ U`, value `V`),
moved by one transfer lemma per C statement (`st_*`), each from the callee's post as the frozen
machine contracts give it (`valid`, `val`).

* The thirds (`B = a->used / 3`, `R = radix^B`): `a0 = |a| mod R`, `a1 = (|a| / R) mod R`,
  `a2 = |a| / R²` (`p0`, `p1`, `p2`), copied by three loops (`KSqr.lowF`, `KSqr.highF`) and
  clamped (`acct0`, `acct1`, `acct2`, by `Ledger.settle`).
* The point values and Chung–Hasan's SQR_3 interpolation as the C writes it: `S0 = a0²`,
  `S1 = (a0 + a2 + a1)²`, `S2 = (a0 + a2 − a1)²` (signed), `S3 = 2 a1 a2`, `S4 = a2²`,
  `tmp = (S1 + S2) / 2 = (a0 + a2)² + a1²` (exact), `S1 − tmp − S3 = 2 a0 a1`,
  `tmp − S4 − S0 = 2 a0 a2 + a1²`.
* The recomposition `S4 R⁴ + S3 R³ + S2' R² + S1' R + S0 = |a|²` (`fin`).
* The bounds each callee's residue needs (`used` against the measure, the stack, `int` sizes).
-/

namespace Tom.TSqr

open MpInt Ledger

/-! ## The thirds -/

/-- `a1` after the copy and `a1.used := B` (before `mp_clamp`). -/
def x1m (a : MpInt) (B n : Nat) : MpInt := MpInt.ofDigits B n Layout.mpZpos (KSqr.highF a B B)

def p0 (A B : Nat) : Nat := A % radix ^ B
def p1 (A B : Nat) : Nat := A / radix ^ B % radix ^ B
def p2 (A B : Nat) : Nat := A / radix ^ B / radix ^ B

theorem rad_pos (B : Nat) : 0 < radix ^ B := Nat.pow_pos radix_pos

theorem p0_lt (A B : Nat) : p0 A B < radix ^ B := Nat.mod_lt _ (rad_pos B)
theorem p1_lt (A B : Nat) : p1 A B < radix ^ B := Nat.mod_lt _ (rad_pos B)

theorem split3 (A B : Nat) : A = p2 A B * radix ^ B * radix ^ B + p1 A B * radix ^ B + p0 A B := by
  unfold p0 p1 p2
  have h1 := Nat.div_add_mod A (radix ^ B)
  have h2 := Nat.div_add_mod (A / radix ^ B) (radix ^ B)
  have e : A / radix ^ B / radix ^ B * radix ^ B * radix ^ B = radix ^ B * (radix ^ B * (A / radix ^ B / radix ^ B)) := by
    rw [Nat.mul_comm (A / radix ^ B / radix ^ B * radix ^ B), Nat.mul_comm (A / radix ^ B / radix ^ B)]
  have e2 : A / radix ^ B % radix ^ B * radix ^ B = radix ^ B * (A / radix ^ B % radix ^ B) := Nat.mul_comm _ _
  rw [e, e2]
  calc A = radix ^ B * (A / radix ^ B) + A % radix ^ B := h1.symm
    _ = radix ^ B * (radix ^ B * (A / radix ^ B / radix ^ B) + A / radix ^ B % radix ^ B) + A % radix ^ B := by rw [h2]
    _ = _ := by rw [Nat.mul_add]

/-- The top third: `|a| / R² < radix^(u − 2B)`. -/
theorem p2_lt {a : MpInt} (ha : a.ShapeU) {B : Nat} (hB : 2 * B ≤ a.used) : p2 a.mag B < radix ^ (a.used - 2 * B) := by
  unfold p2
  rw [Nat.div_div_eq_div_mul, ← KSqr.pow_two_B]
  exact KSqr.hi_lt ha hB

/-- The top third is at least `radix^(u − 2B − 1)` (`a`'s top digit is nonzero). -/
theorem p2_ge {a : MpInt} (ha : a.ValidU) {B : Nat} (hB : 2 * B < a.used) :
    radix ^ (a.used - 2 * B - 1) ≤ p2 a.mag B := by
  unfold p2
  rw [Nat.div_div_eq_div_mul, ← KSqr.pow_two_B]
  have hm := ha.mag_ge (by omega)
  refine (Nat.le_div_iff_mul_le (rad_pos _)).2 ?_
  rw [← Nat.pow_add, show a.used - 2 * B - 1 + 2 * B = a.used - 1 by omega]
  exact hm

/-! ## The copies and the clamps -/

theorem x1m_shape {a : MpInt} (ha : a.ShapeU) {B n : Nat} (hB : B ≤ n) (hn : n < 2 ^ 31) :
    (x1m a B n).Shape where
  len := MpInt.ofDigits_len _ _ _ _
  used_le := hB
  alloc_lt := hn
  digit_lt i := by
    rw [x1m, MpInt.ofDigits_digit]; unfold KSqr.highF
    split
    · split
      · exact ha.digit_lt _
      · exact radix_pos
    · exact radix_pos
  high_zero i hi := by
    rw [x1m, MpInt.ofDigits_digit]; unfold KSqr.highF
    simp only [x1m, MpInt.ofDigits] at hi
    split
    · rw [if_neg (by omega)]
    · rfl

theorem natUpTo_highF (a : MpInt) (B k : Nat) : natUpTo (KSqr.highF a B k) k = natUpTo (fun i => a.digit (B + i)) k :=
  natUpTo_congr k fun i hi => by simp [KSqr.highF, hi]

/-- `|a| / R = |a1| + R |a2|` as digit windows. -/
theorem hi_split {a : MpInt} {B : Nat} (h2 : 2 * B ≤ a.used) :
    natUpTo (fun i => a.digit (B + i)) (a.used - B) =
      natUpTo (fun i => a.digit (B + i)) B + radix ^ B * natUpTo (fun i => a.digit (2 * B + i)) (a.used - 2 * B) := by
  have := natUpTo_split (fun i => a.digit (B + i)) B (a.used - 2 * B)
  rw [show B + (a.used - 2 * B) = a.used - B by omega] at this
  rw [this]
  congr 2
  exact natUpTo_congr _ fun i _ => by rw [show B + (B + i) = 2 * B + i by omega]

theorem mag_div {a : MpInt} (ha : a.ShapeU) {B : Nat} (hB : B ≤ a.used) :
    a.mag / radix ^ B = natUpTo (fun i => a.digit (B + i)) (a.used - B) := by
  rw [KSqr.mag_split hB, Nat.add_mul_div_left _ _ (rad_pos B),
    Nat.div_eq_of_lt (natUpTo_lt _ ha.digit_lt B), Nat.zero_add]

theorem p1_eq {a : MpInt} (ha : a.ShapeU) {B : Nat} (h2 : 2 * B ≤ a.used) :
    p1 a.mag B = natUpTo (fun i => a.digit (B + i)) B := by
  unfold p1
  rw [mag_div ha (by omega), hi_split h2, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (natUpTo_lt _ (fun i => ha.digit_lt _) B)]

/-- `a0` after `mp_clamp`: an account of `|a| mod R`. -/
theorem acct0 {a : MpInt} (ha : a.ValidU) {B n : Nat} {t : MpInt} (hBu : B ≤ a.used) (hBn : B ≤ n)
    (hn : n < 2 ^ 31) (hn0 : 0 < n) (hc : ClampPost (KSqr.x0r a B n) t) :
    Acct t 1 B (p0 a.mag B : Int) True := by
  obtain ⟨hv, hm⟩ := KSqr.x0c_spec ha.toShapeU hBu hBn hn
  rw [← KSqr.x0c_eq hc] at hv hm
  have := ClampPost.spec (KSqr.x0r_shape ha.toShapeU hBn hn) (.inl rfl) hc
  exact ⟨hv, by rw [hc.alloc]; exact hn0, Nat.le_trans (by rw [hc.used]; exact clampUsed_le _ _) (Nat.le_refl B),
    by rw [Ledger.val_zpos (by rw [hc.sign]; split <;> rfl), hm]; rfl, trivial⟩

/-- `a1` after `mp_clamp`: an account of `(|a| / R) mod R`. -/
theorem acct1 {a : MpInt} (ha : a.ValidU) {B n : Nat} {t : MpInt} (h2 : 2 * B ≤ a.used) (hBn : B ≤ n)
    (hn : n < 2 ^ 31) (hn0 : 0 < n) (hc : ClampPost (x1m a B n) t) :
    Acct t 1 B (p1 a.mag B : Int) True := by
  have hs := Ledger.settle (T := p1 a.mag B) hBn hn (.inl rfl)
    (fun j _ => by unfold KSqr.highF; split <;> first | exact ha.digit_lt _ | exact radix_pos)
    (fun j hj _ => by unfold KSqr.highF; rw [if_neg (by omega)])
    (by rw [natUpTo_highF, p1_eq ha.toShapeU h2]) hc
  exact ⟨hs.valid, by rw [hs.alloc]; exact hn0, by rw [hc.used]; exact clampUsed_le _ _,
    hs.val, trivial⟩

/-- `a2` (`KSqr.x1r a (2B)`, valid: `a`'s top digit) after `mp_clamp`: an account of `|a| / R²`. -/
theorem acct2 {a : MpInt} (ha : a.ValidU) {B n : Nat} {t : MpInt} (h2 : 2 * B < a.used) (hn : a.used - 2 * B ≤ n)
    (hn' : n < 2 ^ 31) (hc : ClampPost (KSqr.x1r a (2 * B) n) t) :
    Acct t 1 (a.used - 2 * B) (p2 a.mag B : Int) True ∧ a.used - 2 * B ≤ t.used := by
  have hv := KSqr.x1r_valid ha h2 hn hn'
  obtain ⟨hv', hm⟩ := ClampPost.spec hv.toShape (.inl rfl) hc
  have hm2 : t.mag = p2 a.mag B := by
    rw [hm, KSqr.x1r_mag ha.toShapeU (by omega) hn]; unfold p2; rw [Nat.div_div_eq_div_mul, ← KSqr.pow_two_B]
  have hs : t.sign = Layout.mpZpos := by rw [hc.sign]; split <;> rfl
  have hU := KSqr.used_le_of_lt hv' (hm2 ▸ p2_lt ha.toShapeU (by omega))
  refine ⟨⟨hv', by rw [hc.alloc]; show 0 < n; omega, hU, by rw [Ledger.val_zpos hs, hm2], trivial⟩, ?_⟩
  have hge := p2_ge ha h2
  have hlt := MpInt.mag_lt hv'.toShape
  rw [hm2] at hlt
  have : radix ^ (a.used - 2 * B - 1) < radix ^ t.used := Nat.lt_of_le_of_lt hge hlt
  have := (Nat.pow_lt_pow_iff_right (show 1 < radix by decide)).1 this
  omega

/-! ## Accounts from a callee's value -/

theorem acct_of {x : MpInt} {V : Int} {U : Nat} (hv : x.Valid) (hp : 0 < x.alloc) (hval : x.val = V)
    (hU : V.natAbs < radix ^ U) : Acct x 1 U V True :=
  ⟨hv, hp, Ledger.used_le_of_lt hv (by rw [← natAbs_val, hval]; exact hU), hval, trivial⟩

theorem two_le_rad : 2 ≤ radix := by decide
theorem four_le_rad : 4 ≤ radix := by decide

theorem pow_mono {i j : Nat} (h : i ≤ j) : radix ^ i ≤ radix ^ j := Nat.pow_le_pow_right radix_pos h

theorem lt_succ_of_lt4 {x k : Nat} (h : x < 4 * radix ^ k) : x < radix ^ (k + 1) := by
  rw [Nat.pow_succ]; have := four_le_rad
  exact Nat.lt_of_lt_of_le h (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ this)

theorem mul_lt_pow {x y i j : Nat} (hx : x < radix ^ i) (hy : y < radix ^ j) : x * y < radix ^ (i + j) := by
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (Nat.lt_of_le_of_lt (Nat.zero_le _) hy)

/-! ## The bounds (`P = radix^K`, `K = u − 2B`, `B ≤ K`) -/

section bounds
variable {A B K : Nat} (hBK : B ≤ K) (h2 : p2 A B < radix ^ K)

include hBK in
theorem p0K : p0 A B < radix ^ K := Nat.lt_of_lt_of_le (p0_lt A B) (pow_mono hBK)
include hBK in
theorem p1K : p1 A B < radix ^ K := Nat.lt_of_lt_of_le (p1_lt A B) (pow_mono hBK)
include hBK h2

theorem b_u2 : ((p0 A B + p2 A B : Nat) : Int).natAbs < radix ^ (K + 1) := by
  have := p0K (A := A) hBK; simp only [Int.natAbs_natCast]; exact lt_succ_of_lt4 (by omega)

theorem b_b3 : ((p0 A B : Int) + p2 A B - p1 A B).natAbs < radix ^ (K + 1) := by
  have := p0K (A := A) hBK; have := p1K (A := A) hBK; exact lt_succ_of_lt4 (by omega)

theorem b_u4 : ((p0 A B + p2 A B + p1 A B : Nat) : Int).natAbs < radix ^ (K + 1) := by
  have := p0K (A := A) hBK; have := p1K (A := A) hBK; simp only [Int.natAbs_natCast]; exact lt_succ_of_lt4 (by omega)

end bounds

/-! ## The values, step by step (`x_i = p_i` as integers) -/

section vals
variable (A B : Nat)

def vZ : Int := (p0 A B : Int) * p0 A B
def vU2 : Int := (p0 A B : Int) + p2 A B
def vB3 : Int := (p0 A B : Int) + p2 A B - p1 A B
def vU4 : Int := (p0 A B : Int) + p2 A B + p1 A B
def vU5 : Int := vU4 A B * vU4 A B
def vB6 : Int := vB3 A B * vB3 A B
def vV7 : Int := (p1 A B : Int) * p2 A B
def vV8 : Int := 2 * ((p1 A B : Int) * p2 A B)
def vW9 : Int := (p2 A B : Int) * p2 A B
def vB10 : Int := vU5 A B + vB6 A B
def vB11 : Int := ((p0 A B : Int) + p2 A B) * ((p0 A B : Int) + p2 A B) + (p1 A B : Int) * p1 A B
def vU12 : Int := 2 * (((p0 A B : Int) + p2 A B) * p1 A B)
def vU13 : Int := 2 * ((p0 A B : Int) * p1 A B)
def vB14 : Int := (p0 A B : Int) * p0 A B + 2 * ((p0 A B : Int) * p2 A B) + (p1 A B : Int) * p1 A B
def vB15 : Int := 2 * ((p0 A B : Int) * p2 A B) + (p1 A B : Int) * p1 A B
def vW16 : Int := vW9 A B * ((radix ^ (4 * B) : Nat) : Int)
def vV17 : Int := vV8 A B * ((radix ^ (3 * B) : Nat) : Int)
def vB18 : Int := vB15 A B * ((radix ^ (2 * B) : Nat) : Int)
def vU19 : Int := vU13 A B * ((radix ^ B : Nat) : Int)
def vW20 : Int := vW16 A B + vV17 A B
def vB21 : Int := vW20 A B + vB18 A B
def vB22 : Int := vB21 A B + vU19 A B
def vB23 : Int := vB22 A B + vZ A B

/-- `(S1 + S2) / 2` is exact. -/
theorem e_b11 : (vB10 A B).tdiv 2 = vB11 A B := by
  have : vB10 A B = 2 * vB11 A B := by unfold vB10 vU5 vB6 vU4 vB3 vB11; grind
  rw [this, Int.mul_tdiv_cancel_left _ (by decide)]

theorem e_u12 : vU5 A B - vB11 A B = vU12 A B := by unfold vU5 vU4 vB11 vU12; grind
theorem e_u13 : vU12 A B - vV8 A B = vU13 A B := by unfold vU12 vV8 vU13; grind
theorem e_b14 : vB11 A B - vW9 A B = vB14 A B := by unfold vB11 vW9 vB14; grind
theorem e_b15 : vB14 A B - vZ A B = vB15 A B := by unfold vB14 vZ vB15; grind

theorem pow_cast (k : Nat) : ((radix ^ k : Nat) : Int) = (radix : Int) ^ k := by push_cast; rfl

/-- **The recomposition**: `S4 R⁴ + S3 R³ + (2 a0 a2 + a1²) R² + 2 a0 a1 R + a0² = |a|²`. -/
theorem e_fin : vB23 A B = ((A * A : Nat) : Int) := by
  have hA := split3 A B
  have e4 : radix ^ (4 * B) = radix ^ B * radix ^ B * radix ^ B * radix ^ B := by
    rw [show 4 * B = B + B + B + B by omega, Nat.pow_add, Nat.pow_add, Nat.pow_add]
  have e3 : radix ^ (3 * B) = radix ^ B * radix ^ B * radix ^ B := by
    rw [show 3 * B = B + B + B by omega, Nat.pow_add, Nat.pow_add]
  have e2 : radix ^ (2 * B) = radix ^ B * radix ^ B := by rw [Nat.two_mul, Nat.pow_add]
  unfold vB23 vB22 vB21 vW20 vW16 vV17 vB18 vU19 vZ vW9 vV8 vB15 vU13
  rw [e4, e3, e2]
  conv => rhs; rw [hA]
  generalize radix ^ B = R
  generalize p0 A B = x0; generalize p1 A B = x1; generalize p2 A B = x2
  push_cast
  grind

theorem cast_u13 : vU13 A B = ((2 * (p0 A B * p1 A B) : Nat) : Int) := by unfold vU13; push_cast; rfl
theorem cast_z : vZ A B = ((p0 A B * p0 A B : Nat) : Int) := by unfold vZ; push_cast; rfl
theorem cast_b15 : vB15 A B = ((2 * (p0 A B * p2 A B) + p1 A B * p1 A B : Nat) : Int) := by unfold vB15; push_cast; rfl
theorem cast_b11 : vB11 A B = (((p0 A B + p2 A B) * (p0 A B + p2 A B) + p1 A B * p1 A B : Nat) : Int) := by
  unfold vB11; push_cast; rfl
theorem cast_u12 : vU12 A B = ((2 * ((p0 A B + p2 A B) * p1 A B) : Nat) : Int) := by unfold vU12; push_cast; rfl
theorem cast_b14 : vB14 A B = ((p0 A B * p0 A B + 2 * (p0 A B * p2 A B) + p1 A B * p1 A B : Nat) : Int) := by
  unfold vB14; push_cast; rfl
theorem cast_b10 : vB10 A B = ((2 * ((p0 A B + p2 A B) * (p0 A B + p2 A B) + p1 A B * p1 A B) : Nat) : Int) := by
  have : vB10 A B = 2 * vB11 A B := by unfold vB10 vU5 vB6 vU4 vB3 vB11; grind
  rw [this, cast_b11]; push_cast; rfl

end vals

/-! ## Transfers -/

/-- A callee's value `V`, equal to the model `V'`, bounded: an account. -/
theorem step {x : MpInt} {V V' : Int} {U : Nat} (hx : x.Valid) (hp : 0 < x.alloc) (hv : x.val = V) (he : V = V')
    (hU : V'.natAbs < radix ^ U) : Acct x 1 U V' True := acct_of hx hp (hv.trans he) hU

/-- `mp_lshd` (growing) of an account: the value times `radix^k`. -/
theorem lshd_val {x x' : MpInt} {k : Nat} (hx : x.Valid) (hm : x'.mag = x.mag * radix ^ k) (hs : x'.sign = x.sign) :
    x'.val = x.val * ((radix ^ k : Nat) : Int) := by
  rw [MpInt.val_eq (a := x'), MpInt.val_eq (a := x), hm, hs]
  split <;> push_cast <;> grind

section bounds2
variable {A B K : Nat} (hBK : B ≤ K) (h2 : p2 A B < radix ^ K)
include hBK h2

theorem b_u5 : (vU5 A B).natAbs < radix ^ (2 * K + 2) := by
  unfold vU5; rw [Int.natAbs_mul, show 2 * K + 2 = (K + 1) + (K + 1) by omega]
  exact mul_lt_pow (b_u4 hBK h2) (b_u4 hBK h2)

theorem b_b6 : (vB6 A B).natAbs < radix ^ (2 * K + 2) := by
  unfold vB6; rw [Int.natAbs_mul, show 2 * K + 2 = (K + 1) + (K + 1) by omega]
  exact mul_lt_pow (b_b3 hBK h2) (b_b3 hBK h2)

theorem b_v7 : (vV7 A B).natAbs < radix ^ (B + K) := by
  unfold vV7; rw [Int.natAbs_mul]; simp only [Int.natAbs_natCast]
  exact mul_lt_pow (p1_lt A B) h2

theorem b_v8 : (vV8 A B).natAbs < radix ^ (B + K + 1) := by
  have h := b_v7 hBK h2
  unfold vV8; unfold vV7 at h; rw [Int.natAbs_mul]
  exact lt_succ_of_lt4 (by have : Int.natAbs 2 = 2 := rfl; rw [this]; omega)

theorem b_w9 : (vW9 A B).natAbs < radix ^ (2 * K) := by
  unfold vW9; rw [Int.natAbs_mul]; simp only [Int.natAbs_natCast]; rw [Nat.two_mul]
  exact mul_lt_pow h2 h2

theorem b_u13 : (vU13 A B).natAbs < radix ^ (2 * B + 1) := by
  rw [cast_u13, Int.natAbs_natCast]
  have := mul_lt_pow (p0_lt A B) (p1_lt A B)
  rw [← Nat.two_mul] at this
  exact lt_succ_of_lt4 (by omega)

theorem b_z : (vZ A B).natAbs < radix ^ (2 * B) := by
  rw [cast_z, Int.natAbs_natCast, Nat.two_mul]; exact mul_lt_pow (p0_lt A B) (p0_lt A B)

theorem b_b15 : (vB15 A B).natAbs < radix ^ (B + K + 1) := by
  rw [cast_b15, Int.natAbs_natCast]
  have h02 := mul_lt_pow (p0_lt A B) h2
  have h11 := Nat.lt_of_lt_of_le (mul_lt_pow (p1_lt A B) (p1_lt A B)) (pow_mono (show B + B ≤ B + K by omega))
  exact lt_succ_of_lt4 (by omega)

theorem b_b11 : (vB11 A B).natAbs < radix ^ (2 * K + 3) := by
  rw [cast_b11, Int.natAbs_natCast]
  have h02 : p0 A B + p2 A B < radix ^ (K + 1) := lt_succ_of_lt4 (by have := p0K (A := A) hBK; omega)
  have hs := mul_lt_pow h02 h02
  have h11 := Nat.lt_of_lt_of_le (mul_lt_pow (p1_lt A B) (p1_lt A B)) (pow_mono (show B + B ≤ K + 1 + (K + 1) by omega))
  have := lt_succ_of_lt4 (k := K + 1 + (K + 1)) (x := (p0 A B + p2 A B) * (p0 A B + p2 A B) + p1 A B * p1 A B) (by omega)
  exact Nat.lt_of_lt_of_le this (pow_mono (by omega))

theorem b_b10 : (vB10 A B).natAbs < radix ^ (2 * K + 3) := by
  rw [cast_b10, Int.natAbs_natCast]
  have h02 : p0 A B + p2 A B < radix ^ (K + 1) := lt_succ_of_lt4 (by have := p0K (A := A) hBK; omega)
  have hs := mul_lt_pow h02 h02
  have h11 := Nat.lt_of_lt_of_le (mul_lt_pow (p1_lt A B) (p1_lt A B)) (pow_mono (show B + B ≤ K + 1 + (K + 1) by omega))
  have := lt_succ_of_lt4 (k := K + 1 + (K + 1)) (x := 2 * ((p0 A B + p2 A B) * (p0 A B + p2 A B) + p1 A B * p1 A B)) (by
    have := Nat.pow_le_pow_right radix_pos (show K + 1 + (K + 1) ≤ K + 1 + (K + 1) by omega)
    omega)
  exact Nat.lt_of_lt_of_le this (pow_mono (by omega))

theorem b_u12 : (vU12 A B).natAbs < radix ^ (2 * K + 3) := by
  rw [cast_u12, Int.natAbs_natCast]
  have h02 : p0 A B + p2 A B < radix ^ (K + 1) := lt_succ_of_lt4 (by have := p0K (A := A) hBK; omega)
  have hm := Nat.lt_of_lt_of_le (mul_lt_pow h02 (p1_lt A B)) (pow_mono (show K + 1 + B ≤ 2 * K + 2 by omega))
  have := lt_succ_of_lt4 (k := 2 * K + 2) (x := 2 * ((p0 A B + p2 A B) * p1 A B)) (by omega)
  exact this

theorem b_b14 : (vB14 A B).natAbs < radix ^ (2 * K + 3) := by
  rw [cast_b14, Int.natAbs_natCast]
  have h00 := Nat.lt_of_lt_of_le (mul_lt_pow (p0_lt A B) (p0_lt A B)) (pow_mono (show B + B ≤ 2 * K + 2 by omega))
  have h02 := Nat.lt_of_lt_of_le (mul_lt_pow (p0_lt A B) h2) (pow_mono (show B + K ≤ 2 * K + 2 by omega))
  have h11 := Nat.lt_of_lt_of_le (mul_lt_pow (p1_lt A B) (p1_lt A B)) (pow_mono (show B + B ≤ 2 * K + 2 by omega))
  exact lt_succ_of_lt4 (by omega)

end bounds2

/-! ## The recomposition's partial sums (all below `|a|²`) -/

section sums
variable (A B : Nat)

def nW16 : Nat := p2 A B * p2 A B * radix ^ (4 * B)
def nV17 : Nat := 2 * (p1 A B * p2 A B) * radix ^ (3 * B)
def nB18 : Nat := (2 * (p0 A B * p2 A B) + p1 A B * p1 A B) * radix ^ (2 * B)
def nU19 : Nat := 2 * (p0 A B * p1 A B) * radix ^ B

theorem cast_w16 : vW16 A B = (nW16 A B : Int) := by unfold vW16 vW9 nW16; push_cast; rfl
theorem cast_v17 : vV17 A B = (nV17 A B : Int) := by unfold vV17 vV8 nV17; push_cast; rfl
theorem cast_b18 : vB18 A B = (nB18 A B : Int) := by unfold vB18 vB15 nB18; push_cast; rfl
theorem cast_u19 : vU19 A B = (nU19 A B : Int) := by unfold vU19 vU13 nU19; push_cast; rfl

theorem e_finN : nW16 A B + nV17 A B + nB18 A B + nU19 A B + p0 A B * p0 A B = A * A := by
  have h := e_fin A B
  unfold vB23 vB22 vB21 vW20 at h
  rw [cast_w16, cast_v17, cast_b18, cast_u19, cast_z] at h
  exact_mod_cast h

variable {A B : Nat} {u : Nat} (hA : A < radix ^ u)
include hA

theorem sq_lt_u : A * A < radix ^ (2 * u) := by rw [Nat.two_mul]; exact mul_lt_pow hA hA

theorem b_w20 : (vW20 A B).natAbs < radix ^ (2 * u) := by
  have := e_finN A B; have := sq_lt_u hA
  unfold vW20; rw [cast_w16, cast_v17, ← Int.natCast_add, Int.natAbs_natCast]; omega

theorem b_b21 : (vB21 A B).natAbs < radix ^ (2 * u) := by
  have := e_finN A B; have := sq_lt_u hA
  unfold vB21 vW20; rw [cast_w16, cast_v17, cast_b18, ← Int.natCast_add, ← Int.natCast_add, Int.natAbs_natCast]; omega

theorem b_b22 : (vB22 A B).natAbs < radix ^ (2 * u) := by
  have := e_finN A B; have := sq_lt_u hA
  unfold vB22 vB21 vW20
  rw [cast_w16, cast_v17, cast_b18, cast_u19, ← Int.natCast_add, ← Int.natCast_add, ← Int.natCast_add, Int.natAbs_natCast]
  omega

theorem b_b23 : (vB23 A B).natAbs < radix ^ (2 * u) := by
  rw [e_fin, Int.natAbs_natCast]; exact sq_lt_u hA

theorem b_w16 : (vW16 A B).natAbs < radix ^ (2 * u) := by
  have := e_finN A B; have := sq_lt_u hA
  rw [cast_w16, Int.natAbs_natCast]; omega

theorem b_v17 : (vV17 A B).natAbs < radix ^ (2 * u) := by
  have := e_finN A B; have := sq_lt_u hA
  rw [cast_v17, Int.natAbs_natCast]; omega

theorem b_b18 : (vB18 A B).natAbs < radix ^ (2 * u) := by
  have := e_finN A B; have := sq_lt_u hA
  rw [cast_b18, Int.natAbs_natCast]; omega

theorem b_u19 : (vU19 A B).natAbs < radix ^ (2 * u) := by
  have := e_finN A B; have := sq_lt_u hA
  rw [cast_u19, Int.natAbs_natCast]; omega

end sums

end Tom.TSqr
