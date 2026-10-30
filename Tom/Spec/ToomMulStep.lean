import Tom.Spec.ToomSqrStep
import Tom.Spec.MulAlgo

/-!
# `s_mp_toom_mul`'s model steps

Over the Ledger, as `Tom/Spec/ToomSqrStep.lean` does for squaring: every temporary after its copy
and clamp, and after every call, is an account `Acct t 1 U V True`. The point values the C builds (`toom3_at1`,
`toom3_at2`, `toom3_atm1` of Tom/Spec/MulAlgo.lean), Bodrato's interpolation as the C writes it
over the coefficients `q0 … q4` (`tp0 … tp4`), each exact division (`/3`, `/2`, `/2`) on a
multiple, and the recomposition `q4 R⁴ + q3 R³ + q2 R² + q1 R + q0 = |a| |b|` (`e_fin`).

Bounds: an `a`-side combination of the thirds is below `radix^(Ka + 1)` (`Ka = a->used − 2B`),
a `b`-side one below `radix^(Kb + 1)`, a point product below `radix^(Ka + Kb + 2)`, every
interpolation value (at most 256 coefficients' worth) below `radix^(Ka + Kb + 2)`, and the
recomposition's partial sums below `|a| |b| < radix^(a->used + b->used)`.
-/

namespace Tom.TMul

open MpInt Ledger
open TSqr (p0 p1 p2)

section vals
variable (A V B : Nat)

/-- The thirds as integers. -/
def X0 : Int := (p0 A B : Int)
def X1 : Int := (p1 A B : Int)
def X2 : Int := (p2 A B : Int)
def Y0 : Int := (p0 V B : Int)
def Y1 : Int := (p1 V B : Int)
def Y2 : Int := (p2 V B : Int)

/-- The product's coefficients, as naturals. -/
def n0 : Nat := p0 A B * p0 V B
def n1 : Nat := p0 A B * p1 V B + p1 A B * p0 V B
def n2 : Nat := p0 A B * p2 V B + p1 A B * p1 V B + p2 A B * p0 V B
def n3 : Nat := p1 A B * p2 V B + p2 A B * p1 V B
def n4 : Nat := p2 A B * p2 V B

def q0 : Int := (n0 A V B : Int)
def q1 : Int := (n1 A V B : Int)
def q2 : Int := (n2 A V B : Int)
def q3 : Int := (n3 A V B : Int)
def q4 : Int := (n4 A V B : Int)

/-! The values, call by call (`c<i>`: the `i`-th call of the main line). -/

def vT1a : Int := X2 A B + X1 A B
def vS2a : Int := vT1a A B + X0 A B
def vCa : Int := Y2 V B + Y1 V B
def vS1a : Int := vCa V B + Y0 V B
def w1 : Int := vS1a V B * vS2a A B
def vT1b : Int := vT1a A B + X2 A B
def vT1c : Int := 2 * vT1b A B
def vT1d : Int := vT1c A B + X0 A B
def vCb : Int := vCa V B + Y2 V B
def vCc : Int := 2 * vCb V B
def vCd : Int := vCc V B + Y0 V B
def w2 : Int := vT1d A B * vCd V B
def vA1a : Int := X2 A B - X1 A B
def vA1b : Int := vA1a A B + X0 A B
def vB1a : Int := Y2 V B - Y1 V B
def vB1b : Int := vB1a V B + Y0 V B
def wm : Int := vA1b A B * vB1b V B
def vB1c : Int := X2 A B * Y2 V B
def vS2c : Int := w2 A V B - wm A V B
def vS2d : Int := q1 A V B + q2 A V B + 3 * q3 A V B + 5 * q4 A V B
def vA1d : Int := w1 A V B - wm A V B
def vA1e : Int := q1 A V B + q3 A V B
def vA0b : Int := X0 A B * Y0 V B
def vS1c : Int := q1 A V B + q2 A V B + q3 A V B + q4 A V B
def vS2e : Int := 2 * (q3 A V B + 2 * q4 A V B)
def vS2f : Int := q3 A V B + 2 * q4 A V B
def vS1d : Int := q2 A V B + q4 A V B
def vT1e : Int := 2 * vB1c A V B
def vB1d : Int := vB1c A V B * ((radix ^ (4 * B) : Nat) : Int)
def vS2h : Int := q3 A V B * ((radix ^ (3 * B) : Nat) : Int)
def vB1e : Int := vB1d A V B + vS2h A V B
def vS1f : Int := q2 A V B * ((radix ^ (2 * B) : Nat) : Int)
def vB1f : Int := vB1e A V B + vS1f A V B
def vA1g : Int := q1 A V B * ((radix ^ B : Nat) : Int)
def vB1g : Int := vB1f A V B + vA1g A V B
def vC : Int := vB1g A V B + vA0b A V B

theorem e_q4 : vB1c A V B = q4 A V B := by unfold vB1c q4 n4 X2 Y2; push_cast; rfl
theorem e_q0 : vA0b A V B = q0 A V B := by unfold vA0b q0 n0 X0 Y0; push_cast; rfl

theorem e_w1 : w1 A V B = q0 A V B + q1 A V B + q2 A V B + q3 A V B + q4 A V B := by
  unfold w1 vS1a vCa vS2a vT1a q0 q1 q2 q3 q4 n0 n1 n2 n3 n4 X0 X1 X2 Y0 Y1 Y2; push_cast; grind

theorem e_w2 : w2 A V B = q0 A V B + 2 * q1 A V B + 4 * q2 A V B + 8 * q3 A V B + 16 * q4 A V B := by
  unfold w2 vT1d vT1c vT1b vT1a vCd vCc vCb vCa q0 q1 q2 q3 q4 n0 n1 n2 n3 n4 X0 X1 X2 Y0 Y1 Y2
  push_cast; grind

theorem e_wm : wm A V B = q0 A V B - q1 A V B + q2 A V B - q3 A V B + q4 A V B := by
  unfold wm vA1b vA1a vB1b vB1a q0 q1 q2 q3 q4 n0 n1 n2 n3 n4 X0 X1 X2 Y0 Y1 Y2; push_cast; grind

/-- `(S2 − a1) / 3` is exact. -/
theorem e_s2d : (vS2c A V B).tdiv 3 = vS2d A V B := by
  have : vS2c A V B = 3 * vS2d A V B := by unfold vS2c vS2d; rw [e_w2, e_wm]; omega
  rw [this, Int.mul_tdiv_cancel_left _ (by decide)]

/-- `(S1 − a1) / 2` is exact. -/
theorem e_a1e : (vA1d A V B).tdiv 2 = vA1e A V B := by
  have : vA1d A V B = 2 * vA1e A V B := by unfold vA1d vA1e; rw [e_w1, e_wm]; omega
  rw [this, Int.mul_tdiv_cancel_left _ (by decide)]

theorem e_s1c : w1 A V B - vA0b A V B = vS1c A V B := by unfold vS1c; rw [e_w1, e_q0]; omega
theorem e_s2e : vS2d A V B - vS1c A V B = vS2e A V B := by unfold vS2d vS1c vS2e; omega

theorem e_s2f : (vS2e A V B).tdiv 2 = vS2f A V B := by
  unfold vS2e vS2f; rw [Int.mul_tdiv_cancel_left _ (by decide)]

theorem e_s1d : vS1c A V B - vA1e A V B = vS1d A V B := by unfold vS1c vA1e vS1d; omega
theorem e_s1e : vS1d A V B - vB1c A V B = q2 A V B := by unfold vS1d; rw [e_q4]; omega
theorem e_s2g : vS2f A V B - vT1e A V B = q3 A V B := by unfold vS2f vT1e; rw [e_q4]; omega
theorem e_a1f : vA1e A V B - q3 A V B = q1 A V B := by unfold vA1e; omega

theorem pow_cast (k : Nat) : ((radix ^ k : Nat) : Int) = (radix : Int) ^ k := by push_cast; rfl

/-- **The recomposition**: `q4 R⁴ + q3 R³ + q2 R² + q1 R + q0 = |a| |b|`. -/
theorem e_fin : vC A V B = ((A * V : Nat) : Int) := by
  have hA := TSqr.split3 A B
  have hV := TSqr.split3 V B
  have e4 : radix ^ (4 * B) = radix ^ B * radix ^ B * radix ^ B * radix ^ B := by
    rw [show 4 * B = B + B + B + B by omega, Nat.pow_add, Nat.pow_add, Nat.pow_add]
  have e3 : radix ^ (3 * B) = radix ^ B * radix ^ B * radix ^ B := by
    rw [show 3 * B = B + B + B by omega, Nat.pow_add, Nat.pow_add]
  have e2 : radix ^ (2 * B) = radix ^ B * radix ^ B := by rw [Nat.two_mul, Nat.pow_add]
  unfold vC vB1g vB1f vB1e vB1d vS2h vS1f vA1g vA0b vB1c q1 q2 q3 n1 n2 n3 X0 X2 Y0 Y2
  rw [e4, e3, e2]
  conv => rhs; rw [hA, hV]
  generalize radix ^ B = R
  generalize p0 A B = x0; generalize p1 A B = x1; generalize p2 A B = x2
  generalize p0 V B = y0; generalize p1 V B = y1; generalize p2 V B = y2
  push_cast
  grind

end vals

/-! ## Bounds -/

theorem rad_ge : 256 ≤ radix := by decide

theorem lt_succ_of_lt256 {x k : Nat} (h : x < 256 * radix ^ k) : x < radix ^ (k + 1) := by
  rw [Nat.pow_succ]
  exact Nat.lt_of_lt_of_le h (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ rad_ge)

/-- An integer within `256 · radix^k` of zero is below `radix^(k+1)` in magnitude. -/
theorem bd {V : Int} {k : Nat} (h1 : -(256 * ((radix ^ k : Nat) : Int)) < V) (h2 : V < 256 * ((radix ^ k : Nat) : Int)) :
    V.natAbs < radix ^ (k + 1) :=
  lt_succ_of_lt256 (by omega)

section bounds
variable {A V B Ka Kb : Nat} (hBa : B ≤ Ka) (hBb : B ≤ Kb) (hA2 : p2 A B < radix ^ Ka) (hV2 : p2 V B < radix ^ Kb)

theorem pK {x B K : Nat} (hx : x < radix ^ B) (h : B ≤ K) : x < radix ^ K :=
  Nat.lt_of_lt_of_le hx (TSqr.pow_mono h)

include hBa hA2 in
theorem bx : p0 A B < radix ^ Ka ∧ p1 A B < radix ^ Ka ∧ p2 A B < radix ^ Ka :=
  ⟨pK (TSqr.p0_lt A B) hBa, pK (TSqr.p1_lt A B) hBa, hA2⟩

include hBb hV2 in
theorem bya : p0 V B < radix ^ Kb ∧ p1 V B < radix ^ Kb ∧ p2 V B < radix ^ Kb :=
  ⟨pK (TSqr.p0_lt V B) hBb, pK (TSqr.p1_lt V B) hBb, hV2⟩

/-- An `a`-side combination (coefficients summing to at most 256 in magnitude). -/
theorem bdA {W : Int} (hW : ∀ M : Int, (p0 A B : Int) < M → (p1 A B : Int) < M → (p2 A B : Int) < M →
    -(256 * M) < W ∧ W < 256 * M) (hb : p0 A B < radix ^ Ka ∧ p1 A B < radix ^ Ka ∧ p2 A B < radix ^ Ka) :
    W.natAbs < radix ^ (Ka + 1) := by
  obtain ⟨h1, h2⟩ := hW ((radix ^ Ka : Nat) : Int) (by exact_mod_cast hb.1) (by exact_mod_cast hb.2.1)
    (by exact_mod_cast hb.2.2)
  exact bd h1 h2

include hBa hA2 in
theorem b_t1a : (vT1a A B).natAbs < radix ^ (Ka + 1) :=
  bdA (fun M _ _ _ => by unfold vT1a X1 X2; omega) (bx hBa hA2)
include hBa hA2 in
theorem b_s2a : (vS2a A B).natAbs < radix ^ (Ka + 1) :=
  bdA (fun M _ _ _ => by unfold vS2a vT1a X0 X1 X2; omega) (bx hBa hA2)
include hBa hA2 in
theorem b_t1b : (vT1b A B).natAbs < radix ^ (Ka + 1) :=
  bdA (fun M _ _ _ => by unfold vT1b vT1a X1 X2; omega) (bx hBa hA2)
include hBa hA2 in
theorem b_t1c : (vT1c A B).natAbs < radix ^ (Ka + 1) :=
  bdA (fun M _ _ _ => by unfold vT1c vT1b vT1a X1 X2; omega) (bx hBa hA2)
include hBa hA2 in
theorem b_t1d : (vT1d A B).natAbs < radix ^ (Ka + 1) :=
  bdA (fun M _ _ _ => by unfold vT1d vT1c vT1b vT1a X0 X1 X2; omega) (bx hBa hA2)
include hBa hA2 in
theorem b_a1a : (vA1a A B).natAbs < radix ^ (Ka + 1) :=
  bdA (fun M _ _ _ => by unfold vA1a X1 X2; omega) (bx hBa hA2)
include hBa hA2 in
theorem b_a1b : (vA1b A B).natAbs < radix ^ (Ka + 1) :=
  bdA (fun M _ _ _ => by unfold vA1b vA1a X0 X1 X2; omega) (bx hBa hA2)

theorem bdB {W : Int} (hW : ∀ M : Int, (p0 V B : Int) < M → (p1 V B : Int) < M → (p2 V B : Int) < M →
    -(256 * M) < W ∧ W < 256 * M) (hb : p0 V B < radix ^ Kb ∧ p1 V B < radix ^ Kb ∧ p2 V B < radix ^ Kb) :
    W.natAbs < radix ^ (Kb + 1) := bdA (A := V) (Ka := Kb) hW hb

include hBb hV2 in
theorem b_ca : (vCa V B).natAbs < radix ^ (Kb + 1) :=
  bdB (fun M _ _ _ => by unfold vCa Y1 Y2; omega) (bya hBb hV2)
include hBb hV2 in
theorem b_s1a : (vS1a V B).natAbs < radix ^ (Kb + 1) :=
  bdB (fun M _ _ _ => by unfold vS1a vCa Y0 Y1 Y2; omega) (bya hBb hV2)
include hBb hV2 in
theorem b_cb : (vCb V B).natAbs < radix ^ (Kb + 1) :=
  bdB (fun M _ _ _ => by unfold vCb vCa Y1 Y2; omega) (bya hBb hV2)
include hBb hV2 in
theorem b_cc : (vCc V B).natAbs < radix ^ (Kb + 1) :=
  bdB (fun M _ _ _ => by unfold vCc vCb vCa Y1 Y2; omega) (bya hBb hV2)
include hBb hV2 in
theorem b_cd : (vCd V B).natAbs < radix ^ (Kb + 1) :=
  bdB (fun M _ _ _ => by unfold vCd vCc vCb vCa Y0 Y1 Y2; omega) (bya hBb hV2)
include hBb hV2 in
theorem b_b1a : (vB1a V B).natAbs < radix ^ (Kb + 1) :=
  bdB (fun M _ _ _ => by unfold vB1a Y1 Y2; omega) (bya hBb hV2)
include hBb hV2 in
theorem b_b1b : (vB1b V B).natAbs < radix ^ (Kb + 1) :=
  bdB (fun M _ _ _ => by unfold vB1b vB1a Y0 Y1 Y2; omega) (bya hBb hV2)

-- The point products.
include hBa hBb hA2 hV2 in
theorem b_w1 : (w1 A V B).natAbs < radix ^ (Ka + Kb + 2) := by
  unfold w1; rw [Int.natAbs_mul, show Ka + Kb + 2 = (Kb + 1) + (Ka + 1) by omega]
  exact TSqr.mul_lt_pow (b_s1a hBb hV2) (b_s2a hBa hA2)
include hBa hBb hA2 hV2 in
theorem b_w2 : (w2 A V B).natAbs < radix ^ (Ka + Kb + 2) := by
  unfold w2; rw [Int.natAbs_mul, show Ka + Kb + 2 = (Ka + 1) + (Kb + 1) by omega]
  exact TSqr.mul_lt_pow (b_t1d hBa hA2) (b_cd hBb hV2)
include hBa hBb hA2 hV2 in
theorem b_wm : (wm A V B).natAbs < radix ^ (Ka + Kb + 2) := by
  unfold wm; rw [Int.natAbs_mul, show Ka + Kb + 2 = (Ka + 1) + (Kb + 1) by omega]
  exact TSqr.mul_lt_pow (b_a1b hBa hA2) (b_b1b hBb hV2)
include hA2 hV2 in
theorem b_b1c : (vB1c A V B).natAbs < radix ^ (Ka + Kb) := by
  unfold vB1c X2 Y2; rw [Int.natAbs_mul]; simp only [Int.natAbs_natCast]; exact TSqr.mul_lt_pow hA2 hV2
include hBa hBb in
theorem b_a0b : (vA0b A V B).natAbs < radix ^ (Ka + Kb) := by
  unfold vA0b X0 Y0; rw [Int.natAbs_mul]; simp only [Int.natAbs_natCast]
  exact TSqr.mul_lt_pow (pK (TSqr.p0_lt A B) hBa) (pK (TSqr.p0_lt V B) hBb)

-- The coefficients, against `M = radix^(Ka + Kb)`.
include hBa hBb hA2 hV2 in
theorem bq : n0 A V B < radix ^ (Ka + Kb) ∧ n1 A V B < 2 * radix ^ (Ka + Kb) ∧ n2 A V B < 3 * radix ^ (Ka + Kb) ∧
    n3 A V B < 2 * radix ^ (Ka + Kb) ∧ n4 A V B < radix ^ (Ka + Kb) := by
  obtain ⟨a0, a1, a2⟩ := bx hBa hA2
  obtain ⟨b0, b1, b2⟩ := bya hBb hV2
  have m := fun {x y : Nat} (hx : x < radix ^ Ka) (hy : y < radix ^ Kb) => TSqr.mul_lt_pow hx hy
  have h00 := m a0 b0; have h01 := m a0 b1; have h10 := m a1 b0; have h02 := m a0 b2; have h11 := m a1 b1
  have h20 := m a2 b0; have h12 := m a1 b2; have h21 := m a2 b1; have h22 := m a2 b2
  unfold n0 n1 n2 n3 n4; omega

/-- An interpolation value: an integer combination of the coefficients. -/
theorem bdQ {W : Int} (hW : ∀ M : Int, 0 ≤ q0 A V B → q0 A V B < M → 0 ≤ q1 A V B → q1 A V B < 2 * M →
      0 ≤ q2 A V B → q2 A V B < 3 * M → 0 ≤ q3 A V B → q3 A V B < 2 * M → 0 ≤ q4 A V B → q4 A V B < M →
      -(256 * M) < W ∧ W < 256 * M)
    (hb : n0 A V B < radix ^ (Ka + Kb) ∧ n1 A V B < 2 * radix ^ (Ka + Kb) ∧ n2 A V B < 3 * radix ^ (Ka + Kb) ∧
      n3 A V B < 2 * radix ^ (Ka + Kb) ∧ n4 A V B < radix ^ (Ka + Kb)) :
    W.natAbs < radix ^ (Ka + Kb + 2) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hb
  obtain ⟨l, r⟩ := hW ((radix ^ (Ka + Kb) : Nat) : Int) (by unfold q0; omega) (by unfold q0; omega)
    (by unfold q1; omega) (by unfold q1; omega) (by unfold q2; omega) (by unfold q2; omega)
    (by unfold q3; omega) (by unfold q3; omega) (by unfold q4; omega) (by unfold q4; omega)
  exact Nat.lt_of_lt_of_le (bd l r) (TSqr.pow_mono (by omega))

include hBa hBb hA2 hV2 in
theorem b_s2c : (vS2c A V B).natAbs < radix ^ (Ka + Kb + 2) :=
  bdQ (fun M _ _ _ _ _ _ _ _ _ _ => by unfold vS2c; rw [e_w2, e_wm]; omega) (bq hBa hBb hA2 hV2)
include hBa hBb hA2 hV2 in
theorem b_s2d : (vS2d A V B).natAbs < radix ^ (Ka + Kb + 2) :=
  bdQ (fun M _ _ _ _ _ _ _ _ _ _ => by unfold vS2d; omega) (bq hBa hBb hA2 hV2)
include hBa hBb hA2 hV2 in
theorem b_a1d : (vA1d A V B).natAbs < radix ^ (Ka + Kb + 2) :=
  bdQ (fun M _ _ _ _ _ _ _ _ _ _ => by unfold vA1d; rw [e_w1, e_wm]; omega) (bq hBa hBb hA2 hV2)
include hBa hBb hA2 hV2 in
theorem b_a1e : (vA1e A V B).natAbs < radix ^ (Ka + Kb + 2) :=
  bdQ (fun M _ _ _ _ _ _ _ _ _ _ => by unfold vA1e; omega) (bq hBa hBb hA2 hV2)
include hBa hBb hA2 hV2 in
theorem b_s1c : (vS1c A V B).natAbs < radix ^ (Ka + Kb + 2) :=
  bdQ (fun M _ _ _ _ _ _ _ _ _ _ => by unfold vS1c; omega) (bq hBa hBb hA2 hV2)
include hBa hBb hA2 hV2 in
theorem b_s2e : (vS2e A V B).natAbs < radix ^ (Ka + Kb + 2) :=
  bdQ (fun M _ _ _ _ _ _ _ _ _ _ => by unfold vS2e; omega) (bq hBa hBb hA2 hV2)
include hBa hBb hA2 hV2 in
theorem b_s2f : (vS2f A V B).natAbs < radix ^ (Ka + Kb + 2) :=
  bdQ (fun M _ _ _ _ _ _ _ _ _ _ => by unfold vS2f; omega) (bq hBa hBb hA2 hV2)
include hBa hBb hA2 hV2 in
theorem b_s1d : (vS1d A V B).natAbs < radix ^ (Ka + Kb + 2) :=
  bdQ (fun M _ _ _ _ _ _ _ _ _ _ => by unfold vS1d; omega) (bq hBa hBb hA2 hV2)
include hBa hBb hA2 hV2 in
theorem b_t1e : (vT1e A V B).natAbs < radix ^ (Ka + Kb + 2) :=
  bdQ (fun M _ _ _ _ _ _ _ _ _ _ => by unfold vT1e; rw [e_q4]; omega) (bq hBa hBb hA2 hV2)
include hBa hBb hA2 hV2 in
theorem b_q1 : (q1 A V B).natAbs < radix ^ (Ka + Kb + 2) :=
  bdQ (fun M _ _ _ _ _ _ _ _ _ _ => by omega) (bq hBa hBb hA2 hV2)
include hBa hBb hA2 hV2 in
theorem b_q2 : (q2 A V B).natAbs < radix ^ (Ka + Kb + 2) :=
  bdQ (fun M _ _ _ _ _ _ _ _ _ _ => by omega) (bq hBa hBb hA2 hV2)
include hBa hBb hA2 hV2 in
theorem b_q3 : (q3 A V B).natAbs < radix ^ (Ka + Kb + 2) :=
  bdQ (fun M _ _ _ _ _ _ _ _ _ _ => by omega) (bq hBa hBb hA2 hV2)

end bounds

/-- `S2 − a1 = 3 (q1 + q2 + 3 q3 + 5 q4)` is nonzero: `q4 = x2 y2 > 0` (both top thirds are). -/
theorem s2c_ne {A V B : Nat} (hx : 0 < p2 A B) (hy : 0 < p2 V B) : vS2c A V B ≠ 0 := by
  have : vS2c A V B = 3 * vS2d A V B := by unfold vS2c vS2d; rw [e_w2, e_wm]; omega
  rw [this]; unfold vS2d q1 q2 q3 q4 n4
  have : 0 < p2 A B * p2 V B := Nat.mul_pos hx hy
  omega

/-! ## The recomposition's partial sums (all below `|a| |b|`) -/

section sums
variable (A V B : Nat)

def m4 : Nat := n4 A V B * radix ^ (4 * B)
def m3 : Nat := n3 A V B * radix ^ (3 * B)
def m2 : Nat := n2 A V B * radix ^ (2 * B)
def m1 : Nat := n1 A V B * radix ^ B

theorem cast_b1d : vB1d A V B = (m4 A V B : Int) := by unfold vB1d m4; rw [e_q4]; unfold q4; push_cast; rfl
theorem cast_s2h : vS2h A V B = (m3 A V B : Int) := by unfold vS2h m3 q3; push_cast; rfl
theorem cast_s1f : vS1f A V B = (m2 A V B : Int) := by unfold vS1f m2 q2; push_cast; rfl
theorem cast_a1g : vA1g A V B = (m1 A V B : Int) := by unfold vA1g m1 q1; push_cast; rfl
theorem cast_a0b : vA0b A V B = (n0 A V B : Int) := by rw [e_q0]; rfl

theorem e_finN : m4 A V B + m3 A V B + m2 A V B + m1 A V B + n0 A V B = A * V := by
  have h := e_fin A V B
  unfold vC vB1g vB1f vB1e at h
  rw [cast_b1d, cast_s2h, cast_s1f, cast_a1g, cast_a0b] at h
  exact_mod_cast h

variable {A V B : Nat} {ua ub : Nat} (hA : A < radix ^ ua) (hV : V < radix ^ ub)
include hA hV

theorem prod_lt : A * V < radix ^ (ua + ub) := TSqr.mul_lt_pow hA hV

theorem b_b1d : (vB1d A V B).natAbs < radix ^ (ua + ub) := by
  have := e_finN A V B; have := prod_lt hA hV; rw [cast_b1d, Int.natAbs_natCast]; omega
theorem b_s2h : (vS2h A V B).natAbs < radix ^ (ua + ub) := by
  have := e_finN A V B; have := prod_lt hA hV; rw [cast_s2h, Int.natAbs_natCast]; omega
theorem b_s1f : (vS1f A V B).natAbs < radix ^ (ua + ub) := by
  have := e_finN A V B; have := prod_lt hA hV; rw [cast_s1f, Int.natAbs_natCast]; omega
theorem b_a1g : (vA1g A V B).natAbs < radix ^ (ua + ub) := by
  have := e_finN A V B; have := prod_lt hA hV; rw [cast_a1g, Int.natAbs_natCast]; omega
theorem b_b1e : (vB1e A V B).natAbs < radix ^ (ua + ub) := by
  have := e_finN A V B; have := prod_lt hA hV
  unfold vB1e; rw [cast_b1d, cast_s2h, ← Int.natCast_add, Int.natAbs_natCast]; omega
theorem b_b1f : (vB1f A V B).natAbs < radix ^ (ua + ub) := by
  have := e_finN A V B; have := prod_lt hA hV
  unfold vB1f vB1e; rw [cast_b1d, cast_s2h, cast_s1f, ← Int.natCast_add, ← Int.natCast_add, Int.natAbs_natCast]; omega
theorem b_b1g : (vB1g A V B).natAbs < radix ^ (ua + ub) := by
  have := e_finN A V B; have := prod_lt hA hV
  unfold vB1g vB1f vB1e
  rw [cast_b1d, cast_s2h, cast_s1f, cast_a1g, ← Int.natCast_add, ← Int.natCast_add, ← Int.natCast_add, Int.natAbs_natCast]
  omega
theorem b_c : (vC A V B).natAbs < radix ^ (ua + ub) := by
  rw [e_fin, Int.natAbs_natCast]; exact prod_lt hA hV

end sums

end Tom.TMul
