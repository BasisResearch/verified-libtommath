import Tom.Spec.KSqrStep
import Tom.Spec.KMulStep
import Tom.Spec.GrowHStep

/-!
# `s_mp_karatsuba_mul`'s model steps on the growing callees

The halves are karatsuba squaring's (`Tom/Spec/KSqrStep.lean`: `KSqr.x0c`, `KSqr.x1r`, the copy
loops `lowF`/`highF`), taken of `a` and of `b`. Every temporary is nonnegative, so each callee's
post reads as a magnitude with the sign `MP_ZPOS`:

* `mp_mul` (`MulPost`): `mul_post`;
* the growing `s_mp_add` / `mp_add` (same signs: `s_mp_add`'s branch) over the grown destination
  (`sAddIn`): `sadd_post`;
* the growing `s_mp_sub(a, b, a)` (`sSubIn`): `ssub_post`;
* the bounds on `used` along the way (`used_mul`, `used_add`) for the callees' `int` sizes and the
  recursion's measure;
* the recomposition `fin_mag` (`kara_recompose`).
-/

namespace Tom.KMul

open MpInt

/-! ## Signs and magnitudes -/

/-- A valid `mp_int` of nonnegative value `n` is `MP_ZPOS`. -/
theorem sign_of_val {c : MpInt} (hc : c.Valid) {n : Nat} (h : c.val = (n : Int)) : c.sign = Layout.mpZpos := by
  rcases hc.sign_ok with hs | hs
  · exact hs
  · by_cases hu : c.used = 0
    · exact hc.zero_pos hu
    · have hm := MpInt.mag_ge hc (by omega)
      unfold MpInt.val at h
      rw [if_pos hs] at h
      have : 0 < radix ^ (c.used - 1) := Nat.pow_pos radix_pos
      omega

/-- A nonnegative temporary as a callee leaves it: valid, its magnitude, `MP_ZPOS`. -/
structure TRes (t : MpInt) (n : Nat) : Prop where
  valid : t.Valid
  mag : t.mag = n
  sign : t.sign = Layout.mpZpos

/-- A grown temporary: its old `alloc` kept as a lower bound, its `used` bounded. -/
structure TResG (t : MpInt) (n al u : Nat) : Prop extends TRes t n where
  grow : al ≤ t.alloc
  used : t.used ≤ u

/-- `mp_mul` on nonnegative operands. -/
theorem mul_post {x y z : MpInt} (h : MulPost x y z) (sx : x.sign = Layout.mpZpos) (sy : y.sign = Layout.mpZpos) :
    TRes z (x.mag * y.mag) := by
  have hv : z.val = ((x.mag * y.mag : Nat) : Int) := by
    rw [h.val, KSqr.val_zpos sx, KSqr.val_zpos sy]; push_cast; rfl
  exact ⟨h.valid, KSqr.mag_of_val h.valid hv, sign_of_val h.valid hv⟩

/-- The growing `s_mp_add(x, y, c)` (`c` nonnegative): `|x| + |y|`, grown only. -/
theorem sadd_post {x y c t : MpInt} (hx : x.Shape) (hy : y.Shape) (hc : c.Shape) (sc : c.sign = Layout.mpZpos)
    (h31 : max x.used y.used + 1 < 2 ^ 31) (h : SAddPost x y (sAddIn x y c) t) :
    TResG t (x.mag + y.mag) c.alloc (max x.used y.used + 1) := by
  have hg := sAddIn_grown (a := x) (b := y) hc h31
  obtain ⟨hv, hm⟩ := SAddPost.spec hx hy (sAddIn_room x y c) hg.shape.alloc_lt (by rw [hg.sign, sc]; exact .inl rfl) h
  refine ⟨⟨hv, hm, ?_⟩, by rw [h.alloc]; exact hg.alloc, by rw [h.used]; exact clampUsed_le _ _⟩
  rw [h.sign, hg.sign, sc]; split <;> rfl

/-- The growing `s_mp_sub(x, y, x)` (`x` nonnegative, `|y| ≤ |x|`): `|x| - |y|`, grown only. -/
theorem ssub_post {x y t : MpInt} (hx : x.Shape) (hy : y.Shape) (sx : x.sign = Layout.mpZpos) (hm : y.mag ≤ x.mag)
    (h31 : x.used < 2 ^ 31) (h : SSubPost x y (sSubIn x x) t) :
    TResG t (x.mag - y.mag) x.alloc t.used := by
  have hg := sSubIn_grown (a := x) hx h31
  obtain ⟨hv, hm'⟩ := SSubPost.spec hx hy hm (sSubIn_room x x) hg.shape.alloc_lt (by rw [hg.sign, sx]; exact .inl rfl) h
  refine ⟨⟨hv, hm', ?_⟩, by rw [h.alloc]; exact hg.alloc, Nat.le_refl _⟩
  rw [h.sign, hg.sign, sx]; split <;> rfl

theorem withSign_mag (b : MpInt) (s : Nat) : (b.withSign s).mag = b.mag := rfl
theorem withSign_used (b : MpInt) (s : Nat) : (b.withSign s).used = b.used := rfl

theorem withSign_shape {b : MpInt} (hb : b.Shape) (s : Nat) : (b.withSign s).Shape := hb.withSign s

/-! ## Bounds on `used` -/

theorem mul_lt {X Y k l : Nat} (hx : X < radix ^ k) (hy : Y < radix ^ l) : X * Y < radix ^ (k + l) := by
  rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (by omega)

theorem add_lt {X Y k : Nat} (hx : X < radix ^ k) (hy : Y < radix ^ k) : X + Y < radix ^ (k + 1) := by
  rw [Nat.pow_succ]
  have : 2 ≤ radix := by decide
  calc X + Y < 2 * radix ^ k := by omega
    _ ≤ radix ^ k * radix := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ this

theorem lt_pow_mono {X k l : Nat} (h : X < radix ^ k) (hkl : k ≤ l) : X < radix ^ l :=
  Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right radix_pos hkl)

/-- A valid `t` below `radix^k`: at most `k` digits (`KSqr.used_le_of_lt`). -/
theorem used_le {t : MpInt} (ht : t.Valid) {k : Nat} (h : t.mag < radix ^ k) : t.used ≤ k :=
  KSqr.used_le_of_lt ht h

theorem mag_lt_used (t : MpInt) (ht : t.ShapeU) : t.mag < radix ^ t.used := KSqr.mag_lt t ht

/-- `|a| mod R < radix^B`, `|a| / R < radix^(a->used - B)`. -/
theorem lo_lt (A B : Nat) : A % radix ^ B < radix ^ B := KSqr.lo_lt A B
theorem hi_lt {a : MpInt} (ha : a.ShapeU) {B : Nat} (hB : B ≤ a.used) : a.mag / radix ^ B < radix ^ (a.used - B) :=
  KSqr.hi_lt ha hB

/-- `(x1 + x0)(y1 + y0)` with `x1 + x0 < radix^(ua - B + 1)` and `y1 + y0 < radix^(ub - B + 1)`. -/
theorem prod_lt {a b : MpInt} (ha : a.ShapeU) (hb : b.ShapeU) {B : Nat} (hBa : 2 * B ≤ a.used) (hBb : 2 * B ≤ b.used) :
    (a.mag / radix ^ B + a.mag % radix ^ B) * (b.mag / radix ^ B + b.mag % radix ^ B) <
      radix ^ ((a.used - B + 1) + (b.used - B + 1)) := by
  refine mul_lt (add_lt (hi_lt ha (by omega)) (lt_pow_mono (lo_lt _ _) (by omega)))
    (add_lt (hi_lt hb (by omega)) (lt_pow_mono (lo_lt _ _) (by omega)))

/-! ## The recomposition -/

/-- `t1 − x0` in `s_mp_sub(&t1, &x0, &t1)` is defined. -/
theorem sub_ok (A B' R : Nat) :
    A % R * (B' % R) + A / R * (B' / R) ≤ (A / R + A % R) * (B' / R + B' % R) := kara_sub_ok A B' R

/-- **The result**: `c = (x0y0 + t1 R) + x1y1 R² = |a| |b|`, read off the last `mp_add`. -/
theorem fin_mag {A B' R : Nat} {T V c : MpInt} (hc : c.Valid) (hv : c.val = T.val + V.val)
    (mT : T.mag = A % R * (B' % R) + ((A / R + A % R) * (B' / R + B' % R) - (A % R * (B' % R) + A / R * (B' / R))) * R)
    (sT : T.sign = Layout.mpZpos) (sV : V.sign = Layout.mpZpos)
    (mV : V.mag = A / R * (B' / R) * (R * R)) : c.mag = A * B' := by
  refine KSqr.mag_of_val hc ?_
  have e : T.mag + V.mag = A * B' := by rw [mT, mV]; exact kara_recompose A B' R
  rw [hv, KSqr.val_zpos sT, KSqr.val_zpos sV, ← e]; omega

/-! ## The temporaries' sizes -/

section
variable {a b : MpInt} {B : Nat}

/-- `x0y0 = |x0| |y0| < radix^(2B)`. -/
theorem u_lo {U : MpInt} (hU : U.Valid) (hm : U.mag = a.mag % radix ^ B * (b.mag % radix ^ B)) : U.used ≤ 2 * B :=
  used_le hU (by rw [hm, show 2 * B = B + B by omega]; exact mul_lt (lo_lt _ _) (lo_lt _ _))

/-- `x1y1 = |x1| |y1| < radix^((ua - B) + (ub - B))`. -/
theorem u_hi (ha : a.ShapeU) (hb : b.ShapeU) (hBa : B ≤ a.used) (hBb : B ≤ b.used) {V : MpInt} (hV : V.Valid)
    (hm : V.mag = a.mag / radix ^ B * (b.mag / radix ^ B)) : V.used ≤ (a.used - B) + (b.used - B) :=
  used_le hV (by rw [hm]; exact mul_lt (hi_lt ha hBa) (hi_lt hb hBb))

/-- Below `(x1 + x0)(y1 + y0)`. -/
theorem u_prod (ha : a.ShapeU) (hb : b.ShapeU) (hBa : 2 * B ≤ a.used) (hBb : 2 * B ≤ b.used) {T : MpInt} (hT : T.Valid)
    (hm : T.mag ≤ (a.mag / radix ^ B + a.mag % radix ^ B) * (b.mag / radix ^ B + b.mag % radix ^ B)) :
    T.used ≤ (a.used - B + 1) + (b.used - B + 1) :=
  used_le hT (Nat.lt_of_le_of_lt hm (prod_lt ha hb hBa hBb))

/-- Below `(x1 + x0)(y1 + y0) R`. -/
theorem u_shift (ha : a.ShapeU) (hb : b.ShapeU) (hBa : 2 * B ≤ a.used) (hBb : 2 * B ≤ b.used) {T : MpInt} (hT : T.Valid)
    (hm : T.mag ≤ (a.mag / radix ^ B + a.mag % radix ^ B) * (b.mag / radix ^ B + b.mag % radix ^ B) * radix ^ B) :
    T.used ≤ (a.used - B + 1) + (b.used - B + 1) + B :=
  used_le hT (Nat.lt_of_le_of_lt hm (by
    rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_right (prod_lt ha hb hBa hBb) (Nat.pow_pos radix_pos)))

/-- `x0y0 + t1 R` before the last `mp_add`. -/
theorem u_fin (ha : a.ShapeU) (hb : b.ShapeU) (hBa : 2 * B ≤ a.used) (hBb : 2 * B ≤ b.used) (hB2 : 2 ≤ B)
    {T : MpInt} (hT : T.Valid)
    (hm : T.mag = a.mag % radix ^ B * (b.mag % radix ^ B) +
      ((a.mag / radix ^ B + a.mag % radix ^ B) * (b.mag / radix ^ B + b.mag % radix ^ B) -
        (a.mag % radix ^ B * (b.mag % radix ^ B) + a.mag / radix ^ B * (b.mag / radix ^ B))) * radix ^ B) :
    T.used ≤ a.used + b.used + 1 := by
  refine used_le hT ?_
  rw [hm]
  have h1 : a.mag % radix ^ B * (b.mag % radix ^ B) < radix ^ (a.used + b.used) :=
    lt_pow_mono (mul_lt (lo_lt _ _) (lo_lt _ _)) (by omega)
  have h2 : ((a.mag / radix ^ B + a.mag % radix ^ B) * (b.mag / radix ^ B + b.mag % radix ^ B) -
        (a.mag % radix ^ B * (b.mag % radix ^ B) + a.mag / radix ^ B * (b.mag / radix ^ B))) * radix ^ B <
      radix ^ (a.used + b.used) := by
    refine lt_pow_mono (k := (a.used - B + 1) + (b.used - B + 1) + B) ?_ (by omega)
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (prod_lt ha hb hBa hBb))
      (Nat.pow_pos radix_pos)
  exact add_lt h1 h2

/-- `x1y1 R²` before the last `mp_add`. -/
theorem u_hi2 (ha : a.ShapeU) (hb : b.ShapeU) (hBa : B ≤ a.used) (hBb : B ≤ b.used) {V : MpInt} (hV : V.Valid)
    (hm : V.mag = a.mag / radix ^ B * (b.mag / radix ^ B) * (radix ^ B * radix ^ B)) :
    V.used ≤ a.used + b.used := by
  refine used_le hV ?_
  have e : radix ^ (a.used + b.used) = radix ^ ((a.used - B) + (b.used - B)) * (radix ^ B * radix ^ B) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  rw [hm, e]
  exact Nat.mul_lt_mul_of_pos_right (mul_lt (hi_lt ha hBa) (hi_lt hb hBb))
    (Nat.mul_pos (Nat.pow_pos radix_pos) (Nat.pow_pos radix_pos))

end

end Tom.KMul
