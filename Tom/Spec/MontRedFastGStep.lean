import Tom.Spec.MontRedStep
import Tom.Spec.Grow6Step

/-!
# `s_mp_montgomery_reduce_fast` growing `x`: the model steps of its assembly

`Fn/MontRedFastGMainG.lean` runs `Tom.Mont`'s column model (`fastRows`, `fastTail`) over `x` grown to
`mfIn x n->used` (`mp_grow(x, n->used + 1)` when `x->alloc ≤ n->used`): the same value, room for the
`n->used + 1` digits the copy-out writes. After the copy-out, `x->used := n->used + 1` and the digits
`W[n->used + i] & MP_MASK` (`outv`); `mp_clamp` of that is `MontRedStep.Mid` of the grown `x`
(`outv_mid`, the room proof's `xm_mag` over the Spec), from which `Mid.fin_lt`/`Mid.fin_sub` give
`RedcPost`. The columns' start `W0` is passed as a function equal to `x`'s digits below `x->used`.
-/

namespace Tom

namespace MontRedFastGStep

open MpInt Mont MontRedStep

/-- `x` after `if (x->alloc < n->used + 1) mp_grow(x, n->used + 1)`. -/
def mfIn (x : MpInt) (nu : Nat) : MpInt := if x.alloc ≤ nu then x.growTo (nu + 1) else x

theorem mfIn_valid {x : MpInt} (hx : x.Valid) {nu : Nat} (h31 : nu + 1 < 2 ^ 31) : (mfIn x nu).Valid := by
  unfold mfIn; split
  · exact MpInt.growTo_valid hx (by omega) h31
  · exact hx

theorem mfIn_room (x : MpInt) (nu : Nat) : nu < (mfIn x nu).alloc := by
  unfold mfIn; split
  · simp only [MpInt.growTo, MpInt.ofDigits]; omega
  · omega

theorem mfIn_used (x : MpInt) (nu : Nat) : (mfIn x nu).used = x.used := by
  unfold mfIn; split <;> rfl

theorem mfIn_sign (x : MpInt) (nu : Nat) : (mfIn x nu).sign = x.sign := by
  unfold mfIn; split <;> rfl

theorem mfIn_digit {x : MpInt} (hx : x.Shape) (nu : Nat) : (mfIn x nu).digit = x.digit := by
  unfold mfIn; split
  · exact MpInt.growTo_digit hx (by omega)
  · rfl

theorem mfIn_mag {x : MpInt} (hx : x.Shape) (nu : Nat) : (mfIn x nu).mag = x.mag := by
  unfold MpInt.mag; rw [mfIn_used, mfIn_digit hx]

/-- `x` after `mp_montgomery_reduce`'s `if (x->alloc < digs) mp_grow(x, digs)`, `digs = 2 n->used + 1`. -/
def mrIn (x : MpInt) (nu : Nat) : MpInt := if x.alloc < 2 * nu + 1 then x.growTo (2 * nu + 1) else x

theorem mrIn_valid {x : MpInt} (hx : x.Valid) {nu : Nat} (h31 : 2 * nu + 1 < 2 ^ 31) : (mrIn x nu).Valid := by
  unfold mrIn; split
  · exact MpInt.growTo_valid hx (by omega) h31
  · exact hx

theorem mrIn_room (x : MpInt) (nu : Nat) : 2 * nu + 1 ≤ (mrIn x nu).alloc := by
  unfold mrIn; split
  · simp only [MpInt.growTo, MpInt.ofDigits]; omega
  · omega

theorem mrIn_mag {x : MpInt} (hx : x.Shape) (nu : Nat) : (mrIn x nu).mag = x.mag := by
  unfold mrIn; split
  · unfold MpInt.mag; rw [show (x.growTo (2 * nu + 1)).used = x.used from rfl, MpInt.growTo_digit hx (by omega)]
  · rfl

theorem mrIn_sign (x : MpInt) (nu : Nat) : (mrIn x nu).sign = x.sign := by
  unfold mrIn; split <;> rfl

/-- What a growing Montgomery reduction leaves in `x`: `RedcPost` without the block (`x` may have been
re-placed): valid, `redc |x| |n| rho n->used`, `x`'s sign unless zero. -/
structure RedcV (x n : MpInt) (rho : Nat) (x' : MpInt) : Prop where
  valid : x'.Valid
  mag : x'.mag = redc x.mag n.mag rho n.used
  sign : x'.sign = if x'.used = 0 then Layout.mpZpos else x.sign

/-- `RedcPost` of `x` grown (the same value and sign) as `RedcV` of `x`. -/
theorem RedcPost.toV {x A n x' : MpInt} {rho : Nat} (hm : A.mag = x.mag) (hs : A.sign = x.sign)
    (h : RedcPost A n rho x') : RedcV x n rho x' :=
  ⟨h.valid, by rw [h.mag, hm], by rw [h.sign, hs]⟩

theorem RedcV.spec {x n x' : MpInt} {rho : Nat} (hrho : (n.mag * rho + 1) % radix = 0)
    (hx : x.mag < n.mag * radix ^ n.used) (h : RedcV x n rho x') :
    x'.Valid ∧ x'.mag < n.mag ∧ (x'.mag * radix ^ n.used) % n.mag = x.mag % n.mag :=
  RedcPost.spec (x' := x') (x := { x with alloc := x'.alloc }) hrho hx ⟨h.valid, rfl, h.mag, h.sign⟩

/-- What `mp_clamp` is handed: `used = n->used + 1`, the digits `F` below it. -/
def outv (A : MpInt) (nu : Nat) (F : Nat → Nat) : MpInt :=
  MpInt.ofDigits (nu + 1) A.alloc A.sign (fun i => if i < nu + 1 then F i else 0)

/-- The copy-out's digits: `W[n->used + i] & MP_MASK` after the rows and the tail carries. -/
def outF (n : MpInt) (rho : Nat) (W0 : Nat → Nat) (i : Nat) : Nat :=
  fastTail n.used (fastRows n.digit rho n.used W0 n.used) n.used (n.used + i) % 268435456

theorem outv_shape {A : MpInt} {nu : Nat} {F : Nat → Nat} (hA : nu < A.alloc) (h31 : A.alloc < 2 ^ 31)
    (hF : ∀ i, F i < radix) : (outv A nu F).Shape where
  len := MpInt.ofDigits_len _ _ _ _
  used_le := by simp only [outv, MpInt.ofDigits]; omega
  alloc_lt := h31
  digit_lt := fun i => by
    rw [outv, MpInt.ofDigits_digit]; split
    · split
      · exact hF i
      · exact radix_pos
    · exact radix_pos
  high_zero := fun i hi => by
    simp only [outv, MpInt.ofDigits] at hi
    rw [outv, MpInt.ofDigits_digit, if_neg (show ¬ i < nu + 1 by omega)]; split <;> rfl

theorem outF_lt (n : MpInt) (rho : Nat) (W0 : Nat → Nat) (i : Nat) : outF n rho W0 i < radix := Nat.mod_lt _ (by decide)

/-- **`mp_clamp` of the copy-out**: `T / R`, valid, the grown `x`'s block and sign. -/
theorem outv_mid {x n x2 : MpInt} {rho : Nat} {W0 : Nat → Nat} (hx : x.Valid) (hn : n.Valid)
    (hrho : (n.mag * rho + 1) % radix = 0) (hlt : x.mag < n.mag * radix ^ n.used)
    (hW0 : ∀ i, W0 i = if i < x.used then x.digit i else 0)
    (hcl : ClampPost (outv (mfIn x n.used) n.used (outF n rho W0)) x2) (h31 : n.used + 1 < 2 ^ 31) :
    Mid (mfIn x n.used) n rho x2 := by
  have hnu := nu_pos hlt
  have hA := mfIn_valid hx h31
  have hs := outv_shape (mfIn_room x n.used) hA.alloc_lt (outF_lt n rho W0)
  have hsg : (outv (mfIn x n.used) n.used (outF n rho W0)).sign = Layout.mpZpos ∨
      (outv (mfIn x n.used) n.used (outF n rho W0)).sign = Layout.mpNeg := hA.sign_ok
  have hcs := ClampPost.spec hs hsg hcl
  have hou : x.used ≤ 2 * n.used := by
    rcases Nat.eq_zero_or_pos x.used with h0 | h0
    · omega
    · have h1 := MpInt.mag_ge hx h0
      have h2 : radix ^ (x.used - 1) < radix ^ (2 * n.used) := by
        have := MpInt.mag_lt hn.toShape
        have : n.mag * radix ^ n.used < radix ^ n.used * radix ^ n.used :=
          Nat.mul_lt_mul_of_pos_right this (Nat.pow_pos radix_pos)
        rw [← Nat.pow_add, show n.used + n.used = 2 * n.used by omega] at this; omega
      have := (Nat.pow_lt_pow_iff_right (by simp only [radix, Layout.digitBits]; decide)).1 h2
      omega
  have hrho' : (n.mag % radix * rho + 1) % radix = 0 := by rw [← mul_add_one_mod]; exact hrho
  have hv : wVal W0 0 0 (2 * n.used + 1) = x.mag := by
    unfold wVal MpInt.mag
    rw [natUpTo_congr (2 * n.used + 1) (e := x.digit) (fun i _ => by
      simp only [Nat.not_lt_zero, if_false, hW0]; split
      · rfl
      · exact (hx.high_zero i (by omega)).symm)]
    exact natUpTo_zeros _ _ _ (by omega) fun i h1 _ => hx.high_zero i h1
  have hr := fastRows_spec x.mag n.mag rho n.used n.digit W0 rfl hrho' hv n.used (Nat.le_refl _)
  have ht := fastTail_val n.used (fastRows n.digit rho n.used W0 n.used) (2 * n.used + 1) n.used (by omega)
  rw [show n.used + n.used = 2 * n.used by omega, hr] at ht
  have ho := fastOut_val x.mag n.mag rho n.used _ (MpInt.mag_lt hn.toShape) hlt ht
  have hmag : (outv (mfIn x n.used) n.used (outF n rho W0)).mag = redcT x.mag n.mag rho n.used / radix ^ n.used := by
    rw [← ho]
    show natUpTo (outv (mfIn x n.used) n.used (outF n rho W0)).digit (n.used + 1) = _
    exact natUpTo_congr _ fun i hi => by
      rw [outv, MpInt.ofDigits_digit, if_pos (by have := mfIn_room x n.used; omega), if_pos hi]; rfl
  refine ⟨hcs.1, by rw [hcl.alloc]; rfl, by rw [hcs.2, hmag, mfIn_mag hx.toShape], ?_⟩
  rw [hcl.sign]; rfl

/-! ## The columns' bounds (the room proof's `rows_lt`, `row_lt`, `tail_lt` over any start `W0`) -/

section bounds
variable {nd W0 : Nat → Nat} {rho nu : Nat}

theorem rows_lt (hnd : ∀ i, nd i < radix) (hW0 : ∀ i, W0 i < radix) (hnu : nu ≤ 255) {j : Nat} (hj : j ≤ nu)
    (i : Nat) : fastRows nd rho nu W0 j i < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (fastRows_bound nd W0 rho nu hnd hW0 hnu j hj i) (wBound_lt _ _ _ (by omega))

theorem row_lt (hnd : ∀ i, nd i < radix) (hW0 : ∀ i, W0 i < radix) (hnu : nu ≤ 255) {j : Nat} (hj : j < nu)
    {mu : Nat} (hmu : mu < radix) (iy i : Nat) : wRow nd mu j (fastRows nd rho nu W0 j) iy i < 2 ^ 64 := by
  have h1 := wRow_le nd hnd mu j hmu (fastRows nd rho nu W0 j) iy i
  have h2 := fastRows_bound nd W0 rho nu hnd hW0 hnu j (by omega) i
  have h3 : (if j ≤ i ∧ i < j + iy then (radix - 1) * (radix - 1) else 0) ≤ (radix - 1) * (radix - 1) := by
    split <;> omega
  have h4 : wBound j (j + 1) i < 2 ^ 64 := wBound_lt _ _ _ (by omega)
  unfold wBound at *; rw [Nat.succ_mul] at h4; omega

theorem tail_lt (hnd : ∀ i, nd i < radix) (hW0 : ∀ i, W0 i < radix) (hnu : nu ≤ 255) (k i : Nat) :
    fastTail nu (fastRows nd rho nu W0 nu) k i < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (fastTail_bound nu _ hnu
    (fun i => fastRows_bound nd W0 rho nu hnd hW0 hnu nu (Nat.le_refl _) i) k i) (wBound_lt _ _ _ hnu)

/-- The inner loop's sum stays a word. -/
theorem row_sum_lt (hnd : ∀ i, nd i < radix) (hW0 : ∀ i, W0 i < radix) (hnu : nu ≤ 255) {j : Nat} (hj : j < nu)
    {mu : Nat} (hmu : mu < radix) (iy : Nat) :
    wRow nd mu j (fastRows nd rho nu W0 j) iy (j + iy) + nd iy * mu < 2 ^ 64 := by
  have := row_lt (rho := rho) hnd hW0 hnu hj hmu (iy + 1) (j + iy)
  simp only [wRow] at this
  rw [upd_same] at this; rw [Nat.mul_comm]; exact this

/-- The carry fix stays a word. -/
theorem fix_lt (hnd : ∀ i, nd i < radix) (hW0 : ∀ i, W0 i < radix) (hnu : nu ≤ 255) {j : Nat} (hj : j < nu) :
    let W := fastRows nd rho nu W0 j
    wRow nd (W j % radix * rho % radix) j W nu (j + 1) + wRow nd (W j % radix * rho % radix) j W nu j / 268435456 <
      2 ^ 64 := by
  intro W
  have := rows_lt (rho := rho) hnd hW0 hnu (show j + 1 ≤ nu by omega) (j + 1)
  simp only [fastRows, wFix] at this
  rw [upd_same] at this; exact this

theorem tfix_lt (hnd : ∀ i, nd i < radix) (hW0 : ∀ i, W0 i < radix) (hnu : nu ≤ 255) (k : Nat) :
    fastTail nu (fastRows nd rho nu W0 nu) k (nu + k + 1) + fastTail nu (fastRows nd rho nu W0 nu) k (nu + k) / 268435456 <
      2 ^ 64 := by
  have := tail_lt (rho := rho) hnd hW0 hnu (k + 1) (nu + k + 1)
  simp only [fastTail, wFix] at this
  rw [upd_same] at this; exact this

end bounds

end MontRedFastGStep

end Tom
