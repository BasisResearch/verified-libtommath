import Tom.Spec.ReduceStepL

/-!
# `mp_reduce` (Barrett) over the growing in-place callees: the model steps

`Spec/ReduceStepL.lean`'s chain with the callees as `mp_reduce` meets them in the image: the multipliers on their comba paths in place and growing (`Api/SMpMulHighDigsAF.lean`,
`Api/SMpMulDigsAF.lean`: value facts, no `alloc` equation), `mp_sub(x, &q, x)` and
`mp_add(x, &q, x)` growing (`Api/MpSubH.lean`'s `MpSubHA`, `Api/MpAddHA.lean`: `x' = x ∓ q` as
values), `mp_lshd(&q, um + 1)` growing (`Api/MpLshdH.lean`). So `Env` has no room for `x`
(`ReduceStepL.Env.xal`), and the signed accounts carry no allocation (`Acct _ 0`). Shared with
ReduceStepL: `Q1`, `Q3`, `r0`, `barrettR_ge`/`barrettR_lt`, the high product's shift.
-/

namespace Tom.ReduceStepG

open MpInt Ledger Reduce
open Tom.ReduceStepL (Q1 Q3 r0 barrettR_ge barrettR_lt natAbs_lt_of)

variable {x m mu q q1 q2 q3 q4 q5 q6 x1 x2 x3 xi x' : MpInt}

/-- The run's fixed facts. -/
structure Env (x m mu : MpInt) : Prop where
  vx : x.Valid
  xz : x.sign = Layout.mpZpos
  vm : m.Valid
  mz : m.sign = Layout.mpZpos
  vmu : mu.Valid
  muz : mu.sign = Layout.mpZpos
  k1 : 0 < m.used

theorem Env.mpos (e : Env x m mu) : 0 < m.mag :=
  Nat.lt_of_lt_of_le (Nat.pow_pos radix_pos) (MpInt.mag_ge e.vm e.k1)

/-- `mp_rshd` keeps the allocation. -/
theorem rshd_alloc {a a' : MpInt} {k : Nat} (h : RshdPost a k a') : a'.alloc = a.alloc := by
  rcases Nat.eq_zero_or_pos k with h0 | hk
  · rw [h.noop h0]
  · by_cases hu : a.used ≤ k
    · exact (h.zero hk hu).alloc
    · exact (h.shift hk (by omega)).alloc

/-- `mp_init_copy(&q, x)`, `mp_rshd(&q, um - 1)` (`ReduceStepL.Q1.of`). -/
theorem q1_of (e : Env x m mu) (hc : CopyPost x (MpInt.zeroN (initPrec x.used)) q) (hr : RshdPost q (m.used - 1) q1) :
    Q1 x m.used q1 := by
  have hp : x.used ≤ initPrec x.used ∧ initPrec x.used < 2 ^ 31 := by
    have := e.vx.used_le; have := e.vx.alloc_lt; unfold initPrec; rw [minPrec_eq]; omega
  have h := xfer_copy e.vx hp.1 hp.2 hc
  have hd := xfer_copyD e.vx.toShape hc
  have hr' := xfer_rshdD h.valid.toShape hr
  refine ⟨xfer_rshd0 ⟨h.valid, hc.alloc, by rw [h.mag, val_zpos e.xz]; rfl, by rw [hc.sign, e.xz]; split <;> rfl⟩ hr,
    ?_, ?_⟩
  · rw [hr'.1, hd.1]; rfl
  · rw [hr'.2, hd.2]; rfl

/-- `s_mp_mul_high_digs(&q, mu, &q, um)` (the high product plus low digits `lo` below `um`: the old ones
on the fast path, none on the slow one; valid, nonnegative), `mp_rshd(&q, um + 1)`: the estimate `q3`. -/
theorem q3_of (h : Q1 x m.used q1) (hsm : ¬ 2 ^ 27 < m.used) (hv : q2.Valid) {lo : Nat} (hlo : lo < radix ^ m.used)
    (hmag : q2.mag = lo + highProd q1.digit mu.digit q1.used mu.used m.used)
    (hs : q2.sign = Layout.mpZpos ∨ q2.sign = q1.sign) (hr : RshdPost q2 (m.used + 1) q3) : Q3 x m mu q3 := by
  have hz := h.set.zpos
  have hz2 : q2.sign = Layout.mpZpos := by rcases hs with e | e; exact e; rw [e, hz]
  have s := xfer_rshd0 ⟨hv, rfl, hmag, by rw [hz2]; split <;> rfl⟩ hr
  rw [highFast_shift _ _ _ hlo (highProd_dvd _ _ _ _ _)] at s
  unfold Q3 barrettQ3; rw [if_neg hsm, ← h.digit, ← h.used]; exact s.self

/-- The high product plus low digits below `k` has at most `q1->used + mu->used` digits. -/
theorem q2_used (hq1 : Shape q1) (hmu : mu.Shape) {k lo : Nat} (hv : q2.Valid) (hlo : lo < radix ^ k)
    (hmag : q2.mag = lo + highProd q1.digit mu.digit q1.used mu.used k)
    (hd : k ≤ q1.used + mu.used) : q2.used ≤ q1.used + mu.used := by
  refine used_le_of_lt hv ?_
  have hP := highProd_le q1.digit mu.digit q1.used mu.used k
  have h1 := natUpTo_lt _ hq1.digit_lt q1.used
  have h2 := natUpTo_lt _ hmu.digit_lt mu.used
  have hR : natUpTo q1.digit q1.used * natUpTo mu.digit mu.used < radix ^ (q1.used + mu.used) := by
    rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_lt_of_lt h1 h2
  obtain ⟨c, hc⟩ := highProd_dvd q1.digit mu.digit q1.used mu.used k
  obtain ⟨j, hj⟩ : ∃ j, q1.used + mu.used = k + j := ⟨q1.used + mu.used - k, by omega⟩
  have hD : 0 < radix ^ k := Nat.pow_pos radix_pos
  rw [hj, Nat.pow_add] at hR ⊢
  rw [hc] at hP
  have hcj : c < radix ^ j := Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt hP hR)
  have := Nat.mul_le_mul_left (radix ^ k) (show c + 1 ≤ radix ^ j by omega)
  rw [hmag, hc, Nat.mul_add, Nat.mul_one] at *
  omega

/-- `mp_mod_2d(x, MP_DIGIT_BIT (um + 1), x)`: `|x| mod D`. -/
theorem x1_of (e : Env x m mu) (h : Mod2dPost x (Layout.digitBits * (m.used + 1)) x x1) :
    Settled x1 x.alloc (x.mag % radix ^ (m.used + 1)) Layout.mpZpos := by
  have s := xfer_mod2d e.vx h; rwa [e.xz, Nat.pow_mul] at s

/-- A shaped, top-clamped, nonnegative integer is valid (the fast multiplier's output). -/
theorem valid_of {t : MpInt} (hs : t.Shape) (ht : 0 < t.used → t.digit (t.used - 1) ≠ 0)
    (hz : t.sign = Layout.mpZpos) : t.Valid :=
  { toShape := hs, top := ht, sign_ok := .inl hz, zero_pos := fun _ => hz }

/-- `s_mp_mul_digs(&q, m, &q, um + 1)` on its fast path: `q3 m mod D`. -/
theorem q4_of (h3 : Q3 x m mu q3) (hv : q4.Valid) (hm : q4.mag = q3.mag * m.mag % radix ^ (m.used + 1))
    (hz : q4.sign = Layout.mpZpos) :
    Settled q4 q4.alloc (barrettQ3 x m mu * m.mag % radix ^ (m.used + 1)) Layout.mpZpos :=
  ⟨hv, rfl, by rw [hm, h3.mag], by rw [hz]; split <;> rfl⟩

/-- `mp_sub(x, &q, x)`: `|x| mod D - q3 m mod D`, of either sign. -/
theorem x2_of {A B al1 al4 : Nat} (h1 : Settled x1 al1 A Layout.mpZpos) (h4 : Settled q4 al4 B Layout.mpZpos)
    (hA : A < radix ^ (m.used + 1)) (hB : B < radix ^ (m.used + 1)) (hv : x2.Valid) (hval : x2.val = x1.val - q4.val) :
    Acct x2 0 (m.used + 1) ((A : Int) - B) True := by
  have e2 : x2.val = (A : Int) - B := by rw [hval, h1.val, h4.val]
  refine ⟨hv, Nat.zero_le _, used_le_of_lt hv ?_, e2, trivial⟩
  have : x2.mag = ((A : Int) - B).natAbs := by rw [← e2, natAbs_val]
  rw [this]; exact natAbs_lt_of (by omega) (by omega)

/-- `mp_cmp_d(x, 0) != MP_LT`: nothing to repair. -/
theorem x3_ge (h2 : Acct x2 0 (m.used + 1)
      ((x.mag % radix ^ (m.used + 1) : Nat) - (barrettQ3 x m mu * m.mag % radix ^ (m.used + 1) : Nat)) True)
    (hge : ¬ cmpD x2 0 = .lt) : Acct x2 0 (m.used + 1) (r0 x m mu) True := by
  have := mt (xfer_cmpD0 h2).2 hge
  generalize hA : x.mag % radix ^ (m.used + 1) = A at h2 this
  generalize hB : barrettQ3 x m mu * m.mag % radix ^ (m.used + 1) = B at h2 this
  rw [r0, barrettR_ge (by rw [hA, hB]; omega), hA, hB]
  exact (show (A : Int) - B = ((A - B : Nat) : Int) by omega) ▸ h2

/-- `mp_set(&q, 1)`: a valid one with `q`'s allocation. -/
theorem q5_of (hq4 : q4.Shape) (hq0 : 0 < q4.alloc) (hs : SetPost q4 (1 % radix) q5) :
    Settled q5 q4.alloc 1 Layout.mpZpos := by
  have h := xfer_set hq4 hq0 (Nat.mod_lt 1 radix_pos) hs
  rwa [show 1 % radix = 1 from rfl] at h

/-- `mp_lshd(&q, um + 1)` (growing): `radix ^ (um + 1)`. -/
theorem q6_val (h5 : Settled q5 al 1 Layout.mpZpos) (hm6 : q6.mag = q5.mag * radix ^ (m.used + 1))
    (hs6 : q6.sign = q5.sign) : q6.val = ((radix ^ (m.used + 1) : Nat) : Int) := by
  rw [val_zpos (by rw [hs6]; exact h5.zpos), hm6, h5.mag, Nat.one_mul]

/-- `q = D` has `um + 2` digits. -/
theorem q6_used (h5 : Settled q5 al 1 Layout.mpZpos) (hv : q6.Valid) (hm6 : q6.mag = q5.mag * radix ^ (m.used + 1)) :
    q6.used ≤ m.used + 2 :=
  used_le_of_lt hv (by rw [hm6, h5.mag, Nat.one_mul]; exact Nat.pow_lt_pow_right (by decide) (by omega))

/-- `mp_cmp_d(x, 0) == MP_LT`: `mp_add(x, &q, x)` with `q = D`. -/
theorem x3_lt (h2 : Acct x2 0 (m.used + 1)
      ((x.mag % radix ^ (m.used + 1) : Nat) - (barrettQ3 x m mu * m.mag % radix ^ (m.used + 1) : Nat)) True)
    (hlt : cmpD x2 0 = .lt) (hv3 : x3.Valid) (hval3 : x3.val = x2.val + q6.val)
    (h6 : q6.val = ((radix ^ (m.used + 1) : Nat) : Int)) : Acct x3 0 (m.used + 1) (r0 x m mu) True := by
  have := (xfer_cmpD0 h2).1 hlt
  have hD := Nat.pow_pos (n := m.used + 1) radix_pos
  have h1 := Nat.mod_lt (barrettQ3 x m mu * m.mag) hD
  have e3 : x3.val = ((x.mag % radix ^ (m.used + 1) : Nat) : Int) - (barrettQ3 x m mu * m.mag % radix ^ (m.used + 1) : Nat)
      + ((radix ^ (m.used + 1) : Nat) : Int) := by rw [hval3, h2.val, h6]
  generalize hA : x.mag % radix ^ (m.used + 1) = A at this e3
  generalize hB : barrettQ3 x m mu * m.mag % radix ^ (m.used + 1) = B at this e3 h1
  have hr : r0 x m mu = A + radix ^ (m.used + 1) - B := by rw [r0, barrettR_lt (by rw [hA, hB]; omega), hA, hB]
  have hr' : x3.val = ((r0 x m mu : Nat) : Int) := by rw [e3, hr]; omega
  have hrl : r0 x m mu < radix ^ (m.used + 1) := by rw [hr]; omega
  refine ⟨hv3, Nat.zero_le _, used_le_of_lt hv3 ?_, hr', trivial⟩
  have : x3.mag = r0 x m mu := by
    have := natAbs_val x3; rw [hr'] at this; omega
  rw [this]; exact hrl

/-- `mp_reduce_setup`'s `mu` meets `Api.MpReduce.Res`'s digit bounds (`um ≤ mu->used ≤ um + 2`). -/
theorem setup_used {b a' : MpInt} (hb : b.Valid) (hb0 : 0 < b.mag) (h : ReduceSetupPost b a') :
    b.used ≤ a'.used ∧ a'.used ≤ b.used + 2 := by
  have hk : 0 < b.used := Nat.pos_of_ne_zero fun h0 => by rw [MpInt.mag_used_zero h0] at hb0; omega
  have hge := ReduceSetupPost.ge hb.toShape hb0 h
  have hle : a'.mag ≤ radix ^ (b.used + 1) := by
    rw [h.mag]
    have h1 := MpInt.mag_ge hb hk
    calc radix ^ (2 * b.used) / b.mag ≤ radix ^ (2 * b.used) / radix ^ (b.used - 1) := Nat.div_le_div_left h1 (Nat.pow_pos radix_pos)
      _ = radix ^ (b.used + 1) := by
        rw [Nat.pow_div (by omega) radix_pos]; congr 1; omega
  refine ⟨Nat.le_of_not_lt fun hlt => ?_, used_le_of_lt h.valid (Nat.lt_of_le_of_lt hle (Nat.pow_lt_pow_right (by decide) (by omega)))⟩
  have := MpInt.mag_lt h.valid.toShape
  have := Nat.pow_le_pow_right radix_pos (show a'.used ≤ b.used by omega)
  omega

/-! ## The final subtractions -/

/-- The loop head: `x` nonnegative, congruent to `r0`, not above it. -/
structure LI (x m mu xi : MpInt) : Prop where
  acct : Acct xi 0 (m.used + 1) xi.mag True
  res : xi.mag % m.mag = r0 x m mu % m.mag
  le : xi.mag ≤ r0 x m mu

theorem LI.start (h3 : Acct x3 0 (m.used + 1) (r0 x m mu) True) : LI x m mu x3 :=
  have e := h3.magN
  ⟨by rw [e]; exact h3, by rw [e], by rw [e]; exact Nat.le_refl _⟩

/-- `mp_cmp(x, m) != MP_LT`: `s_mp_sub(x, m, x)`, smaller. -/
theorem LI.step (e : Env x m mu) (h : LI x m mu xi) (hge : ¬ cmpS xi m = .lt) (hs : SSubPost xi m xi x') :
    LI x m mu x' ∧ x'.mag < xi.mag := by
  have hle : m.mag ≤ xi.mag := by
    have := mt (xfer_cmp h.acct e.vm (val_zpos e.mz)).2 hge; omega
  have s := xfer_ssub h.acct.settled e.vm hle hs
  have hlt := MpInt.mag_lt h.acct.valid.toShape
  have := Nat.pow_le_pow_right radix_pos h.acct.used
  have := e.mpos
  refine ⟨⟨⟨s.valid, Nat.zero_le _, used_le_of_lt s.valid (by rw [s.mag]; omega),
    val_zpos s.zpos, trivial⟩, ?_, ?_⟩, ?_⟩
  · rw [s.mag, ← Nat.mod_eq_sub_mod hle, h.res]
  · rw [s.mag]; have := h.le; omega
  · rw [s.mag]; omega

/-- `mp_cmp(x, m) != MP_LT`: `m` no longer than `x` (`s_mp_sub`'s residue). -/
theorem LI.ge (e : Env x m mu) (h : LI x m mu xi) (hge : ¬ cmpS xi m = .lt) : m.used ≤ xi.used := by
  have hle : m.mag ≤ xi.mag := by
    have := mt (xfer_cmp h.acct e.vm (val_zpos e.mz)).2 hge; omega
  exact MpInt.used_le_of_mag_le h.acct.valid.toShape e.vm hle

/-- `mp_cmp(x, m) == MP_LT`: `ReducePost`. -/
theorem LI.fin (e : Env x m mu) (h : LI x m mu xi) (hlt : cmpS xi m = .lt) : ReducePost x m mu xi := by
  have hl : xi.mag < m.mag := by have := (xfer_cmp h.acct e.vm (val_zpos e.mz)).1 hlt; omega
  refine ⟨h.acct.valid, ?_, h.acct.zpos (by omega)⟩
  unfold barrett
  rw [redLoop_spec id m.mag e.mpos _ (r0 x m mu) _ ⟨fun _ _ => Nat.le_refl _, fun _ _ => rfl⟩ (Nat.le_refl _)
    (Nat.lt_succ_self _), ← h.res, Nat.mod_eq_of_lt hl]

end Tom.ReduceStepG
