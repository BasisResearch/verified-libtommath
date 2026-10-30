import Tom.Spec.Ledger
import Tom.Spec.Reduce

/-!
# `mp_reduce` (Barrett): the model steps over the Ledger

`bn_mp_reduce.c` at `0x8000620c`, `k = m->used`, `D = radix^(k+1)`: `mp_init_copy(&q, x)`,
`mp_rshd(&q, k - 1)` (`Q1`: `⌊x / radix^(k-1)⌋` with its digits); `mp_mul(&q, mu, &q)` when
`k > 2^27`, else `s_mp_mul_high_digs(&q, mu, &q, k)` (fast or slow path); `mp_rshd(&q, k + 1)`
(`Q3`: `barrettQ3`); `mp_mod_2d(x, 28 (k + 1), x)` (`|x| mod D`); `s_mp_mul_digs(&q, m, &q,
k + 1)` (`q3 m mod D`); `mp_sub(x, &q, x)` (a signed account, possibly negative);
`mp_cmp_d(x, 0) == MP_LT` → `mp_set(&q, 1)`, `mp_lshd(&q, k + 1)`, `mp_add(x, &q, x)` (`+ D`);
then `while (mp_cmp(x, m) != MP_LT) s_mp_sub(x, m, x)` (`LI`, residue and bound kept), and
`ReducePost`.

Every call step is a Ledger transfer (`xfer_copy`/`xfer_copyD`, `xfer_rshd0`/`xfer_rshdD`,
`xfer_mul`, `xfer_mod2d`, `xfer_sub`, `xfer_cmpD0`, `xfer_set`, `xfer_lshd`, `xfer_add`,
`xfer_cmp`, `xfer_ssub`), over the callee Posts as the frozen contracts give them
(`s_mp_mul_high_digs`/`s_mp_mul_digs`: the fields of `Api/SMpMulHighDigs.lean`'s and
`Api/SMpMulDigs.lean`'s `Digs`, the path a proposition `F`). Own: the high product's shift
(`highFast_shift`, `highProd_dvd`) and the sign repair (`barrettR_ge`/`barrettR_lt`).

Assumptions beyond the C: `x`, `m`, `mu` nonnegative (`m < 0` loops forever: `mp_cmp(x, m)` is
never `MP_LT`), `x->alloc ≥ k + 3` (D5 for the in-place `mp_sub`/`mp_add`); each callee's own
precondition is a premise at its step (`hroom`, `hd`, `hq0`).
-/

namespace Tom.ReduceStepL

open MpInt Ledger Reduce

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
  xal : m.used + 3 ≤ x.alloc

theorem Env.mpos (e : Env x m mu) : 0 < m.mag :=
  Nat.lt_of_lt_of_le (Nat.pow_pos radix_pos) (MpInt.mag_ge e.vm e.k1)

/-! ## The quotient estimate -/

/-- `q1 = ⌊x / radix^(k-1)⌋` (`mp_init_copy`, `mp_rshd(&q, k - 1)`), with its digits. -/
structure Q1 (x : MpInt) (k : Nat) (q : MpInt) : Prop where
  set : Settled q (initPrec x.used) (x.mag / radix ^ (k - 1)) Layout.mpZpos
  digit : q.digit = q1Digit x k
  used : q.used = q1Used x k

theorem Q1.of (e : Env x m mu) (hc : CopyPost x (MpInt.zeroN (initPrec x.used)) q) (hr : RshdPost q (m.used - 1) q1) :
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

/-- `q3`: the estimate `barrettQ3` (`Reduce.lean`). -/
abbrev Q3 (x m mu q3 : MpInt) : Prop := Settled q3 q3.alloc (barrettQ3 x m mu) Layout.mpZpos

/-- `k > 2^27`: `mp_mul(&q, mu, &q)`, `mp_rshd(&q, k + 1)`. -/
theorem Q1.mul (e : Env x m mu) (h : Q1 x m.used q1) (hbig : 2 ^ 27 < m.used) (hm : MulPost q1 mu q2)
    (hr : RshdPost q2 (m.used + 1) q3) : Q3 x m mu q3 := by
  have s := xfer_rshd0 (xfer_mul h.set.val (val_zpos e.muz) hm) hr
  unfold Q3 barrettQ3; rw [if_pos hbig]; exact s.self

/-- `k ≤ 2^27`, the fast path of `s_mp_mul_high_digs(&q, mu, &q, k)` (in place: the low digits
of `q1` below `k` stay), `mp_rshd(&q, k + 1)`. -/
theorem Q1.highFast (e : Env x m mu) (h : Q1 x m.used q1) (hsm : ¬ 2 ^ 27 < m.used)
    (hd : m.used ≤ q1.used + mu.used) (hroom : q1.used + mu.used ≤ q1.alloc)
    (hm : MulHighFastPost q1 mu q1 q2 m.used) (hr : RshdPost q2 (m.used + 1) q3) : Q3 x m mu q3 := by
  have hz := h.set.zpos
  obtain ⟨hv, hmag⟩ := hm.spec h.set.valid.toShape e.vmu.toShape h.set.valid.toShape hd hroom (Or.inl hz)
  have s := xfer_rshd0 ⟨hv, rfl, hmag, by rw [hm.sign, hz]⟩ hr
  rw [highFast_shift _ _ _ (natUpTo_lt _ h.set.valid.digit_lt _) (highProd_dvd _ _ _ _ _)] at s
  unfold Q3 barrettQ3; rw [if_neg hsm, ← h.digit, ← h.used]; exact s.self

/-- `k ≤ 2^27`, the slow path (the high product in a fresh `t`). -/
theorem Q1.highSlow (h : Q1 x m.used q1) (hsm : ¬ 2 ^ 27 < m.used)
    (hm : MulHighPost q1 mu q2 m.used) (hr : RshdPost q2 (m.used + 1) q3) : Q3 x m mu q3 := by
  have s := xfer_rshd0 ⟨hm.valid, rfl, hm.spec.2, by rw [hm.sign]; split <;> rfl⟩ hr
  unfold Q3 barrettQ3; rw [if_neg hsm, ← h.digit, ← h.used]; exact s.self

/-! ## The remainder -/

/-- `mp_mod_2d(x, MP_DIGIT_BIT (k + 1), x)`: `|x| mod D`. -/
theorem x1_of (e : Env x m mu) (h : Mod2dPost x (Layout.digitBits * (m.used + 1)) x x1) :
    Settled x1 x.alloc (x.mag % radix ^ (m.used + 1)) Layout.mpZpos := by
  have s := xfer_mod2d e.vx h; rwa [e.xz, Nat.pow_mul] at s

/-- `s_mp_mul_digs(&q, m, &q, k + 1)` (`Digs`: `valid`, `mag`, the fast path's Post, the slow
path's sign): `q3 m mod D`. -/
theorem q4_of (h3 : Q3 x m mu q3) (F : Prop) (hv : q4.Valid) (hm : q4.mag = q3.mag * m.mag % radix ^ (m.used + 1))
    (hf : F → MulFastPost q3 m q3 q4 (m.used + 1)) (hs : ¬ F → q4.alloc = initPrec (m.used + 1) ∧ q4.sign = Layout.mpZpos) :
    Settled q4 q4.alloc (barrettQ3 x m mu * m.mag % radix ^ (m.used + 1)) Layout.mpZpos := by
  refine ⟨hv, rfl, by rw [hm, h3.mag], ?_⟩
  by_cases hF : F
  · rw [(hf hF).sign, h3.zpos]
  · rw [(hs hF).2]; split <;> rfl

theorem natAbs_lt_of {V : Int} {D : Nat} (h0 : -(D : Int) < V) (h1 : V < D) : V.natAbs < D := by omega

/-- `mp_sub(x, &q, x)`: `|x| mod D - q3 m mod D`, of either sign. -/
theorem x2_of (e : Env x m mu) {A B : Nat} (h1 : Settled x1 x.alloc A Layout.mpZpos) (h4 : Settled q4 q4.alloc B Layout.mpZpos)
    (hA : A < radix ^ (m.used + 1)) (hB : B < radix ^ (m.used + 1)) (hs : SubPost x1 q4 x1 x2) :
    Acct x2 x.alloc (m.used + 1) ((A : Int) - B) True :=
  have a1 := h1.acct hA trivial
  have a4 := h4.acct hB trivial
  xfer_sub a1 a4 (by have := a1.used; have := a4.used; have := e.xal; rw [h1.alloc]; omega)
    (natAbs_lt_of (by omega) (by omega)) hs

theorem barrettR_ge {x m k q3 : Nat} (h : q3 * m % radix ^ (k + 1) ≤ x % radix ^ (k + 1)) :
    barrettR x m k q3 = x % radix ^ (k + 1) - q3 * m % radix ^ (k + 1) := by
  unfold barrettR
  have := Nat.mod_lt x (Nat.pow_pos (n := k + 1) radix_pos)
  generalize x % radix ^ (k + 1) = A at *; generalize q3 * m % radix ^ (k + 1) = B at *
  rw [show A + radix ^ (k + 1) - B = A - B + radix ^ (k + 1) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem barrettR_lt {x m k q3 : Nat} (h : x % radix ^ (k + 1) < q3 * m % radix ^ (k + 1)) :
    barrettR x m k q3 = x % radix ^ (k + 1) + radix ^ (k + 1) - q3 * m % radix ^ (k + 1) := by
  unfold barrettR
  have := Nat.mod_lt (q3 * m) (Nat.pow_pos (n := k + 1) radix_pos)
  generalize x % radix ^ (k + 1) = A at *; generalize q3 * m % radix ^ (k + 1) = B at *
  exact Nat.mod_eq_of_lt (by omega)

/-- The remainder `barrettR` the loop starts from. -/
abbrev r0 (x m mu : MpInt) : Nat := barrettR x.mag m.mag m.used (barrettQ3 x m mu)

/-- `mp_cmp_d(x, 0) != MP_LT`: nothing to repair. -/
theorem x3_ge (h2 : Acct x2 x.alloc (m.used + 1)
      ((x.mag % radix ^ (m.used + 1) : Nat) - (barrettQ3 x m mu * m.mag % radix ^ (m.used + 1) : Nat)) True)
    (hge : ¬ cmpD x2 0 = .lt) : Acct x2 x.alloc (m.used + 1) (r0 x m mu) True := by
  have := mt (xfer_cmpD0 h2).2 hge
  generalize hA : x.mag % radix ^ (m.used + 1) = A at h2 this
  generalize hB : barrettQ3 x m mu * m.mag % radix ^ (m.used + 1) = B at h2 this
  rw [r0, barrettR_ge (by rw [hA, hB]; omega), hA, hB]
  exact (show (A : Int) - B = ((A - B : Nat) : Int) by omega) ▸ h2

/-- `mp_cmp_d(x, 0) == MP_LT`: `mp_set(&q, 1)`, `mp_lshd(&q, k + 1)`, `mp_add(x, &q, x)`. -/
theorem x3_lt (e : Env x m mu) (h2 : Acct x2 x.alloc (m.used + 1)
      ((x.mag % radix ^ (m.used + 1) : Nat) - (barrettQ3 x m mu * m.mag % radix ^ (m.used + 1) : Nat)) True)
    (hlt : cmpD x2 0 = .lt) (hq4 : q4.Shape) (hq0 : 0 < q4.alloc) (hs : SetPost q4 (1 % radix) q5)
    (hroom : q5.used + (m.used + 1) ≤ q5.alloc) (hl : LshdPost q5 (m.used + 1) q6) (ha : AddPost x2 q6 x2 x3) :
    Acct x3 x.alloc (m.used + 1) (r0 x m mu) True := by
  have := (xfer_cmpD0 h2).1 hlt
  have s6 := xfer_lshd (xfer_set hq4 hq0 (Nat.mod_lt _ radix_pos) hs) hroom hl
  rw [show 1 % radix = 1 from rfl, Nat.one_mul] at s6
  have a6 := s6.acct (U := m.used + 2) (Nat.pow_lt_pow_right (by decide) (by omega)) trivial
  have hD := Nat.pow_pos (n := m.used + 1) radix_pos
  have h1 := Nat.mod_lt (barrettQ3 x m mu * m.mag) hD
  generalize hA : x.mag % radix ^ (m.used + 1) = A at h2 this
  generalize hB : barrettQ3 x m mu * m.mag % radix ^ (m.used + 1) = B at h2 this h1
  have h3 := xfer_add (U' := m.used + 1) h2 a6 (by have := h2.used; have := h2.room; have := a6.used; have := e.xal; omega)
    (natAbs_lt_of (by omega) (by omega)) ha
  rw [r0, barrettR_lt (by rw [hA, hB]; omega), hA, hB]
  exact (show (A : Int) - B + ((radix ^ (m.used + 1) : Nat) : Int) = ((A + radix ^ (m.used + 1) - B : Nat) : Int) by omega) ▸ h3

/-! ## The final subtractions -/

/-- The loop head: `x` nonnegative, congruent to `r0`, not above it. -/
structure LI (x m mu xi : MpInt) : Prop where
  acct : Acct xi x.alloc (m.used + 1) xi.mag True
  res : xi.mag % m.mag = r0 x m mu % m.mag
  le : xi.mag ≤ r0 x m mu

theorem LI.start (h3 : Acct x3 x.alloc (m.used + 1) (r0 x m mu) True) : LI x m mu x3 :=
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
  refine ⟨⟨⟨s.valid, by rw [s.alloc]; exact h.acct.room, used_le_of_lt s.valid (by rw [s.mag]; omega),
    val_zpos s.zpos, trivial⟩, ?_, ?_⟩, ?_⟩
  · rw [s.mag, ← Nat.mod_eq_sub_mod hle, h.res]
  · rw [s.mag]; have := h.le; omega
  · rw [s.mag]; omega

/-- `mp_cmp(x, m) == MP_LT`: `ReducePost`. -/
theorem LI.fin (e : Env x m mu) (h : LI x m mu xi) (hlt : cmpS xi m = .lt) : ReducePost x m mu xi := by
  have hl : xi.mag < m.mag := by have := (xfer_cmp h.acct e.vm (val_zpos e.mz)).1 hlt; omega
  refine ⟨h.acct.valid, ?_, h.acct.zpos (by omega)⟩
  unfold barrett
  rw [redLoop_spec id m.mag e.mpos _ (r0 x m mu) _ ⟨fun _ _ => Nat.le_refl _, fun _ _ => rfl⟩ (Nat.le_refl _)
    (Nat.lt_succ_self _), ← h.res, Nat.mod_eq_of_lt hl]

end Tom.ReduceStepL
