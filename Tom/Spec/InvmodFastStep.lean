import Tom.Spec.Ledger
import Tom.Spec.Gcd
import Tom.Spec.CopyGStep

/-!
# `s_mp_invmod_fast`: the model steps over the Ledger

`bn_s_mp_invmod_fast.c` at `0x80003338` (checked against `experiments/disasm.txt`): `MP_IS_EVEN(b)`
→ `MP_VAL`; `mp_init_multi(&x, &y, &u, &v, &B, &D)` (structs at `sp+16 … sp+136`); `mp_copy(b, &x)`;
`mp_mod(a, b, &y)`; `MP_IS_ZERO(&x) || MP_IS_ZERO(&y)` → `MP_VAL`; `mp_copy(&x, &u)`,
`mp_copy(&y, &v)`, `mp_set(&D, 1)`; `top:` the `u` loop (`0x8000346c`: `mp_div_2(&u, &u)`, `B` odd →
`mp_sub(&B, &x, &B)`, `mp_div_2(&B, &B)`), the `v` loop (`0x800034f8`, the same on `v`, `D`),
`mp_cmp(&u, &v)` and two in-place `mp_sub`s, `u ≠ 0` → `top` (`0x800035a8`); `mp_cmp_d(&v, 1) != MP_EQ`
→ `MP_VAL`; `neg = a->sign`; `while (D.sign == MP_NEG) mp_add(&D, b, &D)` (`0x800035e0`);
`while (mp_cmp_mag(&D, b) != MP_LT) mp_sub(&D, b, &D)`; `mp_exch(&D, c)`; `c->sign = neg`; `mp_clear_multi`.

The C state is a Ledger account per temporary (`Tmp`: valid, `defPrec ≤ alloc`, `used ≤ defPrec`,
value, for the fresh ones; `x`, `y`: valid, at most `b->used` digits, value) and the model's `FastSt` (`Tom/Spec/Gcd.lean`); the cuts are `Loop` with the remaining
computation `kU` (at `top:`, the `u` loop's head) or `kV` (the `v` loop's head), `Mid` (after the
subtraction), `Done` (`u = 0`), `NA`/`NS` (the two normalisation loops). Every call is a transfer:
`xfer_copy`, `xfer_mod`, `xfer_set`, `xfer_div2`, `xfer_sub`, `xfer_add`, `xfer_cmp`, `xfer_cmpDeq`,
`xfer_cmpMag`; the macros `xfer_isOdd`, `xfer_isZero`, `xfer_isNeg`.

Callee Posts: as the frozen contracts give them (`Api/MpInitMulti.lean`: each temporary
`zeroN defPrec`; `Api/MpCopyG.lean`: `CopyPost s (copyIn s t) t'`, growing; `Api/MpSet.lean`: `SetPost a (1 % radix) a'`;
`Api/Div2.lean` `PostI`: `Div2Post a a a'`; `Api/MpSubAlias.lean`/`Api/MpAddAlias.lean` `PostCA`:
`SubPost a b a a'`, `AddPost a b a a'`; `Api/CmpS.lean`: `cmpS`; `Api/CmpD.lean`: `cmpD`;
`Api/Exch.lean`: the struct at `c` holds `D`). `mp_mod` and `mp_cmp_mag` have no frozen contract:
`ModPost` (`Tom/Spec/Div.lean`) and `cmpMag` (`Tom/Spec/Algo.lean`). `mp_clear_multi` leaves `c`.

Assumptions beyond the C (named premises): `b` positive (`Env`; no room, every
`mp_copy` into a temporary grows it). The in-place `mp_add`/`mp_sub` on `u`, `v`, `B`, `D` may grow their temporary
(`Api/MpAddHA.lean`, `Api/MpSubH.lean`: `mp_grow`, then the value): those temporaries are `Gt`
accounts (valid, the value; no digit bound — the coefficients `B`, `D` are not bounded by `b`'s
digits, a search shows `|B|/b` near 4.3 for 100-bit moduli), and each step takes the callee's
result as `valid`/`val`. `x`, `y` are
accounts of at most `b->used` digits (never written after their copy). `mp_init_multi` failing and every `MP_MEM` are the
machine contract's (`Api/Invmod.lean`), not the model's (`Gcd.lean` has no `MP_MEM` case).
-/

namespace Tom.InvmodFastStep

open MpInt Ledger Gcd

variable {a b c x y u v B D u1 v1 B1 B2 D1 D2 : MpInt} {t : FastSt}

/-! ## Temporaries -/

theorem defPrec_lt : defPrec < 2 ^ 31 := by unfold defPrec; decide

/-- A temporary of `mp_init_multi` as an account: valid, `defPrec ≤ alloc`, `used ≤ defPrec`. -/
abbrev Tmp (t : MpInt) (V : Int) : Prop := Acct t defPrec defPrec V True

theorem tmp_zero : Tmp (MpInt.zeroN defPrec) 0 :=
  ⟨MpInt.zeroN_valid defPrec_lt, Nat.le_refl _, Nat.zero_le _, MpInt.zeroN_val _, trivial⟩

/-- `mp_copy(s, &t)` into a temporary, growing it (`Api/MpCopyG.lean`): `s`'s digit bound and value. -/
theorem copyG {s t t0 : MpInt} {al U : Nat} {V : Int} {A : Prop} (hs : Acct s al U V A) (h0 : t0.Shape)
    (hc : CopyPost s (copyIn s t0) t) : Acct t 0 U V True :=
  have h := CopyPost.specG hs.valid h0 hc
  ⟨h.1, Nat.zero_le _, by rw [hc.used]; exact hs.used, by rw [h.2.2, hs.val], trivial⟩

theorem zeroS : (MpInt.zeroN defPrec).Shape := (MpInt.zeroN_valid defPrec_lt).toShape

/-- The temporary a growing `mp_copy` leaves is nonempty. -/
theorem copy_pos {s t : MpInt} (hs : s.Valid) (hc : CopyPost s (copyIn s (MpInt.zeroN defPrec)) t) : 0 < t.alloc := by
  rw [hc.alloc]
  exact Nat.lt_of_lt_of_le (show 0 < (MpInt.zeroN defPrec).alloc by unfold defPrec; decide)
    (copyIn_grown zeroS (Nat.lt_of_le_of_lt hs.used_le hs.alloc_lt)).alloc

/-- `mp_set(&t, 1)` on a fresh temporary. -/
theorem Tmp.set1 {t : MpInt} (hs : SetPost (MpInt.zeroN defPrec) (1 % radix) t) : Tmp t 1 := by
  have e : 1 % radix = 1 := rfl
  have s := xfer_set (MpInt.zeroN_valid defPrec_lt).toShape (by unfold defPrec; decide)
    (Nat.mod_lt _ radix_pos) hs
  rw [e] at s
  exact (s.acct (U := defPrec) (Nat.one_lt_pow (by unfold defPrec; decide) (by decide)) trivial).mono (Nat.le_refl _)

/-- A temporary that in-place `mp_add`/`mp_sub` may grow: valid, with value `V`. -/
structure Gt (t : MpInt) (V : Int) : Prop where
  valid : t.Valid
  val : t.val = V

theorem Gt.acct {t : MpInt} {V : Int} (h : Gt t V) : Acct t 0 t.used V True :=
  ⟨h.valid, Nat.zero_le _, Nat.le_refl _, h.val, trivial⟩

theorem Tmp.gt {t : MpInt} {V : Int} (h : Tmp t V) : Gt t V := ⟨h.valid, h.val⟩

theorem Gt.of {t : MpInt} {al U : Nat} {V : Int} {A : Prop} (h : Acct t al U V A) : Gt t V := ⟨h.valid, h.val⟩

/-- `mp_sub(&t, n, &t)`, growing: the callee's result (valid, the difference). -/
theorem Gt.sub {t t' n : MpInt} {V W : Int} {alb Ub : Nat} {Ab : Prop} (h : Gt t V) (hn : Acct n alb Ub W Ab)
    (hv : t'.Valid) (he : t'.val = t.val - n.val) : Gt t' (V - W) :=
  ⟨hv, by rw [he, h.val, hn.val]⟩

/-- `mp_add(&t, n, &t)`, growing. -/
theorem Gt.add {t t' n : MpInt} {V W : Int} {alb Ub : Nat} {Ab : Prop} (h : Gt t V) (hn : Acct n alb Ub W Ab)
    (hv : t'.Valid) (he : t'.val = t.val + n.val) : Gt t' (V + W) :=
  ⟨hv, by rw [he, h.val, hn.val]⟩

/-- `mp_div_2(&t, &t)` on an even value: the exact half. -/
theorem Gt.half {t t' : MpInt} {V : Int} (h : Gt t V) (he : V % 2 = 0) (hd : Div2Post t t t') : Gt t' (V / 2) := by
  have h2 := xfer_div2 h.acct hd
  rw [Int.tdiv_eq_ediv_of_dvd (Int.dvd_of_emod_eq_zero he)] at h2
  exact ⟨h2.valid, h2.val⟩

/-- `mp_div_2(&t, &t)` on a nonnegative value. -/
theorem Gt.halfN {t t' : MpInt} {n : Nat} (h : Gt t n) (hd : Div2Post t t t') : Gt t' ((n / 2 : Nat) : Int) := by
  have h2 := xfer_div2 h.acct hd
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega), show ((n : Int) / 2) = ((n / 2 : Nat) : Int) by omega] at h2
  exact ⟨h2.valid, h2.val⟩

theorem even_of {t : MpInt} {al U : Nat} {V : Int} {A : Prop} (h : Acct t al U V A) (he : ¬ isOdd t) : V % 2 = 0 := by
  have := mt (xfer_isOdd h).2 he; omega

theorem odd_of {t : MpInt} {al U : Nat} {V : Int} {A : Prop} (h : Acct t al U V A) (ho : isOdd t) : V % 2 = 1 :=
  (xfer_isOdd h).1 ho

/-! ## The run -/

/-- The run's fixed facts: `a`, `b` valid, `b` positive (as `mp_invmod` calls it). -/
structure Env (a b : MpInt) : Prop where
  va : a.Valid
  vb : b.Valid
  bz : b.sign = Layout.mpZpos

theorem Env.acct (e : Env a b) : Acct b 0 b.used b.mag True := ⟨e.vb, Nat.zero_le _, Nat.le_refl _, val_zpos e.bz, trivial⟩

/-- The model's final state (`fastTop` from `u = b`, `v = a mod b`, `B = 0`, `D = 1`). -/
abbrev Rf (a b : MpInt) : FastSt := fastTop b.mag (fastInit b.mag (invmodRem a b))

/-- Past the two `MP_VAL` exits: `b` odd, `a mod b ≠ 0`. -/
structure Go (a b : MpInt) : Prop where
  odd : b.mag % 2 = 1
  y0 : invmodRem a b ≠ 0

theorem Go.res (g : Go a b) :
    fastRes b.mag (invmodRem a b) = if (Rf a b).v = 1 then some (norm b.mag (Rf a b).D) else none := by
  have := g.odd; have := g.y0
  unfold fastRes; rw [if_neg (by omega), if_neg (by omega)]

/-- An `MP_VAL` exit leaves `c`: the Post when the model says `none`. -/
theorem err_post (h : fastRes b.mag (invmodRem a b) = none) : InvmodFastPost a b c c Layout.mpVal := by
  have k : ∀ d, fastRes b.mag (invmodRem a b) ≠ some d := fun d hd => by rw [h] at hd; cases hd
  exact ⟨fun _ => ⟨rfl, rfl⟩, fun d hd => absurd hd (k d), fun d hd => absurd hd (k d),
    fun d hd => absurd hd (k d), fun d hd => absurd hd (k d), fun d hd => absurd hd (k d)⟩

/-- `if (MP_IS_EVEN(b)) return MP_VAL;` -/
theorem even_exit (e : Env a b) (hb : ¬ isOdd b) : InvmodFastPost a b c c Layout.mpVal := by
  have := even_of e.acct hb
  exact err_post (by unfold fastRes; rw [if_pos (by omega)])

/-- After `mp_init_multi`, `mp_copy(b, &x)`, `mp_mod(a, b, &y)`. -/
structure XY (a b x y : MpInt) : Prop where
  x : Acct x 0 b.used b.mag True
  y : Acct y 0 b.used (invmodRem a b) True

theorem invmodRem_cast (hb : b.sign = Layout.mpZpos) (h0 : 0 < b.mag) : (invmodRem a b : Int) = a.val % b.val := by
  unfold invmodRem; exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by rw [val_zpos hb]; omega))

/-- `mp_copy(b, &x)`, `mp_mod(a, b, &y)` (`b` odd: past the first exit). -/
theorem xy_of (e : Env a b) (hb : isOdd b) (hx : CopyPost b (copyIn b (MpInt.zeroN defPrec)) x) (hy : ModPost a b y) :
    XY a b x y where
  x := copyG e.acct zeroS hx
  y := by
    have h := xfer_modA e.va e.vb e.bz hb.1 hy
    have := odd_of e.acct hb
    exact ⟨h.valid, h.room, h.used, by rw [h.val, invmodRem_cast e.bz (by omega)], trivial⟩

/-- `if (MP_IS_ZERO(&x) || MP_IS_ZERO(&y)) MP_VAL`. -/
theorem XY.zero (h : XY a b x y) (hz : x.used = 0 ∨ y.used = 0) : InvmodFastPost a b c c Layout.mpVal := by
  refine err_post ?_
  unfold fastRes
  by_cases h0 : b.mag % 2 = 0
  · rw [if_pos h0]
  · rw [if_neg h0, if_pos]
    rcases hz with hz | hz
    · have := (xfer_isZero h.x).1 hz; omega
    · have := (xfer_isZero h.y).1 hz; omega

/-! ## The loop -/

/-- After the subtraction: `if (!MP_IS_ZERO(&u)) goto top`. -/
def kSub (X : Nat) (p : FastSt) : FastSt := if p.u = 0 then p else fastTop X p

/-- What remains from the head of the `v` loop. -/
def kV (X : Nat) (t : FastSt) : FastSt := kSub X (fastSub (fastLoopV X t))

/-- What remains from the head of the `u` loop (`top:`). -/
def kU (X : Nat) (t : FastSt) : FastSt := kV X (fastLoopU X t)

theorem kU_top {X : Nat} (hu : 0 < t.u) (hv : 0 < t.v) : kU X t = fastTop X t := by
  rw [fastTop_eq X t hu hv]; rfl

theorem loopU_half {X : Nat} (h0 : 0 < t.u) (he : t.u % 2 = 0) : fastLoopU X t = fastLoopU X (fastHalfU X t) := by
  rw [fastLoopU, dif_pos ⟨by omega, he⟩]

theorem loopU_odd {X : Nat} (ho : t.u % 2 = 1) : fastLoopU X t = t := by rw [fastLoopU, dif_neg (by omega)]

theorem loopV_half {X : Nat} (h0 : 0 < t.v) (he : t.v % 2 = 0) : fastLoopV X t = fastLoopV X (fastHalfV X t) := by
  rw [fastLoopV, dif_pos ⟨by omega, he⟩]

theorem loopV_odd {X : Nat} (ho : t.v % 2 = 1) : fastLoopV X t = t := by rw [fastLoopV, dif_neg (by omega)]

/-- A loop cut: the temporaries hold `t`, positive, and `k t` is the model's final state. -/
structure Loop (a b : MpInt) (k : FastSt → FastSt) (x u v B D : MpInt) (t : FastSt) : Prop where
  go : Go a b
  x : Acct x 0 b.used b.mag True
  u : Gt u t.u
  v : Gt v t.v
  B : Gt B t.B
  D : Gt D t.D
  u_pos : 0 < t.u
  v_pos : 0 < t.v
  run : k t = Rf a b

/-- `mp_copy(&x, &u)`, `mp_copy(&y, &v)`, `mp_set(&D, 1)`: `top:` at `fastInit`. -/
theorem XY.init (e : Env a b) (h : XY a b x y) (hb : isOdd b) (hz : ¬ (x.used = 0 ∨ y.used = 0))
    (hu : CopyPost x (copyIn x (MpInt.zeroN defPrec)) u) (hv : CopyPost y (copyIn y (MpInt.zeroN defPrec)) v)
    (hD : SetPost (MpInt.zeroN defPrec) (1 % radix) D) :
    Loop a b (kU b.mag) x u v (MpInt.zeroN defPrec) D (fastInit b.mag (invmodRem a b)) := by
  have ho := odd_of e.acct hb
  have hy : (invmodRem a b : Int) ≠ 0 := fun e0 => hz (Or.inr ((xfer_isZero h.y).2 e0))
  have hu0 : 0 < b.mag := by omega
  have hy0 : 0 < invmodRem a b := by omega
  exact { go := ⟨by omega, by omega⟩, x := h.x, u := Gt.of (copyG h.x zeroS hu),
          v := Gt.of (copyG h.y zeroS hv), B := tmp_zero.gt, D := (Tmp.set1 hD).gt, u_pos := hu0,
          v_pos := hy0, run := kU_top hu0 hy0 }

/-- `u` even, `B` odd: `mp_div_2(&u, &u)`, `mp_sub(&B, &x, &B)`, `mp_div_2(&B, &B)`. -/
theorem Loop.halfU_odd (h : Loop a b (kU b.mag) x u v B D t) (he : ¬ isOdd u) (hu : Div2Post u u u1)
    (ho : isOdd B) (hv1 : B1.Valid) (hs : B1.val = B.val - x.val) (hB : Div2Post B1 B1 B2) :
    Loop a b (kU b.mag) x u1 v B2 D (fastHalfU b.mag t) := by
  have hue := even_of h.u.acct he
  have hBo := odd_of h.B.acct ho
  have := h.go.odd; have := h.u_pos
  exact { go := h.go, x := h.x, u := h.u.halfN hu, v := h.v, D := h.D, v_pos := h.v_pos
          B := by
            show Gt B2 ((if t.B % 2 = 1 then t.B - b.mag else t.B) / 2)
            rw [if_pos hBo]; exact (Gt.sub h.B h.x hv1 hs).half (by omega) hB
          u_pos := by show 0 < t.u / 2; omega
          run := by unfold kU; rw [← loopU_half h.u_pos (by omega)]; exact h.run }

/-- `u` even, `B` even: `mp_div_2(&u, &u)`, `mp_div_2(&B, &B)`. -/
theorem Loop.halfU_even (h : Loop a b (kU b.mag) x u v B D t) (he : ¬ isOdd u) (hu : Div2Post u u u1)
    (hBe : ¬ isOdd B) (hB : Div2Post B B B2) : Loop a b (kU b.mag) x u1 v B2 D (fastHalfU b.mag t) := by
  have hue := even_of h.u.acct he
  have hBe' := even_of h.B.acct hBe
  have := h.u_pos
  exact { go := h.go, x := h.x, u := h.u.halfN hu, v := h.v, D := h.D, v_pos := h.v_pos
          B := by
            show Gt B2 ((if t.B % 2 = 1 then t.B - b.mag else t.B) / 2)
            rw [if_neg (by omega)]; exact h.B.half hBe' hB
          u_pos := by show 0 < t.u / 2; omega
          run := by unfold kU; rw [← loopU_half h.u_pos (by omega)]; exact h.run }

/-- `u` odd: the `u` loop exits to the `v` loop. -/
theorem Loop.exitU (h : Loop a b (kU b.mag) x u v B D t) (ho : isOdd u) : Loop a b (kV b.mag) x u v B D t :=
  { h with run := by have := h.run; unfold kU at this; rwa [loopU_odd (by have := odd_of h.u.acct ho; omega)] at this }

/-- `v` even, `D` odd: `mp_div_2(&v, &v)`, `mp_sub(&D, &x, &D)`, `mp_div_2(&D, &D)`. -/
theorem Loop.halfV_odd (h : Loop a b (kV b.mag) x u v B D t) (he : ¬ isOdd v) (hv : Div2Post v v v1)
    (ho : isOdd D) (hv1 : D1.Valid) (hs : D1.val = D.val - x.val) (hD : Div2Post D1 D1 D2) :
    Loop a b (kV b.mag) x u v1 B D2 (fastHalfV b.mag t) := by
  have hve := even_of h.v.acct he
  have hDo := odd_of h.D.acct ho
  have := h.go.odd; have := h.v_pos
  exact { go := h.go, x := h.x, u := h.u, v := h.v.halfN hv, B := h.B, u_pos := h.u_pos
          D := by
            show Gt D2 ((if t.D % 2 = 1 then t.D - b.mag else t.D) / 2)
            rw [if_pos hDo]; exact (Gt.sub h.D h.x hv1 hs).half (by omega) hD
          v_pos := by show 0 < t.v / 2; omega
          run := by unfold kV; rw [← loopV_half h.v_pos (by omega)]; exact h.run }

/-- `v` even, `D` even: `mp_div_2(&v, &v)`, `mp_div_2(&D, &D)`. -/
theorem Loop.halfV_even (h : Loop a b (kV b.mag) x u v B D t) (he : ¬ isOdd v) (hv : Div2Post v v v1)
    (hDe : ¬ isOdd D) (hD : Div2Post D D D2) : Loop a b (kV b.mag) x u v1 B D2 (fastHalfV b.mag t) := by
  have hve := even_of h.v.acct he
  have hDe' := even_of h.D.acct hDe
  have := h.v_pos
  exact { go := h.go, x := h.x, u := h.u, v := h.v.halfN hv, B := h.B, u_pos := h.u_pos
          D := by
            show Gt D2 ((if t.D % 2 = 1 then t.D - b.mag else t.D) / 2)
            rw [if_neg (by omega)]; exact h.D.half hDe' hD
          v_pos := by show 0 < t.v / 2; omega
          run := by unfold kV; rw [← loopV_half h.v_pos (by omega)]; exact h.run }

/-- After the subtraction (`u` may be zero). -/
structure Mid (a b : MpInt) (x u v B D : MpInt) (t : FastSt) : Prop where
  go : Go a b
  x : Acct x 0 b.used b.mag True
  u : Gt u t.u
  v : Gt v t.v
  B : Gt B t.B
  D : Gt D t.D
  v_pos : 0 < t.v
  run : kSub b.mag t = Rf a b

theorem Loop.run_sub (h : Loop a b (kV b.mag) x u v B D t) (ho : isOdd v) : kSub b.mag (fastSub t) = Rf a b := by
  have := h.run; unfold kV at this; rwa [loopV_odd (by have := odd_of h.v.acct ho; omega)] at this

/-- `v` odd, `mp_cmp(&u, &v) != MP_LT`: `mp_sub(&u, &v, &u)`, `mp_sub(&B, &D, &B)`. -/
theorem Loop.sub_ge (h : Loop a b (kV b.mag) x u v B D t) (ho : isOdd v) (hc : ¬ cmpS u v = .lt)
    (hv1 : u1.Valid) (hs1 : u1.val = u.val - v.val) (hv2 : B1.Valid) (hs2 : B1.val = B.val - D.val) :
    Mid a b x u1 v B1 D (fastSub t) := by
  have hle : t.v ≤ t.u := by have := mt (xfer_cmp h.u.acct h.v.valid h.v.val).2 hc; omega
  have hrun := h.run_sub ho
  have e : fastSub t = { t with u := t.u - t.v, B := t.B - t.D } := by unfold fastSub; rw [if_pos hle]
  rw [e] at hrun ⊢
  exact { go := h.go, x := h.x, v := h.v, D := h.D, v_pos := h.v_pos, run := hrun
          B := Gt.sub h.B h.D.acct hv2 hs2
          u := by show Gt u1 ((t.u - t.v : Nat) : Int); rw [Int.ofNat_sub hle]; exact Gt.sub h.u h.v.acct hv1 hs1 }

/-- `v` odd, `mp_cmp(&u, &v) == MP_LT`: `mp_sub(&v, &u, &v)`, `mp_sub(&D, &B, &D)`. -/
theorem Loop.sub_lt (h : Loop a b (kV b.mag) x u v B D t) (ho : isOdd v) (hc : cmpS u v = .lt)
    (hv1 : v1.Valid) (hs1 : v1.val = v.val - u.val) (hv2 : D1.Valid) (hs2 : D1.val = D.val - B.val) :
    Mid a b x u v1 B D1 (fastSub t) := by
  have hlt : t.u < t.v := by have := (xfer_cmp h.u.acct h.v.valid h.v.val).1 hc; omega
  have hrun := h.run_sub ho
  have e : fastSub t = { t with v := t.v - t.u, D := t.D - t.B } := by unfold fastSub; rw [if_neg (by omega)]
  rw [e] at hrun ⊢
  exact { go := h.go, x := h.x, u := h.u, B := h.B, run := hrun, D := Gt.sub h.D h.B.acct hv2 hs2
          v := by show Gt v1 ((t.v - t.u : Nat) : Int); rw [Int.ofNat_sub (by omega)]; exact Gt.sub h.v h.u.acct hv1 hs1
          v_pos := by show 0 < t.v - t.u; omega }

/-- The measure of the outer loop: a pass from positive `u`, `v` lowers `u + v`. -/
theorem sub_lt_meas (hu : 0 < t.u) (hv : 0 < t.v) : (fastSub t).u + (fastSub t).v < t.u + t.v := by
  unfold fastSub; split <;> simp only <;> omega

/-- `!MP_IS_ZERO(&u)`: `goto top`. -/
theorem Mid.top (h : Mid a b x u v B D t) (hz : ¬ u.used = 0) : Loop a b (kU b.mag) x u v B D t := by
  have hu : 0 < t.u := by have := mt (xfer_isZero h.u.acct).2 hz; omega
  exact { h with u_pos := hu, run := by rw [kU_top hu h.v_pos, ← h.run, kSub, if_neg (by omega)] }

/-- The loop's exit (`u = 0`): `v`, `D` hold the model's final state. -/
structure Done (a b v D : MpInt) : Prop where
  go : Go a b
  v : Gt v (Rf a b).v
  D : Gt D (Rf a b).D

theorem Mid.done (h : Mid a b x u v B D t) (hz : u.used = 0) : Done a b v D := by
  have hu : t.u = 0 := by have := (xfer_isZero h.u.acct).1 hz; omega
  have e : t = Rf a b := by rw [← h.run, kSub, if_pos hu]
  subst e
  exact ⟨h.go, h.v, h.D⟩

/-- `mp_cmp_d(&v, 1) != MP_EQ`: no inverse. -/
theorem Done.bad (h : Done a b v D) (hne : ¬ cmpD v 1 = .eq) : InvmodFastPost a b c c Layout.mpVal := by
  have := mt (xfer_cmpDeq h.v.acct (by decide)).2 hne
  exact err_post (by rw [h.go.res, if_neg (by omega)])

/-! ## The normalisation loops (shared with `s_mp_invmod_slow`) -/

/-- `while (X < 0) X += b` at its head: `X` holds `W`, and the two loops make `Z` normalised of `W`. -/
structure NA (P : Prop) (b X : MpInt) (Z W : Int) : Prop where
  aux : P
  pos : 0 < b.mag
  X : Gt X W
  run : norm b.mag Z = subDown b.mag (addUp b.mag W)

/-- `while (|X| ≥ b) X -= b` at its head: `X ≥ 0`. -/
structure NS (P : Prop) (b X : MpInt) (Z W : Int) : Prop where
  aux : P
  pos : 0 < b.mag
  X : Gt X W
  nonneg : 0 ≤ W
  run : norm b.mag Z = subDown b.mag W

/-- `X < 0`: `mp_add(&X, b, &X)`, growing. -/
theorem NA.add {P : Prop} {X X1 : MpInt} {Z W : Int} (h : NA P b X Z W) (e : Env a b) (hW : W < 0)
    (hv : X1.Valid) (ha : X1.val = X.val + b.val) : NA P b X1 Z (W + b.mag) :=
  ⟨h.aux, h.pos, Gt.add h.X e.acct hv ha, by rw [h.run, addUp, dif_pos ⟨hW, h.pos⟩]⟩

theorem NA.exit {P : Prop} {X : MpInt} {Z W : Int} (h : NA P b X Z W) (hW : ¬ W < 0) : NS P b X Z W :=
  ⟨h.aux, h.pos, h.X, by omega, by rw [h.run, addUp, dif_neg (by omega)]⟩

/-- `mp_cmp_mag(&X, b) != MP_LT`: `mp_sub(&X, b, &X)`, growing. -/
theorem NS.sub {P : Prop} {X X1 : MpInt} {Z W : Int} (h : NS P b X Z W) (e : Env a b) (hc : ¬ cmpMag X b = .lt)
    (hv : X1.Valid) (hs : X1.val = X.val - b.val) : NS P b X1 Z (W - b.mag) := by
  have hge : (b.mag : Int) ≤ W := by
    have := mt (xfer_cmpMag h.X.acct e.vb).2 hc; have := Int.natAbs_of_nonneg h.nonneg; omega
  exact ⟨h.aux, h.pos, Gt.sub h.X e.acct hv hs, by omega, by rw [h.run, subDown, dif_pos ⟨hge, h.pos⟩]⟩

/-- `mp_cmp_mag(&X, b) == MP_LT`: `X` is `Z` normalised into `[0, b)`. -/
theorem NS.fin {P : Prop} {X : MpInt} {Z W : Int} (h : NS P b X Z W) (e : Env a b) (hc : cmpMag X b = .lt) :
    norm b.mag Z = W ∧ W < b.mag := by
  have hlt : W < b.mag := by
    have := (xfer_cmpMag h.X.acct e.vb).1 hc; have := Int.natAbs_of_nonneg h.nonneg; omega
  exact ⟨by rw [h.run, subDown, dif_neg (by omega)], hlt⟩

/-- The `mp_sub` loop's measure: a step lowers `W ≥ b > 0`. -/
theorem NS.meas {P : Prop} {X : MpInt} {Z W : Int} (h : NS P b X Z W) (e : Env a b) (hc : ¬ cmpMag X b = .lt) :
    (W - b.mag).toNat < W.toNat := by
  have := mt (xfer_cmpMag h.X.acct e.vb).2 hc; have := Int.natAbs_of_nonneg h.nonneg; have := h.pos; omega

/-! ## The exit -/

/-- Past `mp_cmp_d(&v, 1) == MP_EQ`. -/
structure Ok (a b : MpInt) : Prop where
  go : Go a b
  v1 : (Rf a b).v = 1

/-- `mp_cmp_d(&v, 1) == MP_EQ`: the `mp_add` loop on `D` starts. -/
theorem Done.ok (h : Done a b v D) (hq : cmpD v 1 = .eq) : NA (Ok a b) b D (Rf a b).D (Rf a b).D := by
  have := (xfer_cmpDeq h.v.acct (by decide)).1 hq
  have := h.go.odd
  exact ⟨⟨h.go, by omega⟩, by omega, h.D, rfl⟩

/-- `D.sign == MP_NEG`: `mp_add(&D, b, &D)`. -/
theorem NA.addNeg {P : Prop} {X X1 : MpInt} {Z W : Int} (h : NA P b X Z W) (e : Env a b) (hn : X.sign = Layout.mpNeg)
    (hv : X1.Valid) (ha : X1.val = X.val + b.val) : NA P b X1 Z (W + b.mag) :=
  h.add e ((xfer_isNeg h.X.acct).1 hn) hv ha

theorem NA.exitNeg {P : Prop} {X : MpInt} {Z W : Int} (h : NA P b X Z W) (hn : ¬ X.sign = Layout.mpNeg) : NS P b X Z W :=
  h.exit (mt (xfer_isNeg h.X.acct).2 hn)

/-- The `mp_add` loop's measure: a step raises `W < 0` by `b > 0`. -/
theorem NA.meas {P : Prop} {X : MpInt} {Z W : Int} (h : NA P b X Z W) (hn : X.sign = Layout.mpNeg) :
    (-(W + b.mag)).toNat < (-W).toNat := by
  have := (xfer_isNeg h.X.acct).1 hn; have := h.pos; omega

/-- `mp_exch(&D, c)`, `c->sign = neg`: `InvmodFastPost`. -/
theorem fin_post {W : Int} (h : NS (Ok a b) b D (Rf a b).D W) (e : Env a b) (hc : cmpMag D b = .lt) : InvmodFastPost a b c (D.withSign a.sign) Layout.mpOkay := by
  obtain ⟨hn, -⟩ := h.fin e hc
  have hres : fastRes b.mag (invmodRem a b) = some W := by rw [h.aux.go.res, if_pos h.aux.v1, hn]
  have hv := h.X.valid
  have k : ∀ d, fastRes b.mag (invmodRem a b) = some d → d = W := fun d hd => by
    rw [hres] at hd; cases hd; rfl
  exact { err := fun hh => by rw [hres] at hh; cases hh
          ret_ok := fun _ _ => rfl
          shape := fun _ _ => { len := hv.len, used_le := hv.used_le, alloc_lt := hv.alloc_lt
                                digit_lt := hv.digit_lt, high_zero := hv.high_zero }
          top := fun _ _ hu => hv.top hu
          mag := fun d hd => by
            rw [k d hd]; show D.mag = W.toNat; rw [h.X.acct.mag]; have := h.nonneg; omega
          sign := fun _ _ => rfl }

/-! ## The code's tests and the loops' measures -/

/-- `MP_IS_EVEN(t)` as the code tests it: `used == 0`, or the low digit even. -/
theorem not_odd_of_used {t : MpInt} (h : t.used = 0) : ¬ isOdd t := fun ho => by have := ho.1; omega

theorem not_odd_of_dig {t : MpInt} (h : ¬ t.digit 0 % 2 = 1) : ¬ isOdd t := fun ho => h ho.2

theorem odd_of_dig {t : MpInt} (hu : t.used ≠ 0) (h : t.digit 0 % 2 = 1) : isOdd t := ⟨Nat.pos_of_ne_zero hu, h⟩

/-- A positive value's `used` is nonzero (the `beqz` the code takes for zero). -/
theorem used_ne_of_pos {t : MpInt} {n : Nat} (h : Gt t n) (hp : 0 < n) : t.used ≠ 0 := fun e => by
  have := (xfer_isZero h.acct).1 e; omega

theorem Loop.u_used {k : FastSt → FastSt} (h : Loop a b k x u v B D t) : u.used ≠ 0 := used_ne_of_pos h.u h.u_pos

theorem Loop.v_used {k : FastSt → FastSt} (h : Loop a b k x u v B D t) : v.used ≠ 0 := used_ne_of_pos h.v h.v_pos

theorem Loop.meas_halfU {k : FastSt → FastSt} (h : Loop a b k x u v B D t) (X : Nat) :
    (fastHalfU X t).u + (fastHalfU X t).v < t.u + t.v := by
  simp only [fastHalfU_u, fastHalfU_v]; have := h.u_pos; omega

theorem Loop.meas_halfV {k : FastSt → FastSt} (h : Loop a b k x u v B D t) (X : Nat) :
    (fastHalfV X t).u + (fastHalfV X t).v < t.u + t.v := by
  simp only [fastHalfV_u, fastHalfV_v]; have := h.v_pos; omega

theorem Loop.meas_sub {k : FastSt → FastSt} (h : Loop a b k x u v B D t) :
    (fastSub t).u + (fastSub t).v < t.u + t.v := sub_lt_meas h.u_pos h.v_pos

/-- `top:`'s first measure: `u + v = b + (a mod b) < 2 b`. -/
theorem init_meas (e : Env a b) (hb : isOdd b) :
    (fastInit b.mag (invmodRem a b)).u + (fastInit b.mag (invmodRem a b)).v < 2 * b.mag + 2 := by
  have := odd_of e.acct hb
  have h0 : 0 < b.mag := by omega
  have hr := invmodRem_cast (a := a) e.bz h0
  have : a.val % b.val < b.val := Int.emod_lt_of_pos _ (by rw [val_zpos e.bz]; omega)
  rw [val_zpos e.bz] at this hr
  show b.mag + invmodRem a b < _; omega

theorem Mid.v_ne {t : FastSt} (h : Mid a b x u v B D t) : 0 < t.u + t.v := by have := h.v_pos; omega

/-- `mp_cmp_mag(&X, b)` as the code's word: `compare |X| |b|`. -/
theorem NS.subM {P : Prop} {X X1 : MpInt} {Z W : Int} (h : NS P b X Z W) (e : Env a b) (hc : ¬ X.mag < b.mag)
    (hv : X1.Valid) (hs : X1.val = X.val - b.val) : NS P b X1 Z (W - b.mag) :=
  h.sub e (fun hh => hc (by rw [cmpMag_eq h.X.valid e.vb] at hh; exact Nat.compare_eq_lt.1 hh)) hv hs

theorem NS.measM {P : Prop} {X : MpInt} {Z W : Int} (h : NS P b X Z W) (e : Env a b) (hc : ¬ X.mag < b.mag) :
    (W - b.mag).toNat < W.toNat :=
  h.meas e (fun hh => hc (by rw [cmpMag_eq h.X.valid e.vb] at hh; exact Nat.compare_eq_lt.1 hh))

theorem fin_postM {W : Int} (h : NS (Ok a b) b D (Rf a b).D W) (e : Env a b) (hc : D.mag < b.mag) :
    InvmodFastPost a b c (D.withSign a.sign) Layout.mpOkay :=
  fin_post h e (by rw [cmpMag_eq h.X.valid e.vb]; exact Nat.compare_eq_lt.2 hc)

end Tom.InvmodFastStep
