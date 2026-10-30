import Tom.Spec.InvmodFastStep

/-!
# `s_mp_invmod_slow`: the model steps over the Ledger

`bn_s_mp_invmod_slow.c` at `0x80003670` (checked against `experiments/disasm.txt`):
`b->sign == MP_NEG || MP_IS_ZERO(b)` → `MP_VAL`; `mp_init_multi(&x, &y, &u, &v, &A, &B, &C, &D)`
(structs at `sp+32 … sp+200`); `mp_mod(a, b, &x)`; `mp_copy(b, &y)`; `MP_IS_EVEN(&x) &&
MP_IS_EVEN(&y)` → `MP_VAL`; `mp_copy(&x, &u)`, `mp_copy(&y, &v)`, `mp_set(&A, 1)`, `mp_set(&D, 1)`;
`top:` the `u` loop (`0x800037e0`: `mp_div_2(&u, &u)`; `A` or `B` odd → `mp_add(&A, &y, &A)`,
`mp_sub(&B, &x, &B)`; `mp_div_2(&A, &A)`, `mp_div_2(&B, &B)`), the `v` loop (`0x800038ec`, the same
on `v`, `C`, `D`), `mp_cmp(&u, &v)` and three in-place `mp_sub`s, `u ≠ 0` → `top` (`0x800039bc`);
`mp_cmp_d(&v, 1) != MP_EQ` → `MP_VAL`; `while (mp_cmp_d(&C, 0) == MP_LT) mp_add(&C, b, &C)`;
`while (mp_cmp_mag(&C, b) != MP_LT) mp_sub(&C, b, &C)`; `mp_exch(&C, c)`; `mp_clear_multi`.

As `InvmodFastStep` (its `Tmp`, `Env`, `NA`/`NS` are reused), with the model `SlowSt` and the
invariant `SlowInv` (HAC 14.61) carried at every cut: the C's `mp_div_2` truncates toward zero
and the model halves by `Int` `/`, which agree because `A + y`, `B - x` are even after the
fix-up (`par_odd` from `A x + B y = u`, `u` even), so the invariant is needed for exactness.

Assumptions beyond the C: `Env` (b positive; every `mp_copy` grows its temporary), `b` even at the loop entry.
The in-place `mp_add`/`mp_sub` may grow their temporary: `u`, `v`, `A`–`D` are `Gt` accounts and each
step takes the growing callee's result (`valid`, the value). Callee Posts as in
`InvmodFastStep`; `mp_cmp_d(&C, 0)` by `xfer_cmpD0`.
-/

namespace Tom.InvmodSlowStep

open MpInt Ledger Gcd InvmodFastStep

variable {a b c x y u v A B C D u1 v1 A1 A2 B1 B2 C1 C2 D1 D2 : MpInt} {t : SlowSt}

/-- The model's final state (`slowTop` from `u = a mod b`, `v = b`, `A = D = 1`, `B = C = 0`). -/
abbrev Rs (a b : MpInt) : SlowSt := slowTop (invmodRem a b) b.mag (slowInit (invmodRem a b) b.mag)

/-- An `MP_VAL` exit leaves `c`. -/
theorem err_post (h : slowRes (invmodRem a b) b.mag = none) : InvmodSlowPost a b c c Layout.mpVal := by
  have k : ∀ d, slowRes (invmodRem a b) b.mag ≠ some d := fun d hd => by rw [h] at hd; cases hd
  exact ⟨fun _ => ⟨rfl, rfl⟩, fun d hd => absurd hd (k d), fun d hd => absurd hd (k d), fun d hd => absurd hd (k d)⟩

theorem Env.notNeg (e : Env a b) : ¬ b.sign = Layout.mpNeg := by rw [e.bz]; decide

/-- `MP_IS_ZERO(b)`: `MP_VAL` (the model agrees: `v = 0` is never `1`). -/
theorem zero_exit (hz : b.used = 0) : InvmodSlowPost a b c c Layout.mpVal := by
  refine err_post ?_
  rw [MpInt.mag_used_zero hz]
  unfold slowRes
  split
  · rfl
  · have hv : (slowTop (invmodRem a b) 0 (slowInit (invmodRem a b) 0)).v = 0 := by
      rw [slowTop, dif_neg (by simp [slowInit])]
      exact Nat.le_zero.1 (slowPass_le (invmodRem a b) 0 (slowInit (invmodRem a b) 0)).2
    rw [if_neg (by rw [hv]; decide)]

/-- After `mp_init_multi`, `mp_mod(a, b, &x)`, `mp_copy(b, &y)`. -/
structure XY (a b x y : MpInt) : Prop where
  pos : 0 < b.mag
  x : Acct x 0 b.used (invmodRem a b) True
  y : Acct y 0 b.used b.mag True

theorem xy_of (e : Env a b) (hb0 : ¬ b.used = 0) (hx : ModPost a b x) (hy : CopyPost b (copyIn b (MpInt.zeroN defPrec)) y) :
    XY a b x y where
  pos := e.vb.mag_pos (by omega)
  x := by
    have h := xfer_modA e.va e.vb e.bz (by omega) hx
    have := e.vb.mag_pos (by omega)
    exact ⟨h.valid, h.room, h.used, by rw [h.val, invmodRem_cast e.bz this], trivial⟩
  y := copyG e.acct zeroS hy

/-- `MP_IS_EVEN(&x) && MP_IS_EVEN(&y)`: `MP_VAL`. -/
theorem XY.even (h : XY a b x y) (he : ¬ isOdd x ∧ ¬ isOdd y) : InvmodSlowPost a b c c Layout.mpVal := by
  have h1 := even_of h.x he.1; have h2 := even_of h.y he.2
  exact err_post (by unfold slowRes; rw [if_pos (by omega)])

/-! ## The loop -/

def kSub (X Y : Nat) (p : SlowSt) : SlowSt := if p.u = 0 then p else slowTop X Y p
def kV (X Y : Nat) (t : SlowSt) : SlowSt := kSub X Y (slowSub (slowLoopV X Y t))
def kU (X Y : Nat) (t : SlowSt) : SlowSt := kV X Y (slowLoopU X Y t)

theorem kU_top {X Y : Nat} (hu : 0 < t.u) (hv : 0 < t.v) : kU X Y t = slowTop X Y t := by
  rw [slowTop_eq X Y t hu hv]; rfl

theorem loopU_half {X Y : Nat} (h0 : 0 < t.u) (he : t.u % 2 = 0) :
    slowLoopU X Y t = slowLoopU X Y (slowHalfU X Y t) := by
  rw [slowLoopU, dif_pos ⟨by omega, he⟩]

theorem loopU_odd {X Y : Nat} (ho : t.u % 2 = 1) : slowLoopU X Y t = t := by rw [slowLoopU, dif_neg (by omega)]

theorem loopV_half {X Y : Nat} (h0 : 0 < t.v) (he : t.v % 2 = 0) :
    slowLoopV X Y t = slowLoopV X Y (slowHalfV X Y t) := by
  rw [slowLoopV, dif_pos ⟨by omega, he⟩]

theorem loopV_odd {X Y : Nat} (ho : t.v % 2 = 1) : slowLoopV X Y t = t := by rw [slowLoopV, dif_neg (by omega)]

/-- A loop cut: the temporaries hold `t`, positive, the invariant, and `k t` is the final state. -/
structure Loop (a b : MpInt) (k : SlowSt → SlowSt) (x y u v A B C D : MpInt) (t : SlowSt) : Prop where
  pos : 0 < b.mag
  x : Acct x 0 b.used (invmodRem a b) True
  y : Acct y 0 b.used b.mag True
  u : Gt u t.u
  v : Gt v t.v
  A : Gt A t.A
  B : Gt B t.B
  C : Gt C t.C
  D : Gt D t.D
  u_pos : 0 < t.u
  v_pos : 0 < t.v
  inv : SlowInv (invmodRem a b) b.mag t
  run : k t = Rs a b

/-- `mp_copy(&x, &u)`, `mp_copy(&y, &v)`, `mp_set(&A, 1)`, `mp_set(&D, 1)`: `top:` at `slowInit`
(`b` even, so `x` is odd). -/
theorem XY.init (h : XY a b x y) (hev : b.mag % 2 = 0) (hp : ¬ (¬ isOdd x ∧ ¬ isOdd y))
    (hu : CopyPost x (copyIn x (MpInt.zeroN defPrec)) u) (hv : CopyPost y (copyIn y (MpInt.zeroN defPrec)) v)
    (hA : SetPost (MpInt.zeroN defPrec) (1 % radix) A) (hD : SetPost (MpInt.zeroN defPrec) (1 % radix) D) :
    Loop a b (kU (invmodRem a b) b.mag) x y u v A (MpInt.zeroN defPrec) (MpInt.zeroN defPrec) D
      (slowInit (invmodRem a b) b.mag) := by
  have hx : invmodRem a b % 2 = 1 := by
    by_cases ho : isOdd x
    · have := odd_of h.x ho; omega
    · have := odd_of h.y (Classical.byContradiction fun hy => hp ⟨ho, hy⟩); omega
  have hy0 := h.pos
  exact { pos := hy0, x := h.x, y := h.y, u := Gt.of (copyG h.x zeroS hu), v := Gt.of (copyG h.y zeroS hv)
          A := (Tmp.set1 hA).gt, B := tmp_zero.gt, C := tmp_zero.gt, D := (Tmp.set1 hD).gt, u_pos := by show 0 < invmodRem a b; omega
          v_pos := hy0, inv := slowInit_inv (Or.inl hx), run := kU_top (by show 0 < invmodRem a b; omega) hy0 }

/-- `u` even, `A` or `B` odd: `mp_div_2(&u, &u)`, `mp_add(&A, &y, &A)`, `mp_sub(&B, &x, &B)`,
`mp_div_2(&A, &A)`, `mp_div_2(&B, &B)`. -/
theorem Loop.halfU_odd (h : Loop a b (kU (invmodRem a b) b.mag) x y u v A B C D t) (he : ¬ isOdd u)
    (hu : Div2Post u u u1) (ho : isOdd A ∨ isOdd B)
    (hv1 : A1.Valid) (ha : A1.val = A.val + y.val) (hv2 : B1.Valid) (hs : B1.val = B.val - x.val)
    (hA : Div2Post A1 A1 A2) (hB : Div2Post B1 B1 B2) :
    Loop a b (kU (invmodRem a b) b.mag) x y u1 v A2 B2 C D (slowHalfU (invmodRem a b) b.mag t) := by
  have hue := even_of h.u.acct he
  have hod : t.A % 2 = 1 ∨ t.B % 2 = 1 := ho.imp (odd_of h.A.acct) (odd_of h.B.acct)
  have hpar := par_odd t.A t.B (invmodRem a b) b.mag (by rw [h.inv.eu]; omega) (by have := h.inv.par; omega) hod
  have hinv := h.inv.halfU (by omega)
  have hrun : kU (invmodRem a b) b.mag (slowHalfU (invmodRem a b) b.mag t) = Rs a b := by
    unfold kU; rw [← loopU_half h.u_pos (by omega)]; exact h.run
  have e : slowHalfU (invmodRem a b) b.mag t =
      { t with u := t.u / 2, A := (t.A + b.mag) / 2, B := (t.B - invmodRem a b) / 2 } := by
    unfold slowHalfU; rw [if_pos hod]
  have := h.u_pos
  rw [e] at hinv hrun ⊢
  exact { h with
            u := h.u.halfN hu, A := (Gt.add h.A h.y hv1 ha).half hpar.1 hA,
            B := (Gt.sub h.B h.x hv2 hs).half hpar.2 hB, u_pos := (by show 0 < t.u / 2; omega), inv := hinv, run := hrun }

/-- `u` even, `A` and `B` even: `mp_div_2(&u, &u)`, `mp_div_2(&A, &A)`, `mp_div_2(&B, &B)`. -/
theorem Loop.halfU_even (h : Loop a b (kU (invmodRem a b) b.mag) x y u v A B C D t) (he : ¬ isOdd u)
    (hu : Div2Post u u u1) (hAe : ¬ isOdd A) (hBe : ¬ isOdd B) (hA : Div2Post A A A2) (hB : Div2Post B B B2) :
    Loop a b (kU (invmodRem a b) b.mag) x y u1 v A2 B2 C D (slowHalfU (invmodRem a b) b.mag t) := by
  have hue := even_of h.u.acct he
  have h1 := even_of h.A.acct hAe; have h2 := even_of h.B.acct hBe
  have hinv := h.inv.halfU (by omega)
  have hrun : kU (invmodRem a b) b.mag (slowHalfU (invmodRem a b) b.mag t) = Rs a b := by
    unfold kU; rw [← loopU_half h.u_pos (by omega)]; exact h.run
  have e : slowHalfU (invmodRem a b) b.mag t = { t with u := t.u / 2, A := t.A / 2, B := t.B / 2 } := by
    unfold slowHalfU; rw [if_neg (by omega)]
  have := h.u_pos
  rw [e] at hinv hrun ⊢
  exact { h with
            u := h.u.halfN hu, A := h.A.half h1 hA, B := h.B.half h2 hB, u_pos := (by show 0 < t.u / 2; omega),
            inv := hinv, run := hrun }

/-- `u` odd: the `u` loop exits to the `v` loop. -/
theorem Loop.exitU (h : Loop a b (kU (invmodRem a b) b.mag) x y u v A B C D t) (ho : isOdd u) :
    Loop a b (kV (invmodRem a b) b.mag) x y u v A B C D t :=
  { h with run := by have := h.run; unfold kU at this; rwa [loopU_odd (by have := odd_of h.u.acct ho; omega)] at this }

/-- `v` even, `C` or `D` odd: `mp_div_2(&v, &v)`, `mp_add(&C, &y, &C)`, `mp_sub(&D, &x, &D)`,
`mp_div_2(&C, &C)`, `mp_div_2(&D, &D)`. -/
theorem Loop.halfV_odd (h : Loop a b (kV (invmodRem a b) b.mag) x y u v A B C D t) (he : ¬ isOdd v)
    (hv : Div2Post v v v1) (ho : isOdd C ∨ isOdd D)
    (hv1 : C1.Valid) (ha : C1.val = C.val + y.val) (hv2 : D1.Valid) (hs : D1.val = D.val - x.val)
    (hC : Div2Post C1 C1 C2) (hD : Div2Post D1 D1 D2) :
    Loop a b (kV (invmodRem a b) b.mag) x y u v1 A B C2 D2 (slowHalfV (invmodRem a b) b.mag t) := by
  have hve := even_of h.v.acct he
  have hod : t.C % 2 = 1 ∨ t.D % 2 = 1 := ho.imp (odd_of h.C.acct) (odd_of h.D.acct)
  have hpar := par_odd t.C t.D (invmodRem a b) b.mag (by rw [h.inv.ev]; omega) (by have := h.inv.par; omega) hod
  have hinv := h.inv.halfV (by omega)
  have hrun : kV (invmodRem a b) b.mag (slowHalfV (invmodRem a b) b.mag t) = Rs a b := by
    unfold kV; rw [← loopV_half h.v_pos (by omega)]; exact h.run
  have e : slowHalfV (invmodRem a b) b.mag t =
      { t with v := t.v / 2, C := (t.C + b.mag) / 2, D := (t.D - invmodRem a b) / 2 } := by
    unfold slowHalfV; rw [if_pos hod]
  have := h.v_pos
  rw [e] at hinv hrun ⊢
  exact { h with
            v := h.v.halfN hv, C := (Gt.add h.C h.y hv1 ha).half hpar.1 hC,
            D := (Gt.sub h.D h.x hv2 hs).half hpar.2 hD, v_pos := (by show 0 < t.v / 2; omega), inv := hinv, run := hrun }

/-- `v` even, `C` and `D` even: `mp_div_2(&v, &v)`, `mp_div_2(&C, &C)`, `mp_div_2(&D, &D)`. -/
theorem Loop.halfV_even (h : Loop a b (kV (invmodRem a b) b.mag) x y u v A B C D t) (he : ¬ isOdd v)
    (hv : Div2Post v v v1) (hCe : ¬ isOdd C) (hDe : ¬ isOdd D) (hC : Div2Post C C C2) (hD : Div2Post D D D2) :
    Loop a b (kV (invmodRem a b) b.mag) x y u v1 A B C2 D2 (slowHalfV (invmodRem a b) b.mag t) := by
  have hve := even_of h.v.acct he
  have h1 := even_of h.C.acct hCe; have h2 := even_of h.D.acct hDe
  have hinv := h.inv.halfV (by omega)
  have hrun : kV (invmodRem a b) b.mag (slowHalfV (invmodRem a b) b.mag t) = Rs a b := by
    unfold kV; rw [← loopV_half h.v_pos (by omega)]; exact h.run
  have e : slowHalfV (invmodRem a b) b.mag t = { t with v := t.v / 2, C := t.C / 2, D := t.D / 2 } := by
    unfold slowHalfV; rw [if_neg (by omega)]
  have := h.v_pos
  rw [e] at hinv hrun ⊢
  exact { h with
            v := h.v.halfN hv, C := h.C.half h1 hC, D := h.D.half h2 hD, v_pos := (by show 0 < t.v / 2; omega),
            inv := hinv, run := hrun }

/-- After the subtraction (`u` may be zero). -/
structure Mid (a b : MpInt) (x y u v A B C D : MpInt) (t : SlowSt) : Prop where
  pos : 0 < b.mag
  x : Acct x 0 b.used (invmodRem a b) True
  y : Acct y 0 b.used b.mag True
  u : Gt u t.u
  v : Gt v t.v
  A : Gt A t.A
  B : Gt B t.B
  C : Gt C t.C
  D : Gt D t.D
  v_pos : 0 < t.v
  inv : SlowInv (invmodRem a b) b.mag t
  run : kSub (invmodRem a b) b.mag t = Rs a b

theorem Loop.run_sub (h : Loop a b (kV (invmodRem a b) b.mag) x y u v A B C D t) (ho : isOdd v) :
    kSub (invmodRem a b) b.mag (slowSub t) = Rs a b := by
  have := h.run; unfold kV at this; rwa [loopV_odd (by have := odd_of h.v.acct ho; omega)] at this

/-- `v` odd, `mp_cmp(&u, &v) != MP_LT`: `mp_sub(&u, &v, &u)`, `mp_sub(&A, &C, &A)`, `mp_sub(&B, &D, &B)`. -/
theorem Loop.sub_ge (h : Loop a b (kV (invmodRem a b) b.mag) x y u v A B C D t) (ho : isOdd v)
    (hc : ¬ cmpS u v = .lt) (hv1 : u1.Valid) (hs1 : u1.val = u.val - v.val)
    (hv2 : A1.Valid) (hs2 : A1.val = A.val - C.val) (hv3 : B1.Valid) (hs3 : B1.val = B.val - D.val) :
    Mid a b x y u1 v A1 B1 C D (slowSub t) := by
  have hle : t.v ≤ t.u := by have := mt (xfer_cmp h.u.acct h.v.valid h.v.val).2 hc; omega
  have hrun := h.run_sub ho
  have hinv := h.inv.sub
  have e : slowSub t = { t with u := t.u - t.v, A := t.A - t.C, B := t.B - t.D } := by
    unfold slowSub; rw [if_pos hle]
  rw [e] at hrun hinv ⊢
  exact { pos := h.pos, x := h.x, y := h.y, v := h.v, C := h.C, D := h.D, v_pos := h.v_pos, inv := hinv, run := hrun
          A := Gt.sub h.A h.C.acct hv2 hs2, B := Gt.sub h.B h.D.acct hv3 hs3
          u := by show Gt u1 ((t.u - t.v : Nat) : Int); rw [Int.ofNat_sub hle]; exact Gt.sub h.u h.v.acct hv1 hs1 }

/-- `v` odd, `mp_cmp(&u, &v) == MP_LT`: `mp_sub(&v, &u, &v)`, `mp_sub(&C, &A, &C)`, `mp_sub(&D, &B, &D)`. -/
theorem Loop.sub_lt (h : Loop a b (kV (invmodRem a b) b.mag) x y u v A B C D t) (ho : isOdd v)
    (hc : cmpS u v = .lt) (hv1 : v1.Valid) (hs1 : v1.val = v.val - u.val)
    (hv2 : C1.Valid) (hs2 : C1.val = C.val - A.val) (hv3 : D1.Valid) (hs3 : D1.val = D.val - B.val) :
    Mid a b x y u v1 A B C1 D1 (slowSub t) := by
  have hlt : t.u < t.v := by have := (xfer_cmp h.u.acct h.v.valid h.v.val).1 hc; omega
  have hrun := h.run_sub ho
  have hinv := h.inv.sub
  have e : slowSub t = { t with v := t.v - t.u, C := t.C - t.A, D := t.D - t.B } := by
    unfold slowSub; rw [if_neg (by omega)]
  rw [e] at hrun hinv ⊢
  exact { pos := h.pos, x := h.x, y := h.y, u := h.u, A := h.A, B := h.B, inv := hinv, run := hrun
          C := Gt.sub h.C h.A.acct hv2 hs2, D := Gt.sub h.D h.B.acct hv3 hs3
          v := by show Gt v1 ((t.v - t.u : Nat) : Int); rw [Int.ofNat_sub (by omega)]; exact Gt.sub h.v h.u.acct hv1 hs1
          v_pos := by show 0 < t.v - t.u; omega }

/-- The measure of the outer loop. -/
theorem sub_lt_meas (hu : 0 < t.u) (hv : 0 < t.v) : (slowSub t).u + (slowSub t).v < t.u + t.v := by
  unfold slowSub; split <;> simp only <;> omega

/-- `!MP_IS_ZERO(&u)`: `goto top`. -/
theorem Mid.top (h : Mid a b x y u v A B C D t) (hz : ¬ u.used = 0) :
    Loop a b (kU (invmodRem a b) b.mag) x y u v A B C D t := by
  have hu : 0 < t.u := by have := mt (xfer_isZero h.u.acct).2 hz; omega
  exact { h with u_pos := hu, run := by rw [kU_top hu h.v_pos, ← h.run, kSub, if_neg (by omega)] }

/-- The loop's exit (`u = 0`): `v`, `C` hold the model's final state. -/
structure Done (a b v C : MpInt) : Prop where
  par : ¬ (invmodRem a b % 2 = 0 ∧ b.mag % 2 = 0)
  pos : 0 < b.mag
  v : Gt v (Rs a b).v
  C : Gt C (Rs a b).C

theorem Mid.done (h : Mid a b x y u v A B C D t) (hz : u.used = 0) : Done a b v C := by
  have hu : t.u = 0 := by have := (xfer_isZero h.u.acct).1 hz; omega
  have hpar := h.inv.par
  have hpos := h.pos
  have e : t = Rs a b := by rw [← h.run, kSub, if_pos hu]
  subst e
  exact ⟨by have := hpar; omega, hpos, h.v, h.C⟩

theorem Done.res (hp : ¬ (invmodRem a b % 2 = 0 ∧ b.mag % 2 = 0)) :
    slowRes (invmodRem a b) b.mag = if (Rs a b).v = 1 then some (norm b.mag (Rs a b).C) else none := by
  unfold slowRes; rw [if_neg hp]

/-- `mp_cmp_d(&v, 1) != MP_EQ`: no inverse. -/
theorem Done.bad (h : Done a b v C) (hne : ¬ cmpD v 1 = .eq) : InvmodSlowPost a b c c Layout.mpVal := by
  have := mt (xfer_cmpDeq h.v.acct (by decide)).2 hne
  exact err_post (by rw [Done.res h.par, if_neg (show ¬ (Rs a b).v = 1 by omega)])

/-- Past `mp_cmp_d(&v, 1) == MP_EQ`. -/
structure Ok (a b : MpInt) : Prop where
  par : ¬ (invmodRem a b % 2 = 0 ∧ b.mag % 2 = 0)
  v1 : (Rs a b).v = 1

/-- `mp_cmp_d(&v, 1) == MP_EQ`: the `mp_add` loop on `C` starts. -/
theorem Done.ok (h : Done a b v C) (hq : cmpD v 1 = .eq) : NA (Ok a b) b C (Rs a b).C (Rs a b).C := by
  have := (xfer_cmpDeq h.v.acct (by decide)).1 hq
  exact ⟨⟨h.par, by omega⟩, h.pos, h.C, rfl⟩

/-- `mp_cmp_d(&C, 0) == MP_LT`: `mp_add(&C, b, &C)`. -/
theorem NA.addD {P : Prop} {X X1 : MpInt} {Z W : Int} (h : NA P b X Z W) (e : Env a b) (hn : cmpD X 0 = .lt)
    (hv : X1.Valid) (ha : X1.val = X.val + b.val) : NA P b X1 Z (W + b.mag) :=
  h.add e ((xfer_cmpD0 h.X.acct).1 hn) hv ha

theorem NA.exitD {P : Prop} {X : MpInt} {Z W : Int} (h : NA P b X Z W) (hn : ¬ cmpD X 0 = .lt) : NS P b X Z W :=
  h.exit (mt (xfer_cmpD0 h.X.acct).2 hn)

/-- The `mp_add` loop's measure. -/
theorem NA.measD {P : Prop} {X : MpInt} {Z W : Int} (h : NA P b X Z W) (hn : cmpD X 0 = .lt) :
    (-(W + b.mag)).toNat < (-W).toNat := by
  have := (xfer_cmpD0 h.X.acct).1 hn; have := h.pos; omega

/-- `mp_exch(&C, c)`: `InvmodSlowPost`. -/
theorem fin_post {W : Int} (h : NS (Ok a b) b C (Rs a b).C W) (e : Env a b) (hc : cmpMag C b = .lt) :
    InvmodSlowPost a b c C Layout.mpOkay := by
  obtain ⟨hn, -⟩ := h.fin e hc
  have hres : slowRes (invmodRem a b) b.mag = some W := by
    rw [Done.res h.aux.par, if_pos h.aux.v1, hn]
  have k : ∀ d, slowRes (invmodRem a b) b.mag = some d → d = W := fun d hd => by
    rw [hres] at hd; cases hd; rfl
  exact { err := fun hh => by rw [hres] at hh; cases hh
          ret_ok := fun _ _ => rfl
          valid := fun _ _ => h.X.valid
          val := fun d hd => by rw [k d hd]; exact h.X.val }

/-! ## The code's tests and the loops' measures -/

theorem Loop.u_used {k : SlowSt → SlowSt} (h : Loop a b k x y u v A B C D t) : u.used ≠ 0 :=
  used_ne_of_pos h.u h.u_pos

theorem Loop.v_used {k : SlowSt → SlowSt} (h : Loop a b k x y u v A B C D t) : v.used ≠ 0 :=
  used_ne_of_pos h.v h.v_pos

theorem Loop.meas_halfU {k : SlowSt → SlowSt} (h : Loop a b k x y u v A B C D t) (X Y : Nat) :
    (slowHalfU X Y t).u + (slowHalfU X Y t).v < t.u + t.v := by
  simp only [slowHalfU_u, slowHalfU_v]; have := h.u_pos; omega

theorem Loop.meas_halfV {k : SlowSt → SlowSt} (h : Loop a b k x y u v A B C D t) (X Y : Nat) :
    (slowHalfV X Y t).u + (slowHalfV X Y t).v < t.u + t.v := by
  simp only [slowHalfV_u, slowHalfV_v]; have := h.v_pos; omega

theorem Loop.meas_sub {k : SlowSt → SlowSt} (h : Loop a b k x y u v A B C D t) :
    (slowSub t).u + (slowSub t).v < t.u + t.v := sub_lt_meas h.u_pos h.v_pos

/-- `top:`'s first measure: `u + v = (a mod b) + b < 2 b`. -/
theorem init_meas (e : Env a b) (h : XY a b x y) :
    (slowInit (invmodRem a b) b.mag).u + (slowInit (invmodRem a b) b.mag).v < 2 * b.mag + 2 := by
  have h0 := h.pos
  have hr := invmodRem_cast (a := a) e.bz h0
  have : a.val % b.val < b.val := Int.emod_lt_of_pos _ (by rw [val_zpos e.bz]; omega)
  rw [val_zpos e.bz] at this hr
  show invmodRem a b + b.mag < _; omega

/-- `mp_cmp_mag(&C, b) == MP_LT` as the code's word, then `mp_exch(&C, c)`. -/
theorem fin_postM {W : Int} (h : NS (Ok a b) b C (Rs a b).C W) (e : Env a b) (hc : C.mag < b.mag) :
    InvmodSlowPost a b c C Layout.mpOkay :=
  fin_post h e (by rw [cmpMag_eq h.X.valid e.vb]; exact Nat.compare_eq_lt.2 hc)

end Tom.InvmodSlowStep
