import Tom.Machine.Api.Std
import Tom.Machine.Api.StdHeapFn
import Tom.Machine.Api.CntLsb
import Tom.Machine.Api.MpDiv2d
import Tom.Machine.Api.MpMul2d
import Tom.Machine.Api.MpAbs
import Tom.Machine.Fn.CntLsbMain
import Tom.Machine.Fn.MpDiv2dMain
import Tom.Machine.Fn.MpMul2dMainG5
import Tom.Machine.Fn.MpAbsMain
import Tom.Machine.Kit.W64

/-!
# The callee contracts (for `mp_gcd`)

* `cntLsbG`: `mp_cnt_lsb(a)` (`Api/CntLsb.lean`): `a0 = cntLsb a`, nothing written.
* `div2dG`: `mp_div_2d(a, b, a, NULL)` in place (`Api/MpDiv2d.lean` `StatementInPlace`).
* `mul2dG`: `mp_mul_2d(a, b, c)`, distinct operands, with room (`Api/MpMul2d.lean`).
* `cmpMagG`: `mp_cmp_mag(a, b)` (`Std.cmpMag`) with the result pinned as a `Nat` (`ordNG`).
* `mpAbsG`: `mp_abs(a, b)`, distinct operands (`Api/MpAbs.lean`; `mp_gcd` tail-calls it).
* `mpInitCopyG`: `mp_init_copy(a, b)` as `Std.mpInitCopy`, but on `MP_MEM` the
  struct keeps the one fact the caller needs: `a->dp == NULL`, as the kind of a
  two-digit zero array at `a + 16` (`MpInitCopy.Post.mem`'s `dp`).
* `mpClearNullG`: `mp_clear(a)` of a struct with `a->dp == NULL` (`MpClear.NullStatement`):
  nothing written. `mp_gcd`'s `LBL_U` clears the `v` whose `mp_init_copy` failed.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-! ## `mp_cnt_lsb(a)` -/

structure LsbResG (p : ObP) : Prop where
  va : p.a.Valid
  bits : Layout.digitBits * p.a.used < 2 ^ 31

def cntLsbG : Contract where
  P := ObP
  X := Unit
  R := Ob
  all := [.S, .D, .code]
  hall := Ob.all
  entry := CntLsb.entry
  args p := [(10, BitVec.ofNat 64 p.p)]
  rets p ra := [(1, ra), (10, BitVec.ofNat 64 (cntLsb p.a))]
  lay p := Ob.lay p.p p.dp p.a.alloc
  kind := fun ⟨p, dp, a⟩ => Ob.kind p dp a
  out := fun ⟨p, dp, a⟩ _ => Ob.kind p dp a
  isW _ := false
  ws := []
  Res := LsbResG
  Q _ _ := True
  fits p r := by cases p; cases r <;> exact Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qp, qdp, qa⟩ := p
    have hpre : CntLsb.Pre m qp qdp qa ra :=
      { ra_ := Hdr.mpAt (hB .S).2 (hB .D).2, va := hres.va, ga := Hdr.geom (hB .S).2, bits := hres.bits
        ra_al := hra, img := (hB .code).2 }
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩) (Fn.CntLsb.correct hpre)

/-! ## `mp_div_2d(a, b, a, NULL)` -/

structure D2PG where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  b : Nat

structure D2ResG (p : D2PG) : Prop where
  va : p.a.Valid
  b_lt : p.b < 2 ^ 31
  sp_al : p.sp % 16 = 0
  sp_ge : 96 ≤ p.sp

def div2dG : Contract where
  P := D2PG
  X := MpInt
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := MpDiv2d.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.b),
    (12, BitVec.ofNat 64 p.pa), (13, 0#64)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Un.lay 96 p.sp p.pa p.adp p.a
  kind := fun ⟨_, pa, adp, a, _⟩ => Tom.Machine.Un.kind pa adp a
  out := fun ⟨_, pa, adp, _, _⟩ x => Tom.Machine.Un.kind pa adp x
  isW := Un.isW
  ws := Un.ws
  Res := D2ResG
  Q p x := Div2dPost p.a p.b p.a x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MpDiv2d.PreI m qsp qpa qadp qa qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, va := hres.va, ga := Hdr.geom (hB .aS).2, b_lt := hres.b_lt
        rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge, ra_al := hra
        img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.MpDiv2d.correct_inplace (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, hpost.div, ?_, hpost.frame⟩
    have hal : a'.alloc = qa.alloc := (show ClampedTo a' qa.alloc _ _ _ from hpost.div).alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Un.R.code

/-! ## `mp_mul_2d(a, b, c)` -/

structure M2PG where
  sp : Nat
  pa : Nat
  adp : Nat
  pc : Nat
  cdp : Nat
  a : MpInt
  b : Nat
  c : MpInt

structure M2ResG (p : M2PG) : Prop where
  va : p.a.Valid
  sc : p.c.Shape
  b_lt : p.b < 2 ^ 31
  room : p.a.used + p.b / Layout.digitBits + 1 ≤ p.c.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 80 ≤ p.sp

def mul2dG : Contract where
  P := M2PG
  X := MpInt
  R := Two.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Two.all
  entry := MpMul2d.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.b),
    (12, BitVec.ofNat 64 p.pc)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Two.lay 80 p.sp p.pa p.adp p.pc p.cdp p.a p.c
  kind := fun ⟨_, pa, adp, pc, cdp, a, _, c⟩ => Tom.Machine.Two.kind pa adp pc cdp a c
  out := fun ⟨_, pa, adp, pc, cdp, a, _, _⟩ x => Tom.Machine.Two.kind pa adp pc cdp a x
  isW := Two.isW
  ws := Two.ws
  Res := M2ResG
  Q p x := Mul2dPost p.a p.b p.c x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpc, qcdp, qa, qb, qc⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MpMul2d.Pre m qsp qpa qadp qpc qcdp qa qb qc ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rc := Hdr.mpAt (hB .bS).2 (hB .bD).2
        va := hres.va, sc := hres.sc, ga := Hdr.geom (hB .aS).2, gc := Hdr.geom (hB .bS).2
        b_lt := hres.b_lt, room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge
        ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, b', M, hat, hpost⟩ :=
      Fn.MpMul2dG5.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, b', M, hat.sub rfl rfl, hpost.mul, ?_, hpost.frame⟩
    have hal : b'.alloc = qc.alloc := (show ClampedTo b' qc.alloc _ _ _ from hpost.mul).alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact hB.keep hS hpost.frame Two.R.aS
    · exact hB.keep hS hpost.frame Two.R.aD
    · exact witS hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Two.R.code

/-! ## `mp_abs(a, b)` -/

structure AbsResG (p : TwoP) : Prop where
  sa : p.a.Shape
  sb : p.b.Shape
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  room : p.a.used ≤ p.b.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 64 ≤ p.sp

def mpAbsG : Contract where
  P := TwoP
  X := MpInt
  R := Two.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Two.all
  entry := MpAbs.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Two.lay 64 p.sp p.pa p.adp p.pb p.bdp p.a p.b
  kind := fun ⟨_, pa, adp, pb, bdp, a, b⟩ => Tom.Machine.Two.kind pa adp pb bdp a b
  out := fun ⟨_, pa, adp, pb, bdp, a, _⟩ x => Tom.Machine.Two.kind pa adp pb bdp a x
  isW := Two.isW
  ws := Two.ws
  Res := AbsResG
  Q p x := AbsPost p.a p.b x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MpAbs.Pre m qsp qpa qadp qpb qbdp qa qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2
        sa := hres.sa, sb := hres.sb, asign := hres.asign, ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2
        room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge, ra_al := hra
        img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, b', M, hat, hpost⟩ :=
      Fn.MpAbs.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, b', M, hat.sub rfl rfl, hpost.abs, ?_, hpost.frame⟩
    have hal := hpost.abs.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact hB.keep hS hpost.frame Two.R.aS
    · exact hB.keep hS hpost.frame Two.R.aD
    · exact witS hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Two.R.code

/-! ## `mp_cmp_mag(a, b)` with its result as a `Nat` pin -/

/-- `ordCode` as the 64-bit pattern `a0` holds. -/
def ordNG : Ordering → Nat
  | .lt => 18446744073709551615
  | .eq => 0
  | .gt => 1

theorem ofInt_ordCodeG (o : Ordering) : BitVec.ofInt 64 (ordCode o) = BitVec.ofNat 64 (ordNG o) := by
  cases o <;> decide

theorem ordNG_lt (o : Ordering) : ordNG o < 2 ^ 64 := by cases o <;> decide

theorem ordNG_gt {o : Ordering} : ordNG o = 1 ↔ o = .gt := by cases o <;> decide

/-- `Std.cmpMag` with `a0 = BitVec.ofNat 64 (ordNG (compare |a| |b|))`. -/
def cmpMagG : Contract where
  P := CmP
  X := Unit
  R := Cm
  all := [.aS, .aD, .bS, .bD, .code]
  hall r := by cases r <;> simp
  entry := Fn.CmpMag.entry
  args p := [(10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]
  rets p ra := [(1, ra), (10, BitVec.ofNat 64 (ordNG (compare p.a.mag p.b.mag)))]
  lay := Cm.lay
  kind := Cm.kind
  out p _ := Cm.kind p
  isW _ := false
  ws := []
  Res p := p.a.Valid ∧ p.b.Valid
  Q _ _ := True
  fits p r := by cases r <;> exact Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    have h := Std.cmpMag.spec (p := p) (v := v) (outp := outp) hra hres hS hB
    simpa only [Std.cmpMag, ofInt_ordCodeG] using h

/-! ## `a->dp == NULL` as a kind -/

/-- A struct whose `dp` field is `NULL`: the field as two zero digits at `pa + 16`. -/
abbrev nullKG (pa : Nat) : Kind := .mpD (pa + 16) 2 (fun _ => 0)

theorem nullKG_wit {M : Mem} {pa : Nat} (hr : Ram pa 24) (hal : pa % 8 = 0) (hdp : bytesT8 M (pa + 16) = 0#64) :
    (nullKG pa).Fits ⟨pa, 24⟩ ∧ (nullKG pa).Wit ⟨pa, 24⟩ M := by
  refine ⟨show Iv.Sub ⟨pa + 16, 4 * 2⟩ ⟨pa, 24⟩ by simp only [Iv.Sub]; omega, ?_⟩
  refine ⟨⟨by have := hr.lo_ge; omega, by have := hr.hi_le; omega, by have := hr.off; omega⟩, by omega, ?_⟩
  intro j hj
  have h0 := bytesT4_lo M (pa + 16); have h1 := bytesT4_hi M (pa + 16)
  rw [hdp] at h0 h1
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · simpa using h0
  · simpa [Nat.add_assoc] using h1

theorem nullKG_dp {M : Mem} {pa : Nat} {I : Iv} (h : (nullKG pa).Wit I M) : bytesT8 M (pa + 16) = 0#64 := by
  have := bytesT8_of_halves (h.arr 0 (by decide)) (by simpa [Nat.add_assoc] using h.arr 1 (by decide))
    (by decide) (by decide)
  simpa using this

/-! ## `mp_clear(a)` with `a->dp == NULL` -/

inductive CnG | S | code
  deriving DecidableEq

structure CnPG where
  pa : Nat

def CnG.lay (pa : Nat) : CnG → Iv
  | .S => ⟨pa, 24⟩
  | .code => textIv

def CnG.kind (pa : Nat) : CnG → Kind
  | .S => nullKG pa
  | .code => .code

def mpClearNullG : Contract where
  P := CnPG
  X := Unit
  R := CnG
  all := [.S, .code]
  hall r := by cases r <;> simp
  entry := Fn.MpClear.entry
  args p := [(10, BitVec.ofNat 64 p.pa)]
  rets _ ra := [(1, ra)]
  lay p := CnG.lay p.pa
  kind p := CnG.kind p.pa
  out p _ := CnG.kind p.pa
  isW _ := false
  ws := []
  Res p := Ram p.pa 24
  Q _ _ := True
  fits p r := by cases r <;> first | exact Iv.sub_self _ | (show Iv.Sub ⟨p.pa + 16, 4 * 2⟩ ⟨p.pa, 24⟩; simp only [Iv.Sub]; omega)
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩)
      (Fn.MpClear.correct_null (v := v) (outp := outp) (nullKG_dp (hB .S).2) hres (hB .code).2 hra)

/-! ## `mp_init_copy(a, b)`, keeping `a->dp == NULL` on `MP_MEM` -/

def Ic.outG (p : IcP) : Option (Nat × MpInt) → Ic → Kind
  | none, .aS => nullKG p.pa
  | x, r => Ic.out p x r

def mpInitCopyG : HContract where
  P := IcP
  X := Option (Nat × MpInt)
  R := Ic
  all := [.stk, .aS, .bS, .bD, .site, .code]
  hall r := by cases r <;> simp
  entry := Fn.MpInitCopy.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]
  rets _ x ra := [(1, ra), (10, match x with | none => MpInit.memBV | some _ => 0#64)]
  lay := Ic.lay
  kind := Ic.kind
  out := Ic.outG
  isW := fun | .stk | .aS | .site => true | _ => false
  ws := [.stk, .aS, .site]
  site := .site
  site' := Ic.site'
  hin p := p.H
  hout := Ic.hout
  Res := IcRes
  Q := Ic.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    cases x <;> cases r <;> simp_all [Ic.outG, Ic.out, Ic.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    cases r with
    | stk => exact .inl (show 0 < MpInitCopy.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | bS => exact .inl (show 0 < 24 by decide)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.bpos; omega)
    | site => exact .inr (.inl (show 0x80000000 < heapStart by decide))
    | code => exact .inl (show 0 < textLen by decide)
  spec := by
    intro p m v outp ra hra hres hS hB hH _ c hc
    obtain ⟨sp, pa, pb, bdp, b, H⟩ := p
    have hst : StkRes sp MpInitCopy.F := hres.stk
    have hpa : pa % 8 = 0 := hres.pa_al
    have hso : OffHeap pa 24 := hres.soff
    have hbo : OffHeap pb 24 := hres.boff
    have hctx := hst.ctx hc rfl rfl (hB .code).2 hH.imp hra
    have hsub : ∀ r, (MpInitCopy.lay MpInitCopy.F sp pa pb bdp b r).Sub (Ic.lay ⟨sp, pa, pb, bdp, b, H⟩ (Ic.σ r)) := by
      intro r; cases r <;> exact Iv.sub_self _
    have gb := Hdr.geom (show Hdr m pb bdp b from (hB .bS).2)
    have hpre : MpInitCopy.Pre m v H sp pa pb bdp b ra :=
      { heap := hH.heap, st := (hB .aS).2, st_al := hpa, soff := hso
        live := ⟨Hdr.mpAt (hB .bS).2 (hB .bD).2, hres.blk, hbo⟩, vb := hres.vb, apos := hres.bpos, gb := gb
        ctx := ⟨hctx.img, hctx.impure, hctx.gp, hctx.sp_v, hctx.sp_al, hctx.sp_lo, hctx.sp_hi⟩
        ra_al := hra, lay := hS.pull Ic.σ [.stk, .aS, .bS, .bD, .code] MpInitCopy.all hsub (by decide) }
    obtain ⟨c', hs, r, M, hat, hpost⟩ := Fn.MpInitCopy.correct hpre c (hc.subL rfl)
    have hW : ∀ a, InAny (MpInitCopy.lay MpInitCopy.F sp pa pb bdp b) MpInitCopy.ws a →
        InAny (Ic.lay ⟨sp, pa, pb, bdp, b, H⟩) [Ic.stk, .aS, .site] a := fun a ha => by
      rcases ha with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact h.elim
    have himp : ∀ (M : Mem), HFrm (MpInitCopy.lay MpInitCopy.F sp pa pb bdp b) MpInitCopy.ws H m M →
        ImpureAt M := fun M hf =>
      ImpureAt.of_keep hf (fun a h1 h2 hw => hw.elim (fun hw => by
          rcases hw with h | h | h
          · exact offHeap_imp hst.off h.1 h.2 ⟨h1, h2⟩
          · exact offHeap_imp hso h.1 h.2 ⟨h1, h2⟩
          · exact h.elim) (impure_off_foot h1 h2)) hH.imp
    have hn : 0 < initPrec b.used := by unfold initPrec minPrec; simp only [Layout.digitBits]; omega
    cases hpost with
    | @ok q a' hf heap live copy frame =>
      have hal : a'.alloc = initPrec b.used := copy.alloc
      have hf' : Fresh H q (4 * a'.alloc) := by rw [hal]; exact hf
      have g := geom_fresh (show Ram pa 24 from (hB .aS).2) hpa hso hf' (by rw [hal]; exact hn)
      refine ⟨c', hs, some (q, a'), M, hat, ⟨hf, copy⟩, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | aS => exact ⟨Iv.sub_self _, Hdr.of_mpAt live.repr g⟩
                | site => exact absurd rfl hrs
                | _ => simp at hr
              wsite := ⟨Iv.sub_self _, Dig.of_mpAt live.repr g⟩
              place := .fresh hf' (by rw [hal]; omega)
              frame := Keep.mono frame fun a h => h.imp_left (hW a)
              heap := ⟨by show Heap M ((q, 4 * a'.alloc) :: H); rw [hal]; exact heap, himp M frame⟩
              foot := fun a ha => .inl (Foot.of_cons ha), off := off_blk hf' (by rw [hal]; omega) }
    | mem heap dp frame =>
      refine ⟨c', hs, none, M, hat, trivial, ?_⟩
      exact { wit := fun r hr hrs => by
                cases r with
                | stk => exact ⟨trivial, (hB .stk).2⟩
                | aS => exact nullKG_wit (hB .aS).2 hpa dp
                | site => exact absurd rfl hrs
                | _ => simp at hr
              wsite := ⟨trivial, Ram.nil⟩, place := .keep
              frame := Keep.mono frame fun a h => h.imp_left (hW a)
              heap := ⟨heap, himp M frame⟩, foot := fun a ha => .inl ha, off := Off.nil H }

end Tom.Machine.Std
