import Tom.Machine.Api.Std
import Tom.Machine.Api.CountBits
import Tom.Machine.Api.MpSet
import Tom.Machine.Api.Mul2
import Tom.Machine.Api.SSubAlias
import Tom.Machine.Fn.CountBitsMain
import Tom.Machine.Fn.MpSetMain
import Tom.Machine.Fn.Mul2InPlace
import Tom.Machine.Fn.SSubAlias
import Tom.Machine.Fn.CmpMag
import Tom.Machine.Fn.Expt2Main
import Tom.Machine.Kit.MeetD

/-!
# Standard contracts as `Contract` records: `mp_count_bits`, `mp_set`, `mp_2expt`,
`mp_mul_2(a, a)`, `mp_cmp_mag`, `s_mp_sub(a, b, a)`

On top of `Api/Std.lean`; the callees of `mp_montgomery_calc_normalization`.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api

/-! ## `mp_count_bits(a)`: read only -/

def cntBits : Contract where
  P := ObP
  X := Unit
  R := Ob
  all := [.S, .D, .code]
  hall := Ob.all
  entry := CountBits.entry
  args p := [(10, BitVec.ofNat 64 p.p)]
  rets p ra := [(1, ra), (10, BitVec.ofNat 64 (countBits p.a))]
  lay p := Ob.lay p.p p.dp p.a.alloc
  kind := fun ⟨p, dp, a⟩ => Ob.kind p dp a
  out := fun ⟨p, dp, a⟩ _ => Ob.kind p dp a
  isW _ := false
  ws := []
  Res p := p.a.Valid ∧ Layout.digitBits * p.a.used < 2 ^ 31
  Q _ _ := True
  fits p r := by cases p; cases r <;> exact Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qp, qdp, qa⟩ := p
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩) (Fn.CountBits.correct (v := v)
      (outp := outp) { ra_ := Hdr.mpAt (hB .S).2 (hB .D).2, va := hres.1, ga := Hdr.geom (hB .S).2, bits := hres.2
                       ra_al := hra, img := (hB .code).2 })

/-! ## `mp_set(a, d)` -/

structure SetP where
  p : Nat
  dp : Nat
  a : MpInt
  d : Nat

def mpSet : Contract where
  P := SetP
  X := MpInt
  R := Ob
  all := [.S, .D, .code]
  hall := Ob.all
  entry := MpSet.entry
  args p := [(10, BitVec.ofNat 64 p.p), (11, BitVec.ofNat 64 p.d)]
  rets _ ra := [(1, ra)]
  lay p := Ob.lay p.p p.dp p.a.alloc
  kind := fun ⟨p, dp, a, _⟩ => Ob.kind p dp a
  out := fun ⟨p, dp, _, _⟩ x => Ob.kind p dp x
  isW := Ob.isW
  ws := [.S, .D]
  Res p := p.a.Shape ∧ 1 ≤ p.a.alloc
  Q p x := SetPost p.a (p.d % radix) x
  fits p r := by cases p; cases r <;> exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> simp [Ob.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Ob.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qp, qdp, qa, qd⟩ := p
    have e1 := hS .S .D (by decide); have e2 := hS .S .code (by decide); have e3 := hS .D .code (by decide)
    have hU : Sound (Un.lay 0 0 qp qdp qa) Un.isW := fun r s h => by
      cases r <;> cases s <;> simp_all [Sep, Un.isW, Un.lay, Ob.lay, Iv.Disj, Disj] <;> omega
    have hpre : MpSet.Pre m 0 qp qdp qa ra :=
      { ra_ := Hdr.mpAt (hB .S).2 (hB .D).2, sa := hres.1, ga := Hdr.geom (hB .S).2, room := hres.2, ra_al := hra
        img := (hB .code).2, lay := hU }
    refine Triple.rmap (fun cf ⟨a', M, hat, hpost⟩ => ?_) (Fn.MpSet.correct (v := v) (outp := outp) (bn := qd) hpre)
    have hF : Frm (Ob.lay qp qdp qa.alloc) [Ob.S, Ob.D] m M := fun x hx => hpost.frame x fun h' => by
      rcases h' with h' | h' | h' | h'
      · simp [Un.lay, Iv.In] at h'
      · exact hx (Or.inl h')
      · exact hx (Or.inr (Or.inl h'))
      · exact h'.elim
    have hal := hpost.set.alloc
    refine ⟨a', M, hat, hpost.set, ?_, hF⟩
    intro r; cases r
    · exact witS hpost.repr (Hdr.geom (hB .S).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .S).2) hal (Iv.sub_self _)
    · exact hB.keep hS hF Ob.code

/-! ## One operand with a stack: `mp_2expt(a, k)`, `mp_mul_2(a, a)` -/

structure E2Res (p : LshdP) : Prop where
  sa : p.a.Shape
  k_lt : p.k < 2 ^ 31
  room : p.k / Layout.digitBits + 1 ≤ p.a.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 48 ≤ p.sp

def mp2expt : Contract where
  P := LshdP
  X := MpInt
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := Expt2.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.k)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Un.lay 48 p.sp p.pa p.adp p.a
  kind := fun ⟨_, pa, adp, a, _⟩ => Tom.Machine.Un.kind pa adp a
  out := fun ⟨_, pa, adp, _, _⟩ x => Tom.Machine.Un.kind pa adp x
  isW := Un.isW
  ws := Un.ws
  Res := E2Res
  Q p x := Expt2Post p.a p.k x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qa, qk⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : Expt2.Pre m qsp qpa qadp qa qk ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, sa := hres.sa, ga := Hdr.geom (hB .aS).2, b_lt := hres.k_lt
        room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge, ra_al := hra
        img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.Expt2.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, hpost.expt, ?_, hpost.frame⟩
    have hal := hpost.expt.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Un.R.code

structure UnP where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt

structure Mul2Res (p : UnP) : Prop where
  va : p.a.Valid
  room : p.a.used + 1 ≤ p.a.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 32 ≤ p.sp

def mul2I : Contract where
  P := UnP
  X := MpInt
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := Mul2.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pa)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Un.lay 32 p.sp p.pa p.adp p.a
  kind := fun ⟨_, pa, adp, a⟩ => Tom.Machine.Un.kind pa adp a
  out := fun ⟨_, pa, adp, _⟩ x => Tom.Machine.Un.kind pa adp x
  isW := Un.isW
  ws := Un.ws
  Res := Mul2Res
  Q p x := Mul2Post p.a p.a x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qa⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : Mul2.PreI m qsp qpa qadp qa ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, va := hres.va, ga := Hdr.geom (hB .aS).2, room := hres.room
        rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.Mul2.correct_inplace (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, hpost.mul2, ?_, hpost.frame⟩
    have hal := hpost.mul2.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Un.R.code

/-! ## Two operands: `mp_cmp_mag(a, b)` (read only), `s_mp_sub(a, b, a)` -/

inductive Ab | aS | aD | bS | bD | code
  deriving DecidableEq

structure AbP where
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt

def cmpMagN : Contract where
  P := AbP
  X := Unit
  R := Ab
  all := [.aS, .aD, .bS, .bD, .code]
  hall r := by cases r <;> simp
  entry := Fn.CmpMag.entry
  args p := [(10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]
  rets p ra := [(1, ra), (10, BitVec.ofInt 64 (ordCode (compare p.a.mag p.b.mag)))]
  lay p := fun
    | .aS => ⟨p.pa, 24⟩ | .aD => ⟨p.adp, 4 * p.a.alloc⟩ | .bS => ⟨p.pb, 24⟩ | .bD => ⟨p.bdp, 4 * p.b.alloc⟩
    | .code => textIv
  kind p := fun
    | .aS => .mpS p.pa p.adp p.a | .aD => .mpD p.adp p.a.alloc p.a.digit | .bS => .mpS p.pb p.bdp p.b
    | .bD => .mpD p.bdp p.b.alloc p.b.digit | .code => .code
  out p _ := fun
    | .aS => .mpS p.pa p.adp p.a | .aD => .mpD p.adp p.a.alloc p.a.digit | .bS => .mpS p.pb p.bdp p.b
    | .bD => .mpD p.bdp p.b.alloc p.b.digit | .code => .code
  isW _ := false
  ws := []
  Res p := p.a.Valid ∧ p.b.Valid
  Q _ _ := True
  fits p r := by cases r <;> exact Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB
    obtain ⟨qpa, qadp, qpb, qbdp, qa, qb⟩ := p
    have hpre : Fn.CmpMag.Pre m qpa qadp qpb qbdp qa qb :=
      { ra := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2
        va := hres.1, vb := hres.2, ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2
        code := Img.mpCmpMag (hB .code).2 }
    exact Triple.rmap (fun cf hc => ⟨(), m, hc, trivial, hB, Frm.refl _ _⟩)
      (Fn.CmpMag.correct ra v outp qpa qadp qpb qbdp qa qb m hra hpre)

structure SubARes (p : TwoP) : Prop where
  sa : p.a.Shape
  sb : p.b.Shape
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  ge : p.b.used ≤ p.a.used
  sp_al : p.sp % 16 = 0
  sp_ge : 48 ≤ p.sp

def sSubA : Contract where
  P := TwoP
  X := MpInt
  R := BinA.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := BinA.all
  entry := SSubAlias.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
    (12, BitVec.ofNat 64 p.pa)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := BinA.lay 48 p.sp p.pa p.adp p.pb p.bdp p.a p.b
  kind := fun ⟨_, pa, adp, pb, bdp, a, b⟩ => Tom.Machine.BinA.kind pa adp pb bdp a b
  out := fun ⟨_, pa, adp, pb, bdp, _, b⟩ x => Tom.Machine.BinA.kind pa adp pb bdp x b
  isW := BinA.isWA
  ws := BinA.wsA
  Res := SubARes
  Q p x := SSubPost p.a p.b p.a x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.BinA.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.BinA.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : SSubAlias.PreCA m qsp qpa qadp qpb qbdp qa qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2
        ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2
        sa := hres.sa, sb := hres.sb, asign := hres.asign, ge := hres.ge, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.SSub.correctCA (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, hpost.ssub, ?_, hpost.frame⟩
    have hal := hpost.ssub.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame BinA.R.bS
    · exact hB.keep hS hpost.frame BinA.R.bD
    · exact hB.keep hS hpost.frame BinA.R.code

end Tom.Machine.Std
