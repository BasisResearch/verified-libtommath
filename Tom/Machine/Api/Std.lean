import Tom.Machine.Api.StdLib
import Tom.Machine.Api.MpCopy
import Tom.Machine.Api.MpLshd
import Tom.Machine.Fn.MpCopyMain
import Tom.Machine.Fn.MpLshdMain
import Tom.Machine.Fn.MpRshdMain
import Tom.Machine.Api.SSubAlias
import Tom.Machine.Fn.SSubAlias

/-!
# Standard contracts as `Contract` records: `mp_copy`, `mp_lshd`, `mp_rshd`, `s_mp_sub(a, b, a)`

On top of `Api/StdLib.lean` (the leaf library).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api

/-! ## Two operands: `mp_copy(a, b)` -/

structure TwoP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt

structure CopyRes (p : TwoP) : Prop where
  sa : p.a.Shape
  sb : p.b.Shape
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  room : p.a.used ≤ p.b.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 32 ≤ p.sp

def mpCopy : Contract where
  P := TwoP
  X := MpInt
  R := Two.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Two.all
  entry := MpCopy.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Two.lay 32 p.sp p.pa p.adp p.pb p.bdp p.a p.b
  kind := fun ⟨_, pa, adp, pb, bdp, a, b⟩ => Tom.Machine.Two.kind pa adp pb bdp a b
  out := fun ⟨_, pa, adp, pb, bdp, a, _⟩ x => Tom.Machine.Two.kind pa adp pb bdp a x
  isW := Two.isW
  ws := Two.ws
  Res := CopyRes
  Q p x := CopyPost p.a p.b x ∧ x.Shape
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MpCopy.Pre m qsp qpa qadp qpb qbdp qa qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2
        sa := hres.sa, sb := hres.sb, asign := hres.asign, ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2
        room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge, ra_al := hra
        img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, b', M, hat, hpost⟩ :=
      Fn.MpCopy.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, b', M, hat.sub rfl rfl, ⟨hpost.copy, hpost.copy.shape hres.sa hres.sb hres.room⟩, ?_, hpost.frame⟩
    have hal := hpost.copy.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact hB.keep hS hpost.frame Two.R.aS
    · exact hB.keep hS hpost.frame Two.R.aD
    · exact witS hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Two.R.code

/-! ## `mp_lshd(a, k)` -/

structure LshdP where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  k : Nat

structure LshdRes (p : LshdP) : Prop where
  sa : p.a.Shape
  k_lt : p.k < 2 ^ 31
  room : p.a.used + p.k ≤ p.a.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 32 ≤ p.sp

def mpLshd : Contract where
  P := LshdP
  X := MpInt
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := MpLshd.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.k)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Un.lay 32 p.sp p.pa p.adp p.a
  kind := fun ⟨_, pa, adp, a, _⟩ => Tom.Machine.Un.kind pa adp a
  out := fun ⟨_, pa, adp, _, _⟩ x => Tom.Machine.Un.kind pa adp x
  isW := Un.isW
  ws := Un.ws
  Res := LshdRes
  Q p x := LshdPost p.a p.k x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qa, qk⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MpLshd.Pre m qsp qpa qadp qa qk ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, sa := hres.sa, ga := Hdr.geom (hB .aS).2, b_lt := hres.k_lt
        room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge, ra_al := hra
        img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.MpLshd.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, hpost.lshd, ?_, hpost.frame⟩
    have hal := hpost.lshd.alloc'
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Un.R.code

/-! ## `mp_copy(a, a)`: `MP_OKAY`, nothing written -/

structure AliasP where
  sp : Nat
  p : Nat

def mpCopyA : Contract where
  P := AliasP
  X := Unit
  R := Cd
  all := [.code]
  hall r := by cases r; simp
  entry := MpCopy.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.p), (11, BitVec.ofNat 64 p.p)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay _ _ := textIv
  kind _ _ := .code
  out _ _ _ := .code
  isW _ := false
  ws := []
  Res _ := True
  Q _ _ := True
  fits _ _ := Iv.sub_self _
  out_ram _ _ _ h := by simp at h
  out_ind _ _ _ h := by simp at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qp⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    obtain ⟨c', hs, hat⟩ := Fn.MpCopy.alias_correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hra
      (hB .code).2 c (hc.sub rfl rfl)
    exact ⟨c', hs, (), m, hat.sub rfl rfl, trivial, hB, Frm.refl _ _⟩

/-! ## `mp_rshd(a, k)` -/

theorem _root_.Tom.RshdPost.alloc' {a a' : MpInt} {k : Nat} (h : RshdPost a k a') : a'.alloc = a.alloc := by
  rcases Nat.eq_zero_or_pos k with h0 | hk
  · rw [h.noop h0]
  · by_cases hu : a.used ≤ k
    · exact (h.zero hk hu).alloc
    · exact (h.shift hk (by omega)).alloc

structure RshdP where
  sp : Nat
  pa : Nat
  adp : Nat
  a : MpInt
  k : Nat

structure RshdRes (p : RshdP) : Prop where
  sa : p.a.Shape
  k_lt : p.k < 2 ^ 31
  sp_al : p.sp % 16 = 0
  sp_ge : 32 ≤ p.sp

def mpRshd : Contract where
  P := RshdP
  X := MpInt
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := MpRshd.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.k)]
  rets _ ra := [(1, ra)]
  lay p := Un.lay 32 p.sp p.pa p.adp p.a
  kind := fun ⟨_, pa, adp, a, _⟩ => Tom.Machine.Un.kind pa adp a
  out := fun ⟨_, pa, adp, _, _⟩ x => Tom.Machine.Un.kind pa adp x
  isW := Un.isW
  ws := Un.ws
  Res := RshdRes
  Q p x := RshdPost p.a p.k x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qa, qk⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MpRshd.Pre m qsp qpa qadp qa qk ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, sa := hres.sa, ga := Hdr.geom (hB .aS).2, b_lt := hres.k_lt
        rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge, ra_al := hra
        img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.MpRshd.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, hpost.rshd, ?_, hpost.frame⟩
    have hal := hpost.rshd.alloc'
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Un.R.code

/-! ## `s_mp_sub(a, b, a)` (in place, `c = a`) -/

def BinA.kind (pa adp pb bdp : Nat) (a b : MpInt) : BinA.R → Kind
  | .stk => .ram
  | .aS => .mpS pa adp a
  | .aD => .mpD adp a.alloc a.digit
  | .bS => .mpS pb bdp b
  | .bD => .mpD bdp b.alloc b.digit
  | .code => .code

structure SubRes (p : TwoP) : Prop where
  sa : p.a.Shape
  sb : p.b.Shape
  asign : p.a.sign = Layout.mpZpos ∨ p.a.sign = Layout.mpNeg
  ge : p.b.used ≤ p.a.used
  sp_al : p.sp % 16 = 0
  sp_ge : 48 ≤ p.sp

def sSubCA : Contract where
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
  kind := fun ⟨_, pa, adp, pb, bdp, a, b⟩ => BinA.kind pa adp pb bdp a b
  out := fun ⟨_, pa, adp, pb, bdp, _, b⟩ x => BinA.kind pa adp pb bdp x b
  isW := BinA.isWA
  ws := BinA.wsA
  Res := SubRes
  Q p x := SSubPost p.a p.b p.a x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [BinA.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [BinA.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : SSubAlias.PreCA m qsp qpa qadp qpb qbdp qa qb ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2
        ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, sa := hres.sa, sb := hres.sb, asign := hres.asign
        ge := hres.ge, lay := hS }
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
