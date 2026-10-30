import Tom.Machine.Api.StdR5
import Tom.Machine.Api.SSub

/-!
# Standard contracts as `Contract` records: `s_mp_sub(a, b, c)` with `c` distinct

The callee of `mp_reduce_2k_setup_l` (`s_mp_sub(&tmp, a, d)`): `Api.SSub.correct` re-read as
`Api/Std.lean`'s are, over `Api/Bin.lean`'s regions (stack 48), `c` written in place
(`room`: no `mp_grow`, D5).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api

structure SubDP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  pc : Nat
  cdp : Nat
  a : MpInt
  b : MpInt
  c : MpInt

structure SubDRes (p : SubDP) : Prop where
  sa : p.a.Shape
  sb : p.b.Shape
  sc : p.c.Shape
  csign : p.c.sign = Layout.mpZpos ∨ p.c.sign = Layout.mpNeg
  ge : p.b.used ≤ p.a.used
  room : p.a.used ≤ p.c.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 48 ≤ p.sp

/-- `s_mp_sub(a, b, c)`, `c` distinct from `a`, `b`. -/
def sSubD : Contract where
  P := SubDP
  X := MpInt
  R := Bin.R
  all := [.stk, .cS, .cD, .aS, .aD, .bS, .bD, .code]
  hall := Bin.all
  entry := SSub.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
    (12, BitVec.ofNat 64 p.pc)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Bin.lay 48 p.sp p.pa p.adp p.pb p.bdp p.pc p.cdp p.a p.b p.c
  kind := fun ⟨_, pa, adp, pb, bdp, pc, cdp, a, b, c⟩ => binKind pa adp pb bdp pc cdp a b c
  out := fun ⟨_, pa, adp, pb, bdp, pc, cdp, a, b, _⟩ x => binKind pa adp pb bdp pc cdp a b x
  isW := Bin.isW
  ws := Bin.ws
  Res := SubDRes
  Q p x := SSubPost p.a p.b p.c x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [binKind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [binKind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qpc, qcdp, qa, qb, qc⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : SSub.Pre m qsp qpa qadp qpb qbdp qpc qcdp qa qb qc ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, rb := Hdr.mpAt (hB .bS).2 (hB .bD).2
        rc := Hdr.mpAt (hB .cS).2 (hB .cD).2, sa := hres.sa, sb := hres.sb, sc := hres.sc
        csign := hres.csign, ga := Hdr.geom (hB .aS).2, gb := Hdr.geom (hB .bS).2, gc := Hdr.geom (hB .cS).2
        ge := hres.ge, room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al
        sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, x, M, hat, hrepr, hss, hfr⟩ :=
      SSub.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, x, M, hat.sub rfl rfl, hss, ?_, hfr⟩
    have hal := hss.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hrepr (Hdr.geom (hB .cS).2) hal (Iv.sub_self _)
    · exact witD hrepr (Hdr.geom (hB .cS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hfr Bin.R.aS
    · exact hB.keep hS hfr Bin.R.aD
    · exact hB.keep hS hfr Bin.R.bS
    · exact hB.keep hS hfr Bin.R.bD
    · exact hB.keep hS hfr Bin.R.code

end Tom.Machine.Std
