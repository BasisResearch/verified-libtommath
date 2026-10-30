import Tom.Machine.Api.Std
import Tom.Machine.Api.MontRedFast
import Tom.Machine.Fn.MontRedFastMain
import Tom.Machine.Api.MulHighFast
import Tom.Machine.Fn.MulHighFastMain

/-!
# Standard contracts as `Contract` records: `s_mp_montgomery_reduce_fast`,
`s_mp_mul_high_digs_fast(a, b, a, digs)`

On top of `Api/Std.lean`; the fast paths of `mp_montgomery_reduce` (`Api/MontRed.lean`) and of
`s_mp_mul_high_digs(a, b, a, digs)` (`Api/SMpMulHighDigs.lean`), both tail calls. Regions as
`Api/Two.lean` with the read operand Two's `a` and the written one Two's `b`.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Mont

/-! ## `s_mp_montgomery_reduce_fast(x, n, rho)` -/

structure RedFP where
  sp : Nat
  px : Nat
  xdp : Nat
  pn : Nat
  ndp : Nat
  x : MpInt
  n : MpInt
  rho : Nat

structure RedFRes (p : RedFP) : Prop where
  vx : p.x.Valid
  vn : p.n.Valid
  rho_ok : (p.n.mag * p.rho + 1) % radix = 0
  rho_lt : p.rho < radix
  x_lt : p.x.mag < p.n.mag * radix ^ p.n.used
  nu_pos : 1 ≤ p.n.used
  nu_le : p.n.used ≤ 255
  room : p.n.used < p.x.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 4256 ≤ p.sp

def montRedF : Contract where
  P := RedFP
  X := MpInt
  R := Two.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Two.all
  entry := MontRedFast.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.px), (11, BitVec.ofNat 64 p.pn),
    (12, BitVec.ofNat 64 p.rho)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Two.lay 4256 p.sp p.pn p.ndp p.px p.xdp p.n p.x
  kind := fun ⟨_, px, xdp, pn, ndp, x, n, _⟩ => Tom.Machine.Two.kind pn ndp px xdp n x
  out := fun ⟨_, px, xdp, pn, ndp, _, n, _⟩ x' => Tom.Machine.Two.kind pn ndp px xdp n x'
  isW := Two.isW
  ws := Two.ws
  Res := RedFRes
  Q p x' := RedcPost p.x p.n p.rho x'
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpx, qxdp, qpn, qndp, qx, qn, qrho⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MontRedFast.Pre m qsp qpx qxdp qpn qndp qx qn qrho ra :=
      { rx := Hdr.mpAt (hB .bS).2 (hB .bD).2, rn := Hdr.mpAt (hB .aS).2 (hB .aD).2, vx := hres.vx
        vn := hres.vn, gx := Hdr.geom (hB .bS).2, gn := Hdr.geom (hB .aS).2, rho_ok := hres.rho_ok
        rho_lt := hres.rho_lt, x_lt := hres.x_lt, nu_pos := hres.nu_pos, nu_le := hres.nu_le
        room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge, ra_al := hra
        img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, x', M, hat, hpost⟩ :=
      Fn.MontRedFast.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, x', M, hat.sub rfl rfl, hpost.redc, ?_, hpost.frame⟩
    have hal := hpost.redc.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact hB.keep hS hpost.frame Two.R.aS
    · exact hB.keep hS hpost.frame Two.R.aD
    · exact witS hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Two.R.code

/-! ## `s_mp_mul_high_digs_fast(a, b, a, digs)` (in place) -/

structure HighFP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  dg : Nat
  a : MpInt
  b : MpInt

structure HighFRes (p : HighFP) : Prop where
  sa : p.a.Shape
  sb : p.b.Shape
  cond : MulHighFast.Cond p.a p.b p.dg
  room : p.a.used + p.b.used ≤ p.a.alloc
  sp_al : p.sp % 16 = 0
  sp_ge : 2192 ≤ p.sp

def mulHighFI : Contract where
  P := HighFP
  X := MpInt
  R := Two.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Two.all
  entry := MulHighFast.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pb),
    (12, BitVec.ofNat 64 p.pa), (13, BitVec.ofNat 64 p.dg)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Two.lay 2192 p.sp p.pb p.bdp p.pa p.adp p.b p.a
  kind := fun ⟨_, pa, adp, pb, bdp, _, a, b⟩ => Tom.Machine.Two.kind pb bdp pa adp b a
  out := fun ⟨_, pa, adp, pb, bdp, _, _, b⟩ x => Tom.Machine.Two.kind pb bdp pa adp b x
  isW := Two.isW
  ws := Two.ws
  Res := HighFRes
  Q p x := Reduce.MulHighFastPost p.a p.b p.a x p.dg
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Two.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qpb, qbdp, qdg, qa, qb⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : MulHighFast.Pre m qsp qpa qadp qpb qbdp qdg qa qb ra :=
      { ra_ := Hdr.mpAt (hB .bS).2 (hB .bD).2, rb := Hdr.mpAt (hB .aS).2 (hB .aD).2, sa := hres.sa
        sb := hres.sb, ga := Hdr.geom (hB .bS).2, gb := Hdr.geom (hB .aS).2, cond := hres.cond
        room := hres.room, rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge, ra_al := hra
        img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, x', M, hat, hpost⟩ :=
      Fn.MulHighFast.correct (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, x', M, hat.sub rfl rfl, hpost.fast, ?_, hpost.frame⟩
    have hal := hpost.fast.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact hB.keep hS hpost.frame Two.R.aS
    · exact hB.keep hS hpost.frame Two.R.aD
    · exact witS hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .bS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Two.R.code

end Tom.Machine.Std
