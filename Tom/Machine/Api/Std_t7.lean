import Tom.Machine.Api.Std_r6g
import Tom.Machine.Api.Std_r6h
import Tom.Machine.Fn.GrowT7
import Tom.Machine.Fn.GrowH
import Tom.Machine.Api.MpSubH
import Tom.Machine.Api.Mul2H
import Tom.Machine.Api.MpSqrS
import Tom.Machine.Api.Div2
import Tom.Machine.Fn.Div2InPlace
import Tom.Machine.Fn.KSqrG5K

/-!
# Callee contracts of `s_mp_toom_sqr`

* `mpAddHAv`, `mpAddHBv`: the growing `mp_add(a, b, a)`, `mp_add(a, b, b)` read as values.
* `mpSubHc`, `mpSubHAc`, `mul2Hc`: the growing `mp_sub(a, b, c)`, `mp_sub(a, b, a)`,
  `mp_mul_2(a, a)` (`Api/MpSubH.lean`, `Api/Mul2H.lean`): named premises, carried in the residue.
* `div2I`: `mp_div_2(a, a)` (`Fn.Div2InPlace.correct_inplace`; in place `a->used ≤ a->alloc`, no
  growth).
* `sqrSK`, `sqrSAK`: `mp_sqr` on an operand below 120 digits without the room (`Api/MpSqrS.lean`,
  named premises), with `KSqrG5K`'s cut-off-word parameters for the generator's region matching.
* `mpMulAK`: `mp_mul(a, b, a)` (`Api/MpMulA.lean`, its Statement in the residue: `mp_mul`'s
  recursion group closes without the squaring group), with the cut-off words named.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-! ## `mp_add(a, b, a)`, `mp_add(a, b, b)` growing, as values -/

def mpAddHAv : HContract where
  P := MpAddGA.P
  X := MpSqr.X
  R := MpAddGA.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := MpAddGA.all
  entry := MpAddGA.entry
  args := MpAddGA.args
  rets := MpAddHA.rets
  lay := MpAddGA.lay
  kind := MpAddGA.kind
  out := MpAddHA.out
  isW := MpAddGA.isW
  ws := MpAddGA.ws
  site := .aD
  site' := MpAddHA.site'
  hin := MpAddGA.hin
  hout := MpAddHA.hout
  Res := MpAddGA.Res
  Q := MpAddHA.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpAddHA.out, MpAddGA.kind, MpAddGA.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos
    left
    cases r with
    | code => exact (show 0 < textLen by decide)
    | stk => exact (show 0 < MpAddGA.F by decide)
    | aS | bS => exact (show 0 < 24 by decide)
    | aD => exact (show 0 < 4 * p.a.alloc by omega)
    | bD => exact (show 0 < 4 * p.b.alloc by omega)
  spec := fun hra hres => Fn.GrowT7.mpAddHA hra hres

def mpAddHBv : HContract where
  P := MpAddGB.P
  X := MpSqr.X
  R := MpAddGB.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := MpAddGB.all
  entry := MpAddGB.entry
  args := MpAddGB.args
  rets := MpAddHB.rets
  lay := MpAddGB.lay
  kind := MpAddGB.kind
  out := MpAddHB.out
  isW := MpAddGB.isW
  ws := MpAddGB.ws
  site := .bD
  site' := MpAddHB.site'
  hin := MpAddGB.hin
  hout := MpAddHB.hout
  Res := MpAddGB.Res
  Q := MpAddHB.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpAddHB.out, MpAddGB.kind, MpAddGB.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos
    left
    cases r with
    | code => exact (show 0 < textLen by decide)
    | stk => exact (show 0 < MpAddGB.F by decide)
    | aS | bS => exact (show 0 < 24 by decide)
    | aD => exact (show 0 < 4 * p.a.alloc by omega)
    | bD => exact (show 0 < 4 * p.b.alloc by omega)
  spec := fun hra hres => Fn.GrowT7.mpAddHB hra hres

/-! ## The growing `mp_sub`, `mp_mul_2` (named premises in the residue) -/

structure SubHRes (p : MpAddH.P) : Prop where
  res : MpAddH.Res p
  stmt : MpSubH.Statement

def mpSubHc : HContract where
  P := MpAddH.P
  X := MpSqr.X
  R := Bin.R
  all := [.stk, .cS, .cD, .aS, .aD, .bS, .bD, .code]
  hall := Bin.all
  entry := MpSubH.entry
  args := MpAddH.args
  rets := MpAddH.rets
  lay := MpAddH.lay
  kind := MpAddH.kind
  out := MpAddH.out
  isW := Bin.isW
  ws := Bin.ws
  site := .cD
  site' := MpAddH.site'
  hin := MpAddH.hin
  hout := MpAddH.hout
  Res := SubHRes
  Q := MpSubH.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpAddH.out, MpAddH.kind, Bin.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.res.apos; have := h.res.bpos; have := h.res.cpos
    left
    cases r with
    | code => exact (show 0 < textLen by decide)
    | stk => exact (show 0 < 608 by decide)
    | cS | aS | bS => exact (show 0 < 24 by decide)
    | cD => exact (show 0 < 4 * p.c.alloc by omega)
    | aD => exact (show 0 < 4 * p.a.alloc by omega)
    | bD => exact (show 0 < 4 * p.b.alloc by omega)
  spec := fun hra hres => hres.stmt hra hres.res

structure SubHARes (p : MpAddGA.P) : Prop where
  res : MpAddGA.Res p
  stmt : MpSubHA.Statement

def mpSubHAc : HContract where
  P := MpAddGA.P
  X := MpSqr.X
  R := MpAddGA.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := MpAddGA.all
  entry := MpSubHA.entry
  args := MpAddGA.args
  rets := MpAddHA.rets
  lay := MpAddGA.lay
  kind := MpAddGA.kind
  out := MpAddHA.out
  isW := MpAddGA.isW
  ws := MpAddGA.ws
  site := .aD
  site' := MpAddHA.site'
  hin := MpAddGA.hin
  hout := MpAddHA.hout
  Res := SubHARes
  Q := MpSubHA.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpAddHA.out, MpAddGA.kind, MpAddGA.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.res.apos; have := h.res.bpos
    left
    cases r with
    | code => exact (show 0 < textLen by decide)
    | stk => exact (show 0 < MpAddGA.F by decide)
    | aS | bS => exact (show 0 < 24 by decide)
    | aD => exact (show 0 < 4 * p.a.alloc by omega)
    | bD => exact (show 0 < 4 * p.b.alloc by omega)
  spec := fun hra hres => hres.stmt hra hres.res

structure Mul2HRes (p : Mul2H.P) : Prop where
  res : Mul2H.Res p
  stmt : Mul2H.Statement

def mul2Hc : HContract where
  P := Mul2H.P
  X := MpSqr.X
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := Mul2H.entry
  args := Mul2H.args
  rets := Mul2H.rets
  lay := Mul2H.lay
  kind := Mul2H.kind
  out := Mul2H.out
  isW := Un.isW
  ws := Un.ws
  site := .aD
  site' := Mul2H.site'
  hin := Mul2H.hin
  hout := Mul2H.hout
  Res := Mul2HRes
  Q := Mul2H.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [Mul2H.out, Mul2H.kind, Un.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.res.apos
    left
    cases r with
    | code => exact (show 0 < textLen by decide)
    | stk => exact (show 0 < 576 by decide)
    | aS => exact (show 0 < 24 by decide)
    | aD => exact (show 0 < 4 * p.a.alloc by omega)
  spec := fun hra hres => hres.stmt hra hres.res

/-! ## `mp_div_2(a, a)` -/

structure Div2Res (p : UnP) : Prop where
  va : p.a.Valid
  sp_al : p.sp % 16 = 0
  sp_ge : 32 ≤ p.sp

def div2I : Contract where
  P := UnP
  X := MpInt
  R := Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Un.all
  entry := Div2.entry
  args p := [(2, BitVec.ofNat 64 p.sp), (10, BitVec.ofNat 64 p.pa), (11, BitVec.ofNat 64 p.pa)]
  rets _ ra := [(1, ra), (10, 0#64)]
  lay p := Un.lay 32 p.sp p.pa p.adp p.a
  kind := fun ⟨_, pa, adp, a⟩ => Tom.Machine.Un.kind pa adp a
  out := fun ⟨_, pa, adp, _⟩ x => Tom.Machine.Un.kind pa adp x
  isW := Un.isW
  ws := Un.ws
  Res := Div2Res
  Q p x := Div2Post p.a p.a x
  fits p r := by cases p; cases r <;> first | trivial | exact Iv.sub_self _
  out_ram p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  out_ind p x r _ h := by cases p; cases r <;> first | rfl | simp [Tom.Machine.Un.kind, Kind.isRam] at h
  spec := by
    intro p m v outp ra hra hres hS hB c hc
    obtain ⟨qsp, qpa, qadp, qa⟩ := p
    obtain ⟨sp', gp, tp, s0, s⟩ := v
    have he := At.sp_eq hc (x := BitVec.ofNat 64 qsp) rfl
    simp only at he; subst he
    have hpre : Div2.PreI m qsp qpa qadp qa ra :=
      { ra_ := Hdr.mpAt (hB .aS).2 (hB .aD).2, va := hres.va, ga := Hdr.geom (hB .aS).2, room := hres.va.used_le
        rs := (hB .stk).2, sp_al := hres.sp_al, sp_ge := hres.sp_ge, ra_al := hra, img := (hB .code).2, lay := hS }
    obtain ⟨c', hs, a', M, hat, hpost⟩ :=
      Fn.Div2.correct_inplace (v := ⟨_, gp, tp, s0, s⟩) (s0 := s0) (outp := outp) hpre c (hc.sub rfl rfl)
    refine ⟨c', hs, a', M, hat.sub rfl rfl, hpost.div2, ?_, hpost.frame⟩
    have hal := hpost.div2.alloc
    intro r; cases r
    · exact ⟨trivial, (hB .stk).2⟩
    · exact witS hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact witD hpost.repr (Hdr.geom (hB .aS).2) hal (Iv.sub_self _)
    · exact hB.keep hS hpost.frame Un.R.code

/-! ## `mp_sqr` below 120 digits, growing (named premises) -/

open Tom.Machine.Fn.KSqrG5K (SqrBKP SqrABKP)

def SqrBKP.toP (p : SqrBKP) : MpSqr.P := ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
def SqrABKP.toP (p : SqrABKP) : MpSqrA.P := ⟨p.sp, p.pa, p.adp, p.a, p.H⟩

structure SqrSRes (p : SqrBKP) : Prop where
  res : MpSqrS.Res (SqrBKP.toP p)
  stmt : MpSqrS.Statement

structure SqrSARes (p : SqrABKP) : Prop where
  res : MpSqrSA.Res (SqrABKP.toP p)
  stmt : MpSqrSA.Statement

def sqrSK : HContract where
  P := SqrBKP
  X := MpSqr.X
  R := MpSqr.R
  all := [.stk, .aS, .aD, .bS, .bD, .ks, .ts, .km, .tm, .code]
  hall := MpSqr.all
  entry := MpSqr.entry
  args p := MpSqr.args ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  rets p := MpSqr.rets ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  lay p := MpSqrS.lay ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  kind p := MpSqr.kind ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  out p := MpSqr.out ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  isW := MpSqr.isW
  ws := MpSqr.ws
  site := .bD
  site' p := MpSqr.site' ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  hin p := MpSqr.hin ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  hout p := MpSqr.hout ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  Res := SqrSRes
  Q p := MpSqr.Q ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  fits p r := by
    cases r <;> first | trivial | exact Iv.sub_self _ | simp [Kind.Fits, MpSqr.kind, MpSqrS.lay, MpSqr.lay, Iv.Sub]
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpSqr.out, MpSqr.kind, MpSqr.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    have : 0 < p.a.alloc := h.res.apos
    have : 0 < p.b.alloc := h.res.bpos
    left
    cases r with
    | stk => exact (show 0 < 4096 by decide)
    | code => exact (show 0 < textLen by decide)
    | aD => exact (show 0 < 4 * p.a.alloc by omega)
    | bD => exact (show 0 < 4 * p.b.alloc by omega)
    | aS | bS => exact (show 0 < 24 by decide)
    | ks | ts | km | tm => exact (show 0 < 4 by decide)
  spec := fun hra hres => hres.stmt (SqrBKP.toP _) hra hres.res

def sqrSAK : HContract where
  P := SqrABKP
  X := MpSqr.X
  R := MpSqrA.R
  all := [.stk, .aS, .aD, .ks, .ts, .km, .tm, .code]
  hall := MpSqrA.all
  entry := MpSqr.entry
  args p := MpSqrA.args ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  rets p := MpSqrA.rets ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  lay p := MpSqrSA.lay ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  kind p := MpSqrA.kind ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  out p := MpSqrA.out ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  isW := MpSqrA.isW
  ws := MpSqrA.ws
  site := .aD
  site' p := MpSqrA.site' ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  hin p := MpSqrA.hin ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  hout p := MpSqrA.hout ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  Res := SqrSARes
  Q p := MpSqrA.Q ⟨p.sp, p.pa, p.adp, p.a, p.H⟩
  fits p r := by
    cases r <;> first | trivial | exact Iv.sub_self _ | simp [Kind.Fits, MpSqrA.kind, MpSqrSA.lay, MpSqrA.lay, Iv.Sub]
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpSqrA.out, MpSqrA.kind, MpSqrA.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    have : 0 < p.a.alloc := h.res.apos
    left
    cases r with
    | stk => exact (show 0 < 4096 by decide)
    | code => exact (show 0 < textLen by decide)
    | aD => exact (show 0 < 4 * p.a.alloc by omega)
    | aS => exact (show 0 < 24 by decide)
    | ks | ts | km | tm => exact (show 0 < 4 by decide)
  spec := fun hra hres => hres.stmt (SqrABKP.toP _) hra hres.res

/-! ## `mp_mul(a, b, a)` from its Statement, the cut-off words named -/

structure MulAKP where
  sp : Nat
  pa : Nat
  adp : Nat
  pb : Nat
  bdp : Nat
  a : MpInt
  b : MpInt
  H : List (Nat × Nat)
  kc : Nat
  tc : Nat

def MulAKP.toP (p : MulAKP) : MpMulA.P := ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩

structure MulAKRes (p : MulAKP) : Prop where
  res : MpMulA.Res p.toP
  stmt : MpMulA.Statement

def mpMulAK : HContract where
  P := MulAKP
  X := MpMul.X
  R := MpMulA.R
  all := [.stk, .aS, .aD, .bS, .bD, .kc, .tc, .code]
  hall := MpMulA.all
  entry := MpMul.entry
  args p := MpMulA.args ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  rets p := MpMulA.rets ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  lay p := MpMulA.lay ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  kind p := MpMulA.kind ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  out p := MpMulA.out ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  isW := MpMulA.isW
  ws := MpMulA.ws
  site := .aD
  site' p := MpMulA.site' ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  hin p := MpMulA.hin ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  hout p := MpMulA.hout ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  Res := MulAKRes
  Q p := MpMulA.Q ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.a, p.b, p.H⟩
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _ | simp [Kind.Fits, MpMulA.kind, MpMulA.lay, Iv.Sub]
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpMulA.out, MpMulA.kind, MpMulA.ws, Kind.isRam, Kind.indep]
  pos p h r := mpMulA_pos p.toP h.res r
  spec := fun hra hres => hres.stmt _ hra hres.res

end Tom.Machine.Std
