import Tom.Machine.Fn.MpLshdGMainG
import Tom.Machine.Fn.MpMul2dIMainG
import Tom.Machine.Fn.MulDGMainG
import Tom.Machine.Fn.SAddGMainG
import Tom.Machine.Fn.SAddGAMainG
import Tom.Machine.Fn.SAddGBMainG
import Tom.Machine.Fn.SSubGMainG
import Tom.Machine.Fn.SSubGAMainG
import Tom.Machine.Fn.SSubGBMainG

/-!
# Growing callees as allocating contracts

The callees `mp_div` needs with no room assumption,
each its generated proof read as an `HContract` (`Kit/MeetHeap.lean`) whose site is the
caller's own digit array: `Place.keep` without growth, `Place.regrow` after `realloc`, and an
`MP_MEM` outcome (`x = none`) that changes nothing.

* `mpLshdG`: `mp_lshd(a, k)` (`Api/MpLshdG.lean`, `Fn.MpLshdGG5.correct`), regions `stk aS aD
  code`, stack 576.
* `mpMul2dI`: `mp_mul_2d(a, b, a)` (`Api/MpMul2dI.lean`, `Fn.MpMul2dIG5.correct`), regions
  `stk aS aD code`, stack 592.
* `mulDG`: `mp_mul_d(a, b, c)` (`Api/MulDG.lean`, `Fn.MulDGG5.correct`), regions `stk aS aD cS cD
  code` (site `cD`), stack 624.
* `sAddG`, `sAddGA`, `sAddGB`: `s_mp_add(a, b, c)`, `(a, b, a)`, `(a, b, b)` (`Api/SAddG*.lean`, one rows
  file `saddgg`, three annotations), stack 608.
* `sSubG`, `sSubGA`, `sSubGB`: `s_mp_sub(a, b, c)`, `(a, b, a)`, `(a, b, b)` (`Api/SSubG*.lean`, rows
  `ssubgg`), stack 592; `mp_add`/`mp_sub` with unequal signs need them.
-/

namespace Tom.Machine.Std

open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc

/-- `mp_lshd(a, k)`, growing `a` when it must. -/
def mpLshdG : HContract where
  P := Api.MpLshdG.P
  X := Option (Nat × MpInt)
  R := Api.MpLshdG.R
  all := [.stk, .aS, .aD, .code]
  hall := Api.MpLshdG.all
  entry := Api.MpLshdG.entry
  args := Api.MpLshdG.args
  rets := Api.MpLshdG.rets
  lay := Api.MpLshdG.lay
  kind := Api.MpLshdG.kind
  out := Api.MpLshdG.out
  isW := Api.MpLshdG.isW
  ws := Api.MpLshdG.ws
  site := .aD
  site' := Api.MpLshdG.site'
  hin := Api.MpLshdG.hin
  hout := Api.MpLshdG.hout
  Res := Api.MpLshdG.Res
  Q := Api.MpLshdG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, a'⟩ <;> cases r <;> simp_all [Api.MpLshdG.out, Api.MpLshdG.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos
    cases r with
    | stk => exact .inl (show 0 < Api.MpLshdG.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.MpLshdGG5.correct

/-- `mp_mul_2d(a, b, a)`, growing `a` when it must. -/
def mpMul2dI : HContract where
  P := Api.MpMul2dI.P
  X := Option (Nat × MpInt)
  R := Api.MpMul2dI.R
  all := [.stk, .aS, .aD, .code]
  hall := Api.MpMul2dI.all
  entry := Api.MpMul2dI.entry
  args := Api.MpMul2dI.args
  rets := Api.MpMul2dI.rets
  lay := Api.MpMul2dI.lay
  kind := Api.MpMul2dI.kind
  out := Api.MpMul2dI.out
  isW := Api.MpMul2dI.isW
  ws := Api.MpMul2dI.ws
  site := .aD
  site' := Api.MpMul2dI.site'
  hin := Api.MpMul2dI.hin
  hout := Api.MpMul2dI.hout
  Res := Api.MpMul2dI.Res
  Q := Api.MpMul2dI.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, a'⟩ <;> cases r <;> simp_all [Api.MpMul2dI.out, Api.MpMul2dI.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos
    cases r with
    | stk => exact .inl (show 0 < Api.MpMul2dI.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.MpMul2dIG5.correct

/-- `mp_mul_d(a, b, c)`, growing `c` when it must. -/
def mulDG : HContract where
  P := Api.MulDG.P
  X := Option (Nat × MpInt)
  R := Api.MulDG.R
  all := [.stk, .aS, .aD, .cS, .cD, .code]
  hall := Api.MulDG.all
  entry := Api.MulDG.entry
  args := Api.MulDG.args
  rets := Api.MulDG.rets
  lay := Api.MulDG.lay
  kind := Api.MulDG.kind
  out := Api.MulDG.out
  isW := Api.MulDG.isW
  ws := Api.MulDG.ws
  site := .cD
  site' := Api.MulDG.site'
  hin := Api.MulDG.hin
  hout := Api.MulDG.hout
  Res := Api.MulDG.Res
  Q := Api.MulDG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩ <;> cases r <;> simp_all [Api.MulDG.out, Api.MulDG.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.cpos
    cases r with
    | stk => exact .inl (show 0 < Api.MulDG.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | cS => exact .inl (show 0 < 24 by decide)
    | cD => exact .inl (show 0 < 4 * p.c.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.MulDGG5.correct

/-- `s_mp_add(a, b, c)`, growing `c` when it must. -/
def sAddG : HContract where
  P := Api.SAddG.P
  X := Option (Nat × MpInt)
  R := Api.SAddG.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .code]
  hall := Api.SAddG.all
  entry := Api.SAddG.entry
  args := Api.SAddG.args
  rets := Api.SAddG.rets
  lay := Api.SAddG.lay
  kind := Api.SAddG.kind
  out := Api.SAddG.out
  isW := Api.SAddG.isW
  ws := Api.SAddG.ws
  site := .cD
  site' := Api.SAddG.site'
  hin := Api.SAddG.hin
  hout := Api.SAddG.hout
  Res := Api.SAddG.Res
  Q := Api.SAddG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩ <;> cases r <;> simp_all [Api.SAddG.out, Api.SAddG.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos; have := h.cpos;
    cases r with
    | stk => exact .inl (show 0 < Api.SAddG.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bS => exact .inl (show 0 < 24 by decide)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | cS => exact .inl (show 0 < 24 by decide)
    | cD => exact .inl (show 0 < 4 * p.c.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.SAddGG5.correct

/-- `s_mp_add(a, b, a)`, growing `a` when it must. -/
def sAddGA : HContract where
  P := Api.SAddGA.P
  X := Option (Nat × MpInt)
  R := Api.SAddGA.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Api.SAddGA.all
  entry := Api.SAddGA.entry
  args := Api.SAddGA.args
  rets := Api.SAddGA.rets
  lay := Api.SAddGA.lay
  kind := Api.SAddGA.kind
  out := Api.SAddGA.out
  isW := Api.SAddGA.isW
  ws := Api.SAddGA.ws
  site := .aD
  site' := Api.SAddGA.site'
  hin := Api.SAddGA.hin
  hout := Api.SAddGA.hout
  Res := Api.SAddGA.Res
  Q := Api.SAddGA.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩ <;> cases r <;> simp_all [Api.SAddGA.out, Api.SAddGA.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos;
    cases r with
    | stk => exact .inl (show 0 < Api.SAddGA.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bS => exact .inl (show 0 < 24 by decide)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.SAddGAG5.correct

/-- `s_mp_add(a, b, b)`, growing `b` when it must. -/
def sAddGB : HContract where
  P := Api.SAddGB.P
  X := Option (Nat × MpInt)
  R := Api.SAddGB.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Api.SAddGB.all
  entry := Api.SAddGB.entry
  args := Api.SAddGB.args
  rets := Api.SAddGB.rets
  lay := Api.SAddGB.lay
  kind := Api.SAddGB.kind
  out := Api.SAddGB.out
  isW := Api.SAddGB.isW
  ws := Api.SAddGB.ws
  site := .bD
  site' := Api.SAddGB.site'
  hin := Api.SAddGB.hin
  hout := Api.SAddGB.hout
  Res := Api.SAddGB.Res
  Q := Api.SAddGB.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩ <;> cases r <;> simp_all [Api.SAddGB.out, Api.SAddGB.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos;
    cases r with
    | stk => exact .inl (show 0 < Api.SAddGB.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bS => exact .inl (show 0 < 24 by decide)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.SAddGBG5.correct

/-- `s_mp_sub(a, b, c)`, growing `c` when it must. -/
def sSubG : HContract where
  P := Api.SSubG.P
  X := Option (Nat × MpInt)
  R := Api.SSubG.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .code]
  hall := Api.SSubG.all
  entry := Api.SSubG.entry
  args := Api.SSubG.args
  rets := Api.SSubG.rets
  lay := Api.SSubG.lay
  kind := Api.SSubG.kind
  out := Api.SSubG.out
  isW := Api.SSubG.isW
  ws := Api.SSubG.ws
  site := .cD
  site' := Api.SSubG.site'
  hin := Api.SSubG.hin
  hout := Api.SSubG.hout
  Res := Api.SSubG.Res
  Q := Api.SSubG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩ <;> cases r <;> simp_all [Api.SSubG.out, Api.SSubG.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos; have := h.cpos;
    cases r with
    | stk => exact .inl (show 0 < Api.SSubG.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bS => exact .inl (show 0 < 24 by decide)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | cS => exact .inl (show 0 < 24 by decide)
    | cD => exact .inl (show 0 < 4 * p.c.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.SSubGG5.correct

/-- `s_mp_sub(a, b, a)`, growing `a` when it must. -/
def sSubGA : HContract where
  P := Api.SSubGA.P
  X := Option (Nat × MpInt)
  R := Api.SSubGA.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Api.SSubGA.all
  entry := Api.SSubGA.entry
  args := Api.SSubGA.args
  rets := Api.SSubGA.rets
  lay := Api.SSubGA.lay
  kind := Api.SSubGA.kind
  out := Api.SSubGA.out
  isW := Api.SSubGA.isW
  ws := Api.SSubGA.ws
  site := .aD
  site' := Api.SSubGA.site'
  hin := Api.SSubGA.hin
  hout := Api.SSubGA.hout
  Res := Api.SSubGA.Res
  Q := Api.SSubGA.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩ <;> cases r <;> simp_all [Api.SSubGA.out, Api.SSubGA.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos;
    cases r with
    | stk => exact .inl (show 0 < Api.SSubGA.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bS => exact .inl (show 0 < 24 by decide)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.SSubGAG5.correct

/-- `s_mp_sub(a, b, b)`, growing `b` when it must. -/
def sSubGB : HContract where
  P := Api.SSubGB.P
  X := Option (Nat × MpInt)
  R := Api.SSubGB.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Api.SSubGB.all
  entry := Api.SSubGB.entry
  args := Api.SSubGB.args
  rets := Api.SSubGB.rets
  lay := Api.SSubGB.lay
  kind := Api.SSubGB.kind
  out := Api.SSubGB.out
  isW := Api.SSubGB.isW
  ws := Api.SSubGB.ws
  site := .bD
  site' := Api.SSubGB.site'
  hin := Api.SSubGB.hin
  hout := Api.SSubGB.hout
  Res := Api.SSubGB.Res
  Q := Api.SSubGB.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩ <;> cases r <;> simp_all [Api.SSubGB.out, Api.SSubGB.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos;
    cases r with
    | stk => exact .inl (show 0 < Api.SSubGB.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bS => exact .inl (show 0 < 24 by decide)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.SSubGBG5.correct

end Tom.Machine.Std
