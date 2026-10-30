import Tom.Machine.Fn.MpAddGMainG
import Tom.Machine.Fn.MpAddGAMainG
import Tom.Machine.Fn.MpAddGBMainG

/-!
# `mp_add` with growth as allocating contracts

`mp_add(a, b, c)`, `(a, b, a)`, `(a, b, b)` (`Api/MpAddG*.lean`): the sign store and the tail
calls to the growing `s_mp_add`/`s_mp_sub` of `Api/Std_grow6.lean` (`tail_heap`, the callee's
`HPost` becoming the caller's). Separate from `Std_grow6.lean`, whose instances these proofs use.
-/

namespace Tom.Machine.Std

open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc

/-- `mp_add(a, b, c)`, growing `c` when it must. -/
def mpAddG : HContract where
  P := Api.MpAddG.P
  X := Option (Nat × MpInt)
  R := Api.MpAddG.R
  all := [.stk, .aS, .aD, .bS, .bD, .cS, .cD, .code]
  hall := Api.MpAddG.all
  entry := Api.MpAddG.entry
  args := Api.MpAddG.args
  rets := Api.MpAddG.rets
  lay := Api.MpAddG.lay
  kind := Api.MpAddG.kind
  out := Api.MpAddG.out
  isW := Api.MpAddG.isW
  ws := Api.MpAddG.ws
  site := .cD
  site' := Api.MpAddG.site'
  hin := Api.MpAddG.hin
  hout := Api.MpAddG.hout
  Res := Api.MpAddG.Res
  Q := Api.MpAddG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩ <;> cases r <;> simp_all [Api.MpAddG.out, Api.MpAddG.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos; have := h.cpos;
    cases r with
    | stk => exact .inl (show 0 < Api.MpAddG.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bS => exact .inl (show 0 < 24 by decide)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | cS => exact .inl (show 0 < 24 by decide)
    | cD => exact .inl (show 0 < 4 * p.c.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.MpAddGG5.correct

/-- `mp_add(a, b, a)`, growing `a` when it must. -/
def mpAddGA : HContract where
  P := Api.MpAddGA.P
  X := Option (Nat × MpInt)
  R := Api.MpAddGA.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Api.MpAddGA.all
  entry := Api.MpAddGA.entry
  args := Api.MpAddGA.args
  rets := Api.MpAddGA.rets
  lay := Api.MpAddGA.lay
  kind := Api.MpAddGA.kind
  out := Api.MpAddGA.out
  isW := Api.MpAddGA.isW
  ws := Api.MpAddGA.ws
  site := .aD
  site' := Api.MpAddGA.site'
  hin := Api.MpAddGA.hin
  hout := Api.MpAddGA.hout
  Res := Api.MpAddGA.Res
  Q := Api.MpAddGA.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩ <;> cases r <;> simp_all [Api.MpAddGA.out, Api.MpAddGA.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos;
    cases r with
    | stk => exact .inl (show 0 < Api.MpAddGA.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bS => exact .inl (show 0 < 24 by decide)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.MpAddGAG5.correct

/-- `mp_add(a, b, b)`, growing `b` when it must. -/
def mpAddGB : HContract where
  P := Api.MpAddGB.P
  X := Option (Nat × MpInt)
  R := Api.MpAddGB.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Api.MpAddGB.all
  entry := Api.MpAddGB.entry
  args := Api.MpAddGB.args
  rets := Api.MpAddGB.rets
  lay := Api.MpAddGB.lay
  kind := Api.MpAddGB.kind
  out := Api.MpAddGB.out
  isW := Api.MpAddGB.isW
  ws := Api.MpAddGB.ws
  site := .bD
  site' := Api.MpAddGB.site'
  hin := Api.MpAddGB.hin
  hout := Api.MpAddGB.hout
  Res := Api.MpAddGB.Res
  Q := Api.MpAddGB.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩ <;> cases r <;> simp_all [Api.MpAddGB.out, Api.MpAddGB.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos;
    cases r with
    | stk => exact .inl (show 0 < Api.MpAddGB.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bS => exact .inl (show 0 < 24 by decide)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.MpAddGBG5.correct

end Tom.Machine.Std
