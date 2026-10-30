import Tom.Machine.Fn.MpDivDMainG

/-! `mp_div_d` on the machine: `Fn.MpDivDG5.correct : Api.MpDivD.Statement` (generated,
`Fn/MpDivDMainG.lean`), and the allocating contract `Std.mpDivD` for its callers. -/

namespace Tom.Machine.Std

open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.MpDivD

/-- `mp_div_d` as an allocating contract (for `mp_to_radix`-style callers). -/
def mpDivD : HContract where
  P := Api.MpDivD.P
  X := Option (Nat × MpInt)
  R := Api.MpDivD.R
  all := [.stk, .aS, .aD, .cS, .cD, .dS, .code]
  hall := Api.MpDivD.all
  entry := Api.MpDivD.entry
  args := Api.MpDivD.args
  rets := Api.MpDivD.rets
  lay := Api.MpDivD.lay
  kind := Api.MpDivD.kind
  out := Api.MpDivD.out
  isW := Api.MpDivD.isW
  ws := Api.MpDivD.ws
  site := .cD
  site' := Api.MpDivD.site'
  hin := Api.MpDivD.hin
  hout := Api.MpDivD.hout
  Res := Api.MpDivD.Res
  Q := Api.MpDivD.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩ <;> cases r <;> simp_all [Api.MpDivD.out, Api.MpDivD.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.cpos
    cases r with
    | stk => exact .inl (show 0 < Api.MpDivD.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | cS => exact .inl (show 0 < 24 by decide)
    | cD => exact .inl (show 0 < 4 * p.c.alloc by omega)
    | dS => exact .inl (show 0 < 4 by decide)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.MpDivDG5.correct

end Tom.Machine.Std
