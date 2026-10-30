import Tom.Machine.Fn.MpDivDIMainG

/-! `mp_div_d(a, b, a, d)` in place on the machine: `Fn.MpDivDIG5.correct : Api.MpDivDI.Statement`
(generated, `Fn/MpDivDIMainG.lean`), and the allocating contract `Std.mpDivDI` for its callers
(`mp_to_radix`'s `mp_div_d(&t, radix, &t, &d)`). -/

namespace Tom.Machine.Std

open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.MpDivDI

/-- `mp_div_d(a, b, a, d)` as an allocating contract: the site is `a`'s digit array. -/
def mpDivDI : HContract where
  P := Api.MpDivDI.P
  X := Option (Nat × MpInt)
  R := Api.MpDivDI.R
  all := [.stk, .aS, .aD, .dS, .code]
  hall := Api.MpDivDI.all
  entry := Api.MpDivDI.entry
  args := Api.MpDivDI.args
  rets := Api.MpDivDI.rets
  lay := Api.MpDivDI.lay
  kind := Api.MpDivDI.kind
  out := Api.MpDivDI.out
  isW := Api.MpDivDI.isW
  ws := Api.MpDivDI.ws
  site := .aD
  site' := Api.MpDivDI.site'
  hin := Api.MpDivDI.hin
  hout := Api.MpDivDI.hout
  Res := Api.MpDivDI.Res
  Q := Api.MpDivDI.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩ <;> cases r <;> simp_all [Api.MpDivDI.out, Api.MpDivDI.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos
    cases r with
    | stk => exact .inl (show 0 < Api.MpDivDI.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | dS => exact .inl (show 0 < 4 by decide)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.MpDivDIG5.correct

end Tom.Machine.Std
