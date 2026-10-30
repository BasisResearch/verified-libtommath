import Tom.Machine.Fn.Div3IMainG

/-!
# The callee contracts

* `sMpDiv3I`: `s_mp_div_3(a, a, d)` in place (`Api/Div3I.lean`, `Fn.Div3IG5.correct`), as an
  allocating contract: the site is `a`'s digit array.
-/

namespace Tom.Machine.Std

open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Div3I

/-- `s_mp_div_3(a, a, d)` as an allocating contract (for `mp_div_d(a, 3, a, d)`). -/
def sMpDiv3I : HContract where
  P := Api.Div3I.P
  X := Option (Nat × MpInt)
  R := Api.Div3I.R
  all := [.stk, .aS, .aD, .dS, .code]
  hall := Api.Div3I.all
  entry := Fn.Div3.entry
  args := Api.Div3I.args
  rets := Api.Div3I.rets
  lay := Api.Div3I.lay
  kind := Api.Div3I.kind
  out := Api.Div3I.out
  isW := Api.Div3I.isW
  ws := Api.Div3I.ws
  site := .aD
  site' := Api.Div3I.site'
  hin := Api.Div3I.hin
  hout := Api.Div3I.hout
  Res := Api.Div3I.Res
  Q := Api.Div3I.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩ <;> cases r <;> simp_all [Api.Div3I.out, Api.Div3I.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.dd1
    cases r with
    | stk => exact .inl (show 0 < Api.Div3I.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | dS => exact .inl (show 0 < 4 * p.dd.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.Div3IG5.correct

end Tom.Machine.Std
