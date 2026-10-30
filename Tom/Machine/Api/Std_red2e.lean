import Tom.Machine.Api.MpDiv2dRG
import Tom.Machine.Fn.MpDiv2dRGMainG
import Tom.Machine.Api.Std_r6g
import Tom.Machine.Api.Std_grow6

/-!
`div2dRGP`: `mp_div_2d(a, b, c, a)` growing `c` (`Api/MpDiv2dRG.lean`, `Fn.MpDiv2dRGG5.correct`) and
`sAddGAP`: `Std.sAddGA`, each with its site's placement in the result
(`HContract.withPlace`), for `mp_reduce_2k_l`'s `mp_div_2d(a, p, &q, a)` and `s_mp_add(a, &q, a)` on a
general modulus.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_div_2d(a, b, c, a)`, growing `c` when it must. -/
def div2dRG : HContract where
  P := Api.MpDiv2dRG.P
  X := Api.MpDiv2dRG.X
  R := Api.MpDiv2dRG.R
  all := [.stk, .aS, .aD, .cS, .cD, .code]
  hall := Api.MpDiv2dRG.all
  entry := Api.MpDiv2dRG.entry
  args := Api.MpDiv2dRG.args
  rets := Api.MpDiv2dRG.rets
  lay := Api.MpDiv2dRG.lay
  kind := Api.MpDiv2dRG.kind
  out := Api.MpDiv2dRG.out
  isW := Api.MpDiv2dRG.isW
  ws := Api.MpDiv2dRG.ws
  site := .cD
  site' := Api.MpDiv2dRG.site'
  hin := Api.MpDiv2dRG.hin
  hout := Api.MpDiv2dRG.hout
  Res := Api.MpDiv2dRG.Res
  Q := Api.MpDiv2dRG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, a', c'⟩ <;> cases r <;>
      simp_all [Api.MpDiv2dRG.out, Api.MpDiv2dRG.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.cpos
    cases r with
    | stk => exact .inl (show 0 < Api.MpDiv2dRG.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | cD => exact .inl (show 0 < 4 * p.c.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := Fn.MpDiv2dRGG5.correct

/-- `mp_div_2d(a, b, c, a)` growing `c`, with `c`'s placement in the result. -/
def div2dRGP : HContract := div2dRG.withPlace

/-- `s_mp_add(a, b, a)` growing `a`, with `a`'s placement in the result. -/
def sAddGAP : HContract := sAddGA.withPlace

end Tom.Machine.Std
