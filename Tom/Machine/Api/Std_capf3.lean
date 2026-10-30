import Tom.Machine.Api.MulDGA
import Tom.Machine.Fn.MulDGAMainG

/-!
`mulDGA`: `mp_mul_d(a, b, a)` in place, growing `a` (`Api/MulDGA.lean`, `Fn.MulDGAG5.correct`):
`mp_reduce_2k`'s `mp_mul_d(&q, d, &q)` on a `q` that `mp_div_2d` may have filled to its block.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_mul_d(a, b, a)`, `a` growing. -/
def mulDGA : HContract where
  P := Api.MulDGA.P
  X := Option (Nat × MpInt)
  R := Api.MpLshdG.R
  all := [.stk, .aS, .aD, .code]
  hall := Api.MpLshdG.all
  entry := Api.MulDGA.entry
  args := Api.MulDGA.args
  rets := Api.MulDGA.rets
  lay := Api.MulDGA.lay
  kind := Api.MulDGA.kind
  out := Api.MulDGA.out
  isW := Api.MulDGA.isW
  ws := Api.MulDGA.ws
  site := .aD
  site' := Api.MulDGA.site'
  hin := Api.MulDGA.hin
  hout := Api.MulDGA.hout
  Res := Api.MulDGA.Res
  Q := Api.MulDGA.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, a'⟩ <;> cases r <;> simp_all [Api.MulDGA.out, Api.MulDGA.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos
    cases r with
    | stk => exact .inl (show 0 < Api.MulDGA.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | aS => exact .inl (show 0 < 24 by decide)
  spec := Fn.MulDGAG5.correct

end Tom.Machine.Std
