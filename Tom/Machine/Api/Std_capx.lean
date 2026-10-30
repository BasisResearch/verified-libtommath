import Tom.Machine.Api.MpAbsG
import Tom.Machine.Fn.MpAbsGMainG

/-!
`mpAbsGH`: `mp_abs(a, b)` growing `b` (`Api/MpAbsG.lean`, `Fn.MpAbsGG5.correct`), for `mp_exptmod`'s
`mp_abs(X, &tmpX)` into a temporary of `mp_init_multi`.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_abs(a, b)`, growing `b` when it must. -/
def mpAbsGH : HContract where
  P := Api.MpAbsG.P
  X := Option (Nat × MpInt)
  R := Api.MpAbsG.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Api.MpAbsG.all
  entry := Api.MpAbsG.entry
  args := Api.MpAbsG.args
  rets := Api.MpAbsG.rets
  lay := Api.MpAbsG.lay
  kind := Api.MpAbsG.kind
  out := Api.MpAbsG.out
  isW := Api.MpAbsG.isW
  ws := Api.MpAbsG.ws
  site := .bD
  site' := Api.MpAbsG.site'
  hin := Api.MpAbsG.hin
  hout := Api.MpAbsG.hout
  Res := Api.MpAbsG.Res
  Q := Api.MpAbsG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, b'⟩ <;> cases r <;> simp_all [Api.MpAbsG.out, Api.MpAbsG.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos
    cases r with
    | stk => exact .inl (show 0 < Api.MpAbsG.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := Fn.MpAbsGG5.correct

end Tom.Machine.Std
