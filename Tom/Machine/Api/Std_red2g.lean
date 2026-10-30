import Tom.Machine.Api.MpSqrAF
import Tom.Machine.Fn.MpSqrAFMainG

/-!
`mpSqrAF`: `mp_sqr(a, a)` on the comba path growing `a` (`Api/MpSqrAF.lean`, `Fn.MpSqrAFG5.correct`):
`s_mp_exptmod`'s squarings on `mp_init`'s 32-digit `mp_int`s for a modulus of fewer than 120 digits.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_sqr(a, a)` on the comba path, growing `a`. -/
def mpSqrAF : HContract where
  P := Api.MpSqrA.P
  X := Api.MpSqr.X
  R := Api.MpSqrA.R
  all := [.stk, .aS, .aD, .ks, .ts, .km, .tm, .code]
  hall := Api.MpSqrA.all
  entry := Api.MpSqr.entry
  args := Api.MpSqrA.args
  rets := Api.MpSqrA.rets
  lay := Api.MpSqrAF.lay
  kind := Api.MpSqrA.kind
  out := Api.MpSqrA.out
  isW := Api.MpSqrA.isW
  ws := Api.MpSqrA.ws
  site := .aD
  site' := Api.MpSqrA.site'
  hin := Api.MpSqrA.hin
  hout := Api.MpSqrA.hout
  Res := Api.MpSqrAF.Res
  Q := Api.MpSqrA.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    obtain ⟨ok, q, a'⟩ := x
    cases r <;> simp_all [Api.MpSqrA.out, Api.MpSqrA.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos
    cases r with
    | stk => exact .inl (show 0 < 2768 + 8 * p.a.used by omega)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 4 by decide)
  spec := Fn.MpSqrAFG5.correct _

end Tom.Machine.Std
