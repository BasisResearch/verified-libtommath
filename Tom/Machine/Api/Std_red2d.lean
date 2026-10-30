import Tom.Machine.Api.MpCopyG
import Tom.Machine.Fn.MpCopyGMainG
import Tom.Machine.Api.Std_r6g

/-!
`mpCopyGP`: `mp_copy(a, b)` growing `b` (`Api/MpCopyG.lean`, `Fn.MpCopyGG5.correct`), with `b`'s
placement in the result (`HContract.withPlace`), for `mp_div_2d(a, b, c, a)`'s `mp_copy(a, c)`.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_copy(a, b)`, growing `b` when it must. -/
def mpCopyG : HContract where
  P := Api.MpCopyG.P
  X := Option (Nat × MpInt)
  R := Api.MpCopyG.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Api.MpCopyG.all
  entry := Api.MpCopyG.entry
  args := Api.MpCopyG.args
  rets := Api.MpCopyG.rets
  lay := Api.MpCopyG.lay
  kind := Api.MpCopyG.kind
  out := Api.MpCopyG.out
  isW := Api.MpCopyG.isW
  ws := Api.MpCopyG.ws
  site := .bD
  site' := Api.MpCopyG.site'
  hin := Api.MpCopyG.hin
  hout := Api.MpCopyG.hout
  Res := Api.MpCopyG.Res
  Q := Api.MpCopyG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, b'⟩ <;> cases r <;> simp_all [Api.MpCopyG.out, Api.MpCopyG.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos
    cases r with
    | stk => exact .inl (show 0 < Api.MpCopyG.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := Fn.MpCopyGG5.correct

/-- `mp_copy(a, b)` growing `b`, with `b`'s placement in the result. -/
def mpCopyGP : HContract := mpCopyG.withPlace

end Tom.Machine.Std
