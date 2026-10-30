import Tom.Machine.Api.Reduce2kSetupGr
import Tom.Machine.Fn.Reduce2kSetupGrMainG

/-!
`red2kSetupG`: `mp_reduce_2k_setup(a, &d)` with `tmp` growing (`Api/Reduce2kSetupGr.lean`,
`Fn.Reduce2kSetupGrG5.correct`): `s_mp_exptmod_fast`'s setup in mode 2 without `MP_PREC` room on `P`.
Regions, parameters and outcome are `Api/Reduce2kSetup.lean`'s (as `Std.red2kSetupH`).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_reduce_2k_setup(a, &d)`, `tmp` growing. -/
def red2kSetupG : HContract where
  P := Reduce2kSetup.P
  X := Option Nat
  R := Reduce2kSetup.R
  all := [.stk, .aS, .aD, .dD, .code]
  hall := Reduce2kSetup.all
  entry := Reduce2kSetup.entry
  args := Reduce2kSetup.args
  rets := Reduce2kSetup.rets
  lay := Reduce2kSetupGr.lay
  kind := Reduce2kSetup.kind
  out := Reduce2kSetup.out
  isW := Reduce2kSetup.isW
  ws := Reduce2kSetup.ws
  site := .dD
  site' p _ := Reduce2kSetupGr.lay p .dD
  hin := Reduce2kSetup.hin
  hout p _ := Reduce2kSetup.hin p
  Res := Reduce2kSetupGr.Res
  Q := Reduce2kSetup.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | _ <;> cases r <;> simp_all [Reduce2kSetup.out, Reduce2kSetup.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos
    cases r with
    | stk => exact .inl (show 0 < Reduce2kSetupGr.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | dD => exact .inl (show 0 < 4 * 1 by decide)
    | code => exact .inl (show 0 < textLen by decide)
    | aS => exact .inl (show 0 < 24 by decide)
  spec := Fn.Reduce2kSetupGrG5.correct

end Tom.Machine.Std
