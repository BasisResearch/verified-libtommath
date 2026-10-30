import Tom.Machine.Api.Reduce2kSetupLG
import Tom.Machine.Fn.Reduce2kSetupLGMainG

/-!
`red2kSetupLG`: `mp_reduce_2k_setup_l(a, d)` growing `d` (`Api/Reduce2kSetupLG.lean`,
`Fn.Reduce2kSetupLGG5.correct`), for `s_mp_exptmod`'s `mp_reduce_2k_setup_l(P, &mu)` on a general
modulus.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_reduce_2k_setup_l(a, d)`, growing `d`. -/
def red2kSetupLG : HContract where
  P := Api.Reduce2kSetupL.P
  X := Option (Nat × MpInt)
  R := Api.Reduce2kSetupL.R
  all := [.stk, .aS, .aD, .dS, .dD, .code]
  hall := Api.Reduce2kSetupL.all
  entry := Api.Reduce2kSetupL.entry
  args := Api.Reduce2kSetupL.args
  rets := Api.Reduce2kSetupLG.rets
  lay := Api.Reduce2kSetupLG.lay
  kind := Api.Reduce2kSetupLG.kind
  out := Api.Reduce2kSetupLG.out
  isW := Api.Reduce2kSetupL.isW
  ws := Api.Reduce2kSetupL.ws
  site := .dD
  site' := Api.Reduce2kSetupLG.site'
  hin := Api.Reduce2kSetupLG.hin
  hout := Api.Reduce2kSetupLG.hout
  Res := Api.Reduce2kSetupLG.Res
  Q := Api.Reduce2kSetupLG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, d'⟩ <;> cases r <;>
      simp_all [Api.Reduce2kSetupLG.out, Api.Reduce2kSetupL.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.dpos
    cases r with
    | stk => exact .inl (show 0 < Api.Reduce2kSetupLG.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | dD => exact .inl (show 0 < 4 * p.d.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := Fn.Reduce2kSetupLGG5.correct

end Tom.Machine.Std
