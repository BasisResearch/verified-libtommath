import Tom.Machine.Api.MpReduceSetupG
import Tom.Machine.Fn.MpReduceSetupGMainG
import Tom.Machine.Api.Std_grow6
import Tom.Machine.Api.Std_r6g

/-!
`mpReduceSetupG`: `mp_reduce_setup(a, b)` growing `a` (`Api/MpReduceSetupG.lean`,
`Fn.MpReduceSetupGG5.correct`), for `s_mp_exptmod`'s `mp_reduce_setup(&mu, P)` on a general modulus.
`sSubGP`: `Std.sSubG` with the placement of `c`'s block in `Q` (`HContract.withPlace`), for
`mp_reduce_2k_setup_l(a, d)`, which re-places its own `d` by it.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_reduce_setup(a, b)`, growing `a`. -/
def mpReduceSetupG : HContract where
  P := Api.MpReduceSetup.P
  X := Api.MpReduceSetupG.Out
  R := Api.MpReduceSetup.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Api.MpReduceSetup.all
  entry := Api.MpReduceSetup.entry
  args := Api.MpReduceSetup.args
  rets := Api.MpReduceSetupG.rets
  lay := Api.MpReduceSetup.lay
  kind := Api.MpReduceSetup.kind
  out := Api.MpReduceSetupG.out
  isW := Api.MpReduceSetup.isW
  ws := Api.MpReduceSetup.ws
  site := .aD
  site' := Api.MpReduceSetupG.site'
  hin := Api.MpReduceSetupG.hin
  hout := Api.MpReduceSetupG.hout
  Res := Api.MpReduceSetupG.Res
  Q := Api.MpReduceSetupG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    cases r <;> simp_all [Api.MpReduceSetupG.out, Api.MpReduceSetup.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.b0; have := h.vb.used_le
    cases r with
    | stk => exact .inl (show 0 < Api.MpReduceSetup.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := Fn.MpReduceSetupGG5.correct

/-- `s_mp_sub(a, b, c)` growing `c`, with `c`'s placement in the result. -/
def sSubGP : HContract := sSubG.withPlace

end Tom.Machine.Std
