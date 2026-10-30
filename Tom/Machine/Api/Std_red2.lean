import Tom.Machine.Api.Expt2G
import Tom.Machine.Fn.Expt2GMainG

/-!
`mp2exptG`: `mp_2expt(a, b)` growing `a` (`Api/Expt2G.lean`, `Fn.Expt2GG5.correct`), for
`mp_reduce_setup(&mu, P)` and `mp_reduce_2k_setup_l(P, &mu)`'s `tmp` on a general modulus.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_2expt(a, b)`, growing `a` when it must. -/
def mp2exptG : HContract where
  P := Api.Expt2G.P
  X := Option (Nat × MpInt)
  R := Api.Expt2G.R
  all := [.stk, .aS, .aD, .code]
  hall := Api.Expt2G.all
  entry := Api.Expt2G.entry
  args := Api.Expt2G.args
  rets := Api.Expt2G.rets
  lay := Api.Expt2G.lay
  kind := Api.Expt2G.kind
  out := Api.Expt2G.out
  isW := Api.Expt2G.isW
  ws := Api.Expt2G.ws
  site := .aD
  site' := Api.Expt2G.site'
  hin := Api.Expt2G.hin
  hout := Api.Expt2G.hout
  Res := Api.Expt2G.Res
  Q := Api.Expt2G.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, a'⟩ <;> cases r <;> simp_all [Api.Expt2G.out, Api.Expt2G.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos
    cases r with
    | stk => exact .inl (show 0 < Api.Expt2G.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.Expt2GG5.correct

end Tom.Machine.Std
