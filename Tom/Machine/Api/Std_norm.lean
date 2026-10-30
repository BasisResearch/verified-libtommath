import Tom.Machine.Api.MontNormG
import Tom.Machine.Fn.MontNormGMainG
import Tom.Machine.Kit.Placed

/-!
`montNormG`: `mp_montgomery_calc_normalization(a, b)` growing `a` (`Api/MontNormG.lean`,
`Fn.MontNormGG5.correct`), for `s_mp_exptmod_fast`'s `res` (from `mp_init_size(&res, P->alloc)`).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_montgomery_calc_normalization(a, b)`, growing `a` when it must. -/
def montNormG : HContract where
  P := Api.MontNormG.P
  X := Api.MontNormG.X
  R := Api.MontNormG.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Api.MontNormG.all
  entry := Api.MontNormG.entry
  args := Api.MontNormG.args
  rets := Api.MontNormG.rets
  lay := Api.MontNormG.lay
  kind := Api.MontNormG.kind
  out := Api.MontNormG.out
  isW := Api.MontNormG.isW
  ws := Api.MontNormG.ws
  site := .aD
  site' := Api.MontNormG.site'
  hin := Api.MontNormG.hin
  hout := Api.MontNormG.hout
  Res := Api.MontNormG.Res
  Q := Api.MontNormG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [Api.MontNormG.out, Api.MontNormG.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := MpInt.alloc_pos_of_mag h.vb (by have := h.gt1; omega)
    cases r with
    | stk => exact .inl (show 0 < Api.MontNormG.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bS => exact .inl (show 0 < 24 by decide)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.MontNormGG5.correct

end Tom.Machine.Std
