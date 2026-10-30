import Tom.Machine.Api.DrReduceG
import Tom.Machine.Fn.DrReduceGMainG
import Tom.Machine.Kit.Placed
import Tom.Machine.Api.MontRedFastG
import Tom.Machine.Fn.MontRedFastGMainG

/-!
`drReduceG`: `mp_dr_reduce(x, n, k)` growing `x` (`Api/DrReduceG.lean`, `Fn.DrReduceGG5.correct`):
`s_mp_exptmod_fast`'s `redux` in mode 1 on a general modulus.
`montRedFastG`: `s_mp_montgomery_reduce_fast(x, n, rho)` growing `x` (`Api/MontRedFastG.lean`,
`Fn.MontRedFastGG5.correct`): `redux` in mode 0 for `2 P->used + 1 < MP_WARRAY`, `P->used < MP_MAXFAST`. Regions, parameters and the allocating
frame are `Api/ReduxG.lean`'s (`Api/MpReduce2k.lean`'s regions, `x` re-placed).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_dr_reduce(x, n, k)`, `x` growing. -/
def drReduceG : HContract where
  P := Api.MpReduce2k.P
  X := Api.ReduxG.X
  R := Api.MpReduce2k.R
  all := [.stk, .aS, .aD, .nS, .nD, .code]
  hall := Api.MpReduce2k.all
  entry := Api.DrReduceG.entry
  args := Api.MpReduce2k.args
  rets := Api.ReduxG.rets
  lay := Api.DrReduceG.lay
  kind := Api.MpReduce2k.kind
  out := Api.ReduxG.out
  isW := Api.MpReduce2k.isW
  ws := Api.MpReduce2k.ws
  site := .aD
  site' := Api.ReduxG.site'
  hin := Api.ReduxG.hin
  hout := Api.ReduxG.hout
  Res := Api.DrReduceG.Res
  Q := Api.DrReduceG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    obtain ⟨ok, q, a'⟩ := x
    cases r <;> simp_all [Api.ReduxG.out, Api.MpReduce2k.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := MpInt.alloc_pos_of_mag h.vn h.npos
    cases r with
    | stk => exact .inl (show 0 < Api.DrReduceG.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | nD => exact .inl (show 0 < 4 * p.n.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := Fn.DrReduceGG5.correct

/-- `s_mp_montgomery_reduce_fast(x, n, rho)`, `x` growing. -/
def montRedFastG : HContract where
  P := Api.MpReduce2k.P
  X := Api.ReduxG.X
  R := Api.MpReduce2k.R
  all := [.stk, .aS, .aD, .nS, .nD, .code]
  hall := Api.MpReduce2k.all
  entry := Api.MontRedFastG.entry
  args := Api.MpReduce2k.args
  rets := Api.ReduxG.rets
  lay := Api.MontRedFastG.lay
  kind := Api.MpReduce2k.kind
  out := Api.ReduxG.out
  isW := Api.MpReduce2k.isW
  ws := Api.MpReduce2k.ws
  site := .aD
  site' := Api.ReduxG.site'
  hin := Api.ReduxG.hin
  hout := Api.ReduxG.hout
  Res := Api.MontRedFastG.Res
  Q := Api.MontRedFastG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    obtain ⟨ok, q, a'⟩ := x
    cases r <;> simp_all [Api.ReduxG.out, Api.MpReduce2k.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := MpInt.alloc_pos_of_mag h.vn (Tom.MontRedStep.npos h.x_lt)
    cases r with
    | stk => exact .inl (show 0 < Api.MontRedFastG.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | nD => exact .inl (show 0 < 4 * p.n.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := Fn.MontRedFastGG5.correct

end Tom.Machine.Std
