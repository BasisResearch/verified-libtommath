import Tom.Machine.Api.MontRedGr
import Tom.Machine.Fn.MontRedGrMainG
import Tom.Machine.Api.MpReduce2kG
import Tom.Machine.Fn.MpReduce2kGMainG

/-!
`montRedGr`: `mp_montgomery_reduce(x, n, rho)` growing `x` on both paths (`Api/MontRedGr.lean`,
`Fn.MontRedGrG5.correct`): `s_mp_exptmod_fast`'s `redux` in mode 0 when `2 P->used + 1 ≥ MP_WARRAY` or
`P->used ≥ MP_MAXFAST` (its fast path tail-calls `Std.montRedFastG`, `Api/Std_capf.lean`).
`mpReduce2kG`: `mp_reduce_2k(a, n, d)` with `a` and `q` growing (`Api/MpReduce2kG.lean`,
`Fn.MpReduce2kGG5.correct`): `redux` in mode 2.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_montgomery_reduce(x, n, rho)`, `x` growing. -/
def montRedGr : HContract where
  P := Api.MpReduce2k.P
  X := Api.ReduxG.X
  R := Api.MpReduce2k.R
  all := [.stk, .aS, .aD, .nS, .nD, .code]
  hall := Api.MpReduce2k.all
  entry := Api.MontRedGr.entry
  args := Api.MpReduce2k.args
  rets := Api.ReduxG.rets
  lay := Api.MontRedGr.lay
  kind := Api.MpReduce2k.kind
  out := Api.ReduxG.out
  isW := Api.MpReduce2k.isW
  ws := Api.MpReduce2k.ws
  site := .aD
  site' := Api.ReduxG.site'
  hin := Api.ReduxG.hin
  hout := Api.ReduxG.hout
  Res := Api.MontRedGr.Res
  Q := Api.MontRedGr.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    obtain ⟨ok, q, a'⟩ := x
    cases r <;> simp_all [Api.ReduxG.out, Api.MpReduce2k.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := MpInt.alloc_pos_of_mag h.vn (Tom.MontRedStep.npos h.x_lt)
    cases r with
    | stk => exact .inl (show 0 < Api.MontRedGr.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | nD => exact .inl (show 0 < 4 * p.n.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := Fn.MontRedGrG5.correct

/-- `mp_reduce_2k(a, n, d)`, `a` and `q` growing. -/
def mpReduce2kG : HContract where
  P := Api.MpReduce2k.P
  X := Api.ReduxG.X
  R := Api.MpReduce2k.R
  all := [.stk, .aS, .aD, .nS, .nD, .code]
  hall := Api.MpReduce2k.all
  entry := Api.MpReduce2kG.entry
  args := Api.MpReduce2k.args
  rets := Api.ReduxG.rets
  lay := Api.MpReduce2kG.lay
  kind := Api.MpReduce2k.kind
  out := Api.ReduxG.out
  isW := Api.MpReduce2k.isW
  ws := Api.MpReduce2k.ws
  site := .aD
  site' := Api.ReduxG.site'
  hin := Api.ReduxG.hin
  hout := Api.ReduxG.hout
  Res := Api.MpReduce2kG.Res
  Q := Api.MpReduce2kG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    obtain ⟨ok, q, a'⟩ := x
    cases r <;> simp_all [Api.ReduxG.out, Api.MpReduce2k.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := MpInt.alloc_pos_of_mag h.vn h.npos
    cases r with
    | stk => exact .inl (show 0 < Api.MpReduce2kG.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | nD => exact .inl (show 0 < 4 * p.n.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := Fn.MpReduce2kGG5.correct

end Tom.Machine.Std
