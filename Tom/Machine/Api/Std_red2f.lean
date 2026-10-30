import Tom.Machine.Api.MpReduce2kLG
import Tom.Machine.Fn.MpReduce2kLGMainG

/-!
`mpReduce2kLG`: `mp_reduce_2k_l(a, n, d)` with `a` and `q` growing (`Api/MpReduce2kLG.lean`,
`Fn.MpReduce2kLGG5.correct`): `s_mp_exptmod`'s `redux` in mode 1 on a general modulus.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- `mp_reduce_2k_l(a, n, d)`, `a` and `q` growing. -/
def mpReduce2kLG : HContract where
  P := Api.MpReduce2kL.P
  X := Api.MpReduce2kLG.X
  R := Api.MpReduce2kL.R
  all := [.stk, .aS, .aD, .nS, .nD, .dS, .dD, .kc, .tc, .code]
  hall := Api.MpReduce2kL.all
  entry := Api.MpReduce2kL.entry
  args := Api.MpReduce2kL.args
  rets := Api.MpReduce2kLG.rets
  lay := Api.MpReduce2kLG.lay
  kind := Api.MpReduce2kL.kind
  out := Api.MpReduce2kLG.out
  isW := Api.MpReduce2kL.isW
  ws := Api.MpReduce2kL.ws
  site := .aD
  site' := Api.MpReduce2kLG.site'
  hin := Api.MpReduce2kLG.hin
  hout := Api.MpReduce2kLG.hout
  Res := Api.MpReduce2kLG.Res
  Q := Api.MpReduce2kLG.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    obtain ⟨ok, q, a'⟩ := x
    cases r <;> simp_all [Api.MpReduce2kLG.out, Api.MpReduce2kL.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.dpos; have := MpInt.alloc_pos_of_mag h.vn h.npos
    cases r with
    | stk => exact .inl (show 0 < Api.MpReduce2kLG.F (p := p) by unfold Api.MpReduce2kLG.F; omega)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | nD => exact .inl (show 0 < 4 * p.n.alloc by omega)
    | dD => exact .inl (show 0 < 4 * p.d.alloc by omega)
    | kc | tc => exact .inl (show 0 < 4 by decide)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := Fn.MpReduce2kLGG5.correct

end Tom.Machine.Std
