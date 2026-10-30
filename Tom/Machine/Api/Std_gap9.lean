import Tom.Machine.Fn.SqrFastHMainG
import Tom.Machine.Fn.SqrFastHAMainG
import Tom.Machine.Fn.Div3NMainG
import Tom.Machine.Api.Std_multi8

/-!
* `sqrFastG`, `sqrFastGA`: `s_mp_sqr_fast(a, b)` and `s_mp_sqr_fast(a, a)` growing the destination
  (`Api/SqrFastH.lean`, `Api/SqrFastHA.lean`; `Fn.SqrFastHG5.correct`, `Fn.SqrFastHAG5.correct`),
  site the destination's digits, results `(ok, q, b')` with `SqrAlg.Out` (as `mp_sqr`'s
  algorithms), stack 2752: what `mp_sqr` calls below `KARATSUBA_SQR_CUTOFF` with no room.
* `sMpDiv3N`: `s_mp_div_3(a, a, NULL)` (`Api/Div3N.lean`, `Fn.Div3NG5.correct`), site `a`'s digits, stack
  656: `s_mp_toom_mul`'s `s_mp_div_3(&S2, &S2, NULL)`.
-/

namespace Tom.Machine.Std

open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc

/-- `s_mp_sqr_fast(a, b)`, growing `b` when it must. -/
def sqrFastG : HContract where
  P := Api.SqrFastH.P
  X := Api.MpSqr.X
  R := Api.Two.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Api.Two.all
  entry := Api.SqrFastH.entry
  args := Api.SqrFastH.args
  rets := Api.SqrFastH.rets
  lay := Api.SqrFastH.lay
  kind := Api.SqrFastH.kind
  out := Api.SqrFastH.out
  isW := Api.Two.isW
  ws := Api.Two.ws
  site := .bD
  site' := Api.SqrFastH.site'
  hin := Api.SqrFastH.hin
  hout := Api.SqrFastH.hout
  Res := Api.SqrFastH.Res
  Q := Api.SqrFastH.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, q, c'⟩; cases r <;> simp_all [Api.SqrFastH.out, Api.SqrFastH.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos
    cases r with
    | stk => exact .inl (show 0 < Api.SqrFastH.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bS => exact .inl (show 0 < 24 by decide)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.SqrFastHG5.correct

/-- `s_mp_sqr_fast(a, a)`, growing `a` when it must. -/
def sqrFastGA : HContract where
  P := Api.SqrFastHA.P
  X := Api.MpSqr.X
  R := Api.Un.R
  all := [.stk, .aS, .aD, .code]
  hall := Api.Un.all
  entry := Api.SqrFastHA.entry
  args := Api.SqrFastHA.args
  rets := Api.SqrFastHA.rets
  lay := Api.SqrFastHA.lay
  kind := Api.SqrFastHA.kind
  out := Api.SqrFastHA.out
  isW := Api.Un.isW
  ws := Api.Un.ws
  site := .aD
  site' := Api.SqrFastHA.site'
  hin := Api.SqrFastHA.hin
  hout := Api.SqrFastHA.hout
  Res := Api.SqrFastHA.Res
  Q := Api.SqrFastHA.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, q, c'⟩; cases r <;> simp_all [Api.SqrFastHA.out, Api.SqrFastHA.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos
    cases r with
    | stk => exact .inl (show 0 < Api.SqrFastHA.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.SqrFastHAG5.correct

/-- `s_mp_div_3(a, a, NULL)` as an allocating contract. -/
def sMpDiv3N : HContract where
  P := Api.Div3N.P
  X := Option (Nat × MpInt)
  R := Api.Div3N.R
  all := [.stk, .aS, .aD, .code]
  hall := Api.Div3N.all
  entry := Fn.Div3.entry
  args := Api.Div3N.args
  rets := Api.Div3N.rets
  lay := Api.Div3N.lay
  kind := Api.Div3N.kind
  out := Api.Div3N.out
  isW := Api.Div3N.isW
  ws := Api.Div3N.ws
  site := .aD
  site' := Api.Div3N.site'
  hin := Api.Div3N.hin
  hout := Api.Div3N.hout
  Res := Api.Div3N.Res
  Q := Api.Div3N.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | ⟨q, c'⟩ <;> cases r <;> simp_all [Api.Div3N.out, Api.Div3N.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos
    cases r with
    | stk => exact .inl (show 0 < Api.Div3N.F by decide)
    | aS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := Fn.Div3NG5.correct

/-- The arity `s_mp_toom_mul` needs (`mp_init_multi(&S1, &S2, &T1, NULL)`), at its instance. -/
example : mpInitMulti3 = mpInitMultiN 3 := rfl
example : mpClearMulti3 = mpClearMultiN 3 := rfl

end Tom.Machine.Std
