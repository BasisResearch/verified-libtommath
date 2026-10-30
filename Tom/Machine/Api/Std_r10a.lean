import Tom.Machine.Fn.MpDivRMainG
import Tom.Machine.Fn.MpDivQMainG
import Tom.Machine.Api.Std_r8a
import Tom.Machine.Api.Std_grow6A

/-!
# The callee contracts

* `mpDivR`: `mp_div(a, b, NULL, d)` (`Api/MpDivR.lean`, `Fn.MpDivRG5.correct`), for `mp_mod`;
  `mpDivRP`, `mpAddGP`: with the site's placement in `Q` (`HContract.wp`, `Api/Std_r8a.lean`);
* `mpDivQH`: `mp_div(a, b, a, NULL)` (`Api/MpDivQ.lean`, `Fn.MpDivQG5.correct`), for `mp_reduce_setup`.
-/

namespace Tom.Machine.Std

open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc

/-- `mp_div(a, b, NULL, d)`: the remainder in `d`, its digits re-placed. -/
def mpDivR : HContract where
  P := Api.MpDivR.P
  X := Api.MpDivR.Out
  R := Api.MpDivR.R
  all := [.stk, .aS, .aD, .bS, .bD, .dS, .dD, .code]
  hall := Api.MpDivR.all
  entry := Api.MpDivR.entry
  args := Api.MpDivR.args
  rets := Api.MpDivR.rets
  lay := Api.MpDivR.lay
  kind := Api.MpDivR.kind
  out := Api.MpDivR.out
  isW := Api.MpDivR.isW
  ws := Api.MpDivR.ws
  site := .dD
  site' := Api.MpDivR.site'
  hin := Api.MpDivR.hin
  hout := Api.MpDivR.hout
  Res := Api.MpDivR.Res
  Q := Api.MpDivR.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | _ | _ <;> cases r <;> simp_all [Api.MpDivR.out, Api.MpDivR.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.dpos; have := h.bnz; have := h.vb.used_le
    cases r with
    | stk => exact .inl (show 0 < Api.MpDivR.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | dD => exact .inl (show 0 < 4 * p.d.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := Fn.MpDivRG5.correct

/-- `mp_div(a, b, NULL, d)` with the placement of `d`'s digits in `Q`. -/
def mpDivRP : HContract := mpDivR.wp

/-- `mp_add(a, b, c)` growing `c`, with the placement of `c`'s digits in `Q`. -/
def mpAddGP : HContract := mpAddG.wp

/-- `mp_div(a, b, a, NULL)`: the quotient in `a`, its digits re-placed. -/
def mpDivQH : HContract where
  P := Api.MpDivQ.P
  X := Api.MpDivQ.Out
  R := Api.MpDivQ.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Api.MpDivQ.all
  entry := Api.MpDivQ.entry
  args := Api.MpDivQ.args
  rets := Api.MpDivQ.rets
  lay := Api.MpDivQ.lay
  kind := Api.MpDivQ.kind
  out := Api.MpDivQ.out
  isW := Api.MpDivQ.isW
  ws := Api.MpDivQ.ws
  site := .aD
  site' := Api.MpDivQ.site'
  hin := Api.MpDivQ.hin
  hout := Api.MpDivQ.hout
  Res := Api.MpDivQ.Res
  Q := Api.MpDivQ.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with _ | _ <;> cases r <;> simp_all [Api.MpDivQ.out, Api.MpDivQ.kind, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bnz; have := h.vb.used_le
    cases r with
    | stk => exact .inl (show 0 < Api.MpDivQ.F by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by omega)
    | code => exact .inl (show 0 < textLen by decide)
    | _ => exact .inl (show 0 < 24 by decide)
  spec := Fn.MpDivQG5.correct

end Tom.Machine.Std
