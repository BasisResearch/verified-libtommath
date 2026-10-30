import Tom.Machine.Api.Std_t7
import Tom.Machine.Fn.GrowSubHB
import Tom.Machine.Fn.Mul2HDMainG

/-!
# Callee contracts of `s_mp_toom_mul`

* `mpSubHBv`: the growing `mp_sub(a, b, b)` read as values (`Api/MpSubGB.lean`'s `MpSubHB`,
  `Fn.GrowSubHB.mpSubHB` from `msubgb.asm.json`): `mp_sub(&a2, &a1, &a1)`, `mp_sub(&b2, &b1, &b1)`,
  `mp_sub(&S1, &a1, &a1)`.
* `mul2HDv`: the growing `mp_mul_2(a, b)`, `b` distinct (`Api/Mul2HD.lean`,
  `Fn.Mul2HDG5.correct` from `mul2hd.asm.json`): `mp_mul_2(&b1, &T1)`.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

def mpSubHBv : HContract where
  P := MpAddGB.P
  X := MpSqr.X
  R := MpAddGB.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := MpAddGB.all
  entry := MpSubHB.entry
  args := MpAddGB.args
  rets := MpAddHB.rets
  lay := MpAddGB.lay
  kind := MpAddGB.kind
  out := MpAddHB.out
  isW := MpAddGB.isW
  ws := MpAddGB.ws
  site := .bD
  site' := MpAddHB.site'
  hin := MpAddGB.hin
  hout := MpAddHB.hout
  Res := MpAddGB.Res
  Q := MpSubHB.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MpAddHB.out, MpAddGB.kind, MpAddGB.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos
    left
    cases r with
    | code => exact (show 0 < textLen by decide)
    | stk => exact (show 0 < MpAddGB.F by decide)
    | aS | bS => exact (show 0 < 24 by decide)
    | aD => exact (show 0 < 4 * p.a.alloc by omega)
    | bD => exact (show 0 < 4 * p.b.alloc by omega)
  spec := fun hra hres => Fn.GrowSubHB.mpSubHB hra hres

def mul2HDv : HContract where
  P := Mul2HD.P
  X := MpSqr.X
  R := Two.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := Two.all
  entry := Mul2HD.entry
  args := Mul2HD.args
  rets := Mul2HD.rets
  lay := Mul2HD.lay
  kind := Mul2HD.kind
  out := Mul2HD.out
  isW := Two.isW
  ws := Two.ws
  site := .bD
  site' := Mul2HD.site'
  hin := Mul2HD.hin
  hout := Mul2HD.hout
  Res := Mul2HD.Res
  Q := Mul2HD.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [Mul2HD.out, Mul2HD.kind, Two.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    have := h.apos; have := h.bpos
    left
    cases r with
    | code => exact (show 0 < textLen by decide)
    | stk => exact (show 0 < 576 by decide)
    | aS | bS => exact (show 0 < 24 by decide)
    | aD => exact (show 0 < 4 * p.a.alloc by omega)
    | bD => exact (show 0 < 4 * p.b.alloc by omega)
  spec := fun hra hres => Fn.Mul2HDG5.correct hra hres

end Tom.Machine.Std
