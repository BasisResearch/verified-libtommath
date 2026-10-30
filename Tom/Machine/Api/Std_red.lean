import Tom.Machine.Api.Std_r6g
import Tom.Machine.Fn.MulHighFastGAMainG

/-!
# Callee contracts of `mp_reduce`'s in-place multipliers

`s_mp_mul_high_digs_fast(a, b, a, digs)` with growth (`Api/MulHighFastHA.lean`, proved by
`Fn.MulHighFastGAG5.correct`) as an `HContract`, for the tail call of
`s_mp_mul_high_digs(a, b, a, digs)` on its fast path (`experiments/asm/mhdigsaf.asm.json`).
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

def mulHighFastHA : HContract where
  P := SMpMulHighDigs.P
  X := MpMul.X
  R := SMpMulHighDigs.R
  all := [.stk, .aS, .aD, .bS, .bD, .code]
  hall := SMpMulHighDigs.all
  entry := MulHighFastHA.entry
  args := SMpMulHighDigs.args
  rets := MulHighFastHA.rets
  lay := MulHighFastHA.lay
  kind := SMpMulHighDigs.kind
  out := MulHighFastHA.out
  isW := SMpMulHighDigs.isW
  ws := SMpMulHighDigs.ws
  site := .aD
  site' := MulHighFastHA.site'
  hin := MulHighFastHA.hin
  hout := MulHighFastHA.hout
  Res := MulHighFastHA.Res
  Q := MulHighFastHA.Q
  fits p r := by cases r <;> first | trivial | exact Iv.sub_self _
  site_ws := by decide
  site_w := rfl
  out_ind p x r hr hs h := by
    rcases x with ⟨_, _, _⟩; cases r <;> simp_all [MulHighFastHA.out, SMpMulHighDigs.kind, SMpMulHighDigs.ws, Kind.isRam, Kind.indep]
  pos p h r := by
    cases r with
    | stk => exact .inl (show 0 < MulHighFastHA.F by decide)
    | aS | bS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.apos; omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.bpos; omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := fun hra hres => Fn.MulHighFastGAG5.correct hra hres

end Tom.Machine.Std
