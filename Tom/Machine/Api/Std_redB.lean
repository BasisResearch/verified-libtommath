import Tom.Machine.Api.Std_red
import Tom.Machine.Api.Std_r9a
import Tom.Machine.Fn.SMpMulHighDigsAFMainG
import Tom.Machine.Fn.SMpMulDigsAFMainG

/-!
# `mp_reduce`'s in-place multipliers as callee contracts

`s_mp_mul_high_digs(a, b, a, digs)` and `s_mp_mul_digs(a, b, a, digs)` on their fast paths, growing
(`Api/SMpMulHighDigsAF.lean`, `Api/SMpMulDigsAF.lean`, proved by `Fn.SMpMulHighDigsAFG5.correct`,
`Fn.SMpMulDigsAFG5.correct`), with the placement added to `Q` (`HContract.withPlace`): `mp_reduce`
keeps its temporary `q`'s block fresh across the re-placements.
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

def sMpMulHighDigsAF0 : HContract := { mulHighFastHA with
  entry := SMpMulHighDigs.entry
  spec := fun hra hres => Fn.SMpMulHighDigsAFG5.correct hra hres }

def sMpMulHighDigsAFP : HContract := sMpMulHighDigsAF0.withPlace

def sMpMulDigsAF0 : HContract := { mulFastHA with
  Res := SMpMulDigsAF.Res
  entry := SMpMulDigs.entry
  pos p h r := by
    cases r with
    | stk => exact .inl (show 0 < MulFastHA.F by decide)
    | aS | bS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.apos; omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.bpos; omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := fun hra hres => Fn.SMpMulDigsAFG5.correct hra hres }

def sMpMulDigsAFP : HContract := sMpMulDigsAF0.withPlace

end Tom.Machine.Std
