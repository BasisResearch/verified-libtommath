import Tom.Machine.Api.Std_redB
import Tom.Machine.Fn.SMpMulDigsAGClosed

/-!
# `mp_reduce`'s in-place multipliers on both paths as callee contracts
-/

namespace Tom.Machine.Std

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

def sMpMulHighDigsG0 : HContract := { mulHighFastHA with
  entry := SMpMulHighDigs.entry
  Res := SMpMulHighDigsG.Res
  Q := SMpMulHighDigsG.Q
  pos p h r := by
    cases r with
    | stk => exact .inl (show 0 < MulHighFastHA.F by decide)
    | aS | bS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.apos; omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.bpos; omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := fun hra hres => Fn.SMpMulDigsAGClosed.highCorrect hra hres }

def sMpMulHighDigsGP : HContract := sMpMulHighDigsG0.withPlace

def sMpMulDigsAG0 : HContract := { mulFastHA with
  entry := SMpMulDigs.entry
  Res := SMpMulDigsAG.Res
  Q := SMpMulDigsAG.Q
  pos p h r := by
    cases r with
    | stk => exact .inl (show 0 < MulFastHA.F by decide)
    | aS | bS => exact .inl (show 0 < 24 by decide)
    | aD => exact .inl (show 0 < 4 * p.a.alloc by have := h.apos; omega)
    | bD => exact .inl (show 0 < 4 * p.b.alloc by have := h.bpos; omega)
    | code => exact .inl (show 0 < textLen by decide)
  spec := fun hra hres => Fn.SMpMulDigsAGClosed.digsCorrect hra hres }

def sMpMulDigsAGP : HContract := sMpMulDigsAG0.withPlace

end Tom.Machine.Std
