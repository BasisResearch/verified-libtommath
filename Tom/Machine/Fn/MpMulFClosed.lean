import Tom.Machine.Fn.MpMulFMainG
import Tom.Machine.Fn.MulGroupB

/-!
# `mp_mul(a, b, c)` on the comba path, closed

`Fn.MpMulFG5.correct` (`experiments/asm/mmulf.asm.json`) under `MpMulG`'s residue, discharged by the
closed multiplication group (`Fn/MulGroupB.lean`: the recursion hypothesis at every bound;
`Fn/MulGroupK.lean`: karatsuba and the growing fast multiplier; balance and toom): the distinct-
destination twin of `Fn/MpMulAFClosed.lean` (`Api/MpMulF.lean`).
-/

namespace Tom.Machine.Fn.MpMulFClosed

open Tom.Machine.Api

/-- **`mp_mul(a, b, c)` on the comba path, `c->alloc` kept or grown**, no premises. -/
theorem correct : MpMulF.Statement := fun p _ _ _ _ hra hres =>
  MpMulFG5.correct p hra
    { toG := { toResI := { toResU := hres.res.toU, ih := MulGroupB.mulBelow _ },
               gaps := MulGroupK.Gaps.full ⟨BalMulG5.correct, ToomMulG5.correct⟩ },
      small := hres.small }

end Tom.Machine.Fn.MpMulFClosed
