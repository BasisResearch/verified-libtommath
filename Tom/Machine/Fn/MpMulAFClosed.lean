import Tom.Machine.Fn.MpMulAFMainG
import Tom.Machine.Fn.MulGroupB

/-!
# `mp_mul(a, b, a)` on the comba path, closed

`Fn.MpMulAFG5.correct` (`experiments/asm/mmulaf.asm.json`) under `MpMulGA`'s residue, discharged by
the closed multiplication group (`Fn/MulGroupB.lean`: the recursion hypothesis at every bound, the
in-place algorithms' contracts): the `alloc` bound of the mul group's contract gap in the form
`mp_reduce_2k_l` needs (`Api/MpMulAF.lean`).
-/

namespace Tom.Machine.Fn.MpMulAFClosed

open Tom.Machine.Api

/-- **`mp_mul(a, b, a)` on the comba path, `a->alloc` kept or grown**, no premises. -/
theorem correct : MpMulAF.Statement := fun p _ _ _ _ hra hres =>
  MpMulAFG5.correct p hra
    { toGA := { toAResI := { toRes := hres.res, ih := MulGroupB.mulBelow _ },
                gaps := MpMulAG5I.GapsA.full ⟨BalMulAG5.correct, ToomMulAG5.correct⟩ },
      small := hres.small }

end Tom.Machine.Fn.MpMulAFClosed
