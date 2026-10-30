import Tom.Machine.Api.MpSqrAG
import Tom.Machine.Fn.MpSqrAFMainG
import Tom.Machine.Fn.MulGroupB

/-!
# `mp_sqr(a, a)` at any size, growing `a`, closed

By cases on `KARATSUBA_SQR_CUTOFF`: below it the comba path's growing contract
(`Fn.MpSqrAFG5.correct`); at and above it the closed group's in-place contract
(`Fn.MulGroupB.sqrCorrect.2`, `room` vacuous), through `Api/MpSqrAG.lean`'s bridges `Spec.ofComba`/`Spec.ofGroup`.
-/

namespace Tom.Machine.Fn.MpSqrAGClosed

open Tom.Machine Tom.Machine.Api

/-- **`mp_sqr(a, a)` at any size, growing `a`**, no premises. -/
theorem correct : MpSqrAG.Statement := fun p => if hs : p.a.used < 120
  then MpSqrAG.Spec.ofComba hs MpSqrAFG5.correct
  else MpSqrAG.Spec.ofGroup hs MulGroupB.sqrCorrect.2

end Tom.Machine.Fn.MpSqrAGClosed
