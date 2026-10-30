import Tom.Machine.Fn.ToomSqrMainG
import Tom.Machine.Fn.GrowSubH
import Tom.Machine.Fn.Mul2HMainG
import Tom.Machine.Fn.MpSqrSMainG
import Tom.Machine.Fn.MpSqrSAMainG

/-!
# `s_mp_toom_sqr` with its callee premises discharged

The `Fn.ToomSqrG5.correct : Api.ToomSqrI.Statement` assumes `Api.ToomSqrI.Gaps`. Five of its
six fields are proved: the growing `mp_sub(a, b, c)` / `mp_sub(a, b, a)` (`Fn/GrowSubH.lean`), the
growing `mp_mul_2(a, a)` (`Fn.Mul2HG5.correct`), `mp_sqr(a, b)` / `mp_sqr(a, a)` below 120 digits
with no room (`Fn.MpSqrSG5.correct`, `Fn.MpSqrSAG5.correct`, over the growing `s_mp_sqr_fast`).
The sixth, `mulA : Api.MpMulA.Statement` (`mp_mul(a, b, a)`), stays a premise until the
multiplication group closes.
-/

namespace Tom.Machine.Fn.ToomSqrG5

open Tom.Machine.Api

/-- **`s_mp_toom_sqr(a, b)` on the machine**, given only `mp_mul(a, b, a)`'s contract. -/
theorem correctClosed (hA : MpMulA.Statement) : ToomSqr.Statement :=
  correct ⟨GrowSubH.mpSubH, GrowSubH.mpSubHA, Mul2HG5.correct, MpSqrSG5.correct, MpSqrSAG5.correct, hA⟩

end Tom.Machine.Fn.ToomSqrG5
