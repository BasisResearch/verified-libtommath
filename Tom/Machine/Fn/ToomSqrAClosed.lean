import Tom.Machine.Fn.ToomSqrAMainG
import Tom.Machine.Fn.ToomSqrClosed

/-!
# `s_mp_toom_sqr(a, a)` with its callee premises discharged

`Fn.ToomSqrAG5.correct : Api.ToomSqrAI.Statement` (generated from `tsqra.asm.json`, the in-place
variant of `tsqr.asm.json`) assumes `Api.ToomSqrI.Gaps`; as for `b` distinct (`ToomSqrClosed.lean`)
five of its six fields are proved, and `mp_mul(a, b, a)`'s contract stays a premise.
-/

namespace Tom.Machine.Fn.ToomSqrAG5

open Tom.Machine.Api

/-- **`s_mp_toom_sqr(a, a)` on the machine**, given only `mp_mul(a, b, a)`'s contract. -/
theorem correctClosed (hA : MpMulA.Statement) : ToomSqr.StatementA :=
  correct ⟨GrowSubH.mpSubH, GrowSubH.mpSubHA, Mul2HG5.correct, MpSqrSG5.correct, MpSqrSAG5.correct, hA⟩

end Tom.Machine.Fn.ToomSqrAG5
