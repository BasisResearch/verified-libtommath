import Tom.Machine.Fn.SqrGroup
import Tom.Machine.Fn.GrowH

/-!
# The squaring group with the growing callees discharged

`Fn.SqrGroup.correct` with its premises `MpAddH.Statement` and `MpLshdH.Statement`
proved. Left: `s_mp_toom_sqr`
(`Api/ToomSqr.lean`, both shapes).
-/

namespace Tom.Machine.Fn.SqrGroupH

open Tom.Machine.Api

/-- **`mp_sqr` on the machine** (both shapes), given only toom's contracts. -/
theorem correct (hT : ToomSqr.Statement) (hTA : ToomSqr.StatementA) : MpSqr.Statement ∧ MpSqrA.Statement :=
  SqrGroup.correct GrowH.mpAddH GrowH.mpLshdH hT hTA

end Tom.Machine.Fn.SqrGroupH
