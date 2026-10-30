import Tom.Machine.Fn.MpSqrMainG
import Tom.Machine.Fn.MpSqrAMainG

/-!
# `mp_sqr` on the machine

The two generated assemblies (`MpSqrG5.correct : Api.MpSqrI.Statement`,
`MpSqrAG5.correct : Api.MpSqrAI.Statement`) closed by the strong induction of
`Api/SqrRec.lean`: both `mp_sqr` contracts, from karatsuba's and toom's (named premises).
-/

namespace Tom.Machine.Fn.MpSqrG5

open Tom.Machine.Api

/-- **`mp_sqr(a, b)` and `mp_sqr(a, a)` on the machine**, given the algorithms' contracts. -/
theorem correct_rec (hK : KSqr.Statement) (hKA : KSqr.StatementA) (hT : ToomSqr.Statement)
    (hTA : ToomSqr.StatementA) : MpSqr.Statement ∧ MpSqrA.Statement :=
  SqrRec.close (correct hK hT) (MpSqrAG5.correct hKA hTA)

end Tom.Machine.Fn.MpSqrG5
