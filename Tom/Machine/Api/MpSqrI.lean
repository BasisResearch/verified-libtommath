import Tom.Machine.Api.KSqr
import Tom.Machine.Api.ToomSqr

/-!
# What `mp_sqr`'s generated assemblies prove

`mp_sqr`'s contracts given the induction hypothesis (`SqrRec.StatementI`, `StatementAI`), with
the algorithms it dispatches to as named premises (their Statements; `Api/Std_r6h.lean` carries
them in the callee residue), discharged by `Fn.MulGroupB.sqrCorrect`'s closure. `SqrRec.close` turns the pair
into `Api.MpSqr.Statement ∧ Api.MpSqrA.Statement`.
-/

namespace Tom.Machine.Api.MpSqrI

/-- `mp_sqr(a, b)` given the hypothesis, from karatsuba's and toom's contracts. -/
def Statement : Prop := KSqr.Statement → ToomSqr.Statement → SqrRec.StatementI

end Tom.Machine.Api.MpSqrI

namespace Tom.Machine.Api.MpSqrAI

/-- `mp_sqr(a, a)` given the hypothesis, from karatsuba's and toom's in-place contracts. -/
def Statement : Prop := KSqr.StatementA → ToomSqr.StatementA → SqrRec.StatementAI

end Tom.Machine.Api.MpSqrAI
