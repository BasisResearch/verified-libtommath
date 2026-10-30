import Tom.Machine.Fn.MpSqrG5
import Tom.Machine.Fn.KSqrMainG
import Tom.Machine.Fn.KSqrAMainG

/-!
# The squaring group: `mp_sqr` with karatsuba proved

`mp_sqr(a, b)` and `mp_sqr(a, a)` from the generated assemblies of `mp_sqr` and
`s_mp_karatsuba_sqr` (both shapes), closed by `SqrRec.close`. What is left are named premises:
the growing `mp_add`/`mp_lshd` (`Api/MpAddH.lean`, `Api/MpLshdH.lean`) and `s_mp_toom_sqr`
(`Api/ToomSqr.lean`).
-/

namespace Tom.Machine.Fn.SqrGroup

open Tom.Machine.Api

/-- **`mp_sqr` on the machine**, given the growing `mp_add`, `mp_lshd` and toom's contracts. -/
theorem correct (hA : MpAddH.Statement) (hL : MpLshdH.Statement) (hT : ToomSqr.Statement)
    (hTA : ToomSqr.StatementA) : MpSqr.Statement ∧ MpSqrA.Statement :=
  MpSqrG5.correct_rec (KSqrG5.correct hA hL) (KSqrAG5.correct hA hL) hT hTA

end Tom.Machine.Fn.SqrGroup
