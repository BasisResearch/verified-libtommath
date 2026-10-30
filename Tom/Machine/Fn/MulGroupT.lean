import Tom.Machine.Fn.MulGroupA
import Tom.Machine.Fn.ToomMulMainG
import Tom.Machine.Fn.ToomMulAMainG
import Tom.Machine.Fn.ToomSqrAClosed

/-!
# The multiplication and squaring groups with toom proved

`Fn/MulGroupA.lean`'s two closures (`MulGroupK.correctFull`, `SqrGroupH.correctFull`) with the
toom premises discharged: `Fn.ToomMulG5.correct : ToomMul.Statement` (`tmul.asm.json`),
`Fn.ToomMulAG5.correct : ToomMulA.Statement` (`tmula.asm.json`, its in-place variant) and
`Fn.ToomSqrAG5.correctClosed : MpMulA.Statement → ToomSqr.StatementA` (`tsqra.asm.json`). Only
`s_mp_balance_mul`'s two contracts stay premises.
-/

namespace Tom.Machine.Fn.MulGroupT

open Tom.Machine.Api

/-- The premises left: `s_mp_balance_mul(a, b, c)` and `s_mp_balance_mul(a, b, a)`. -/
structure GapsFull : Prop where
  bal : BalMul.Statement
  balA : BalMulA.Statement

theorem GapsFull.mul (g : GapsFull) : MulGroupK.GapsFull :=
  ⟨g.bal, ToomMulG5.correct, ⟨g.balA, ToomMulAG5.correct⟩⟩

/-- **`mp_mul(a, b, c)` and `mp_mul(a, b, a)` on the machine**, given balance's two contracts. -/
theorem mulCorrectFull (g : GapsFull) : MpMul.Statement ∧ MpMulA.Statement :=
  MulGroupK.correctFull g.mul

/-- **`mp_sqr(a, b)` and `mp_sqr(a, a)` on the machine**, given balance's two contracts. -/
theorem sqrCorrectFull (g : GapsFull) : MpSqr.Statement ∧ MpSqrA.Statement :=
  SqrGroupH.correctFull ⟨g.mul, ToomSqrAG5.correctClosed (mulCorrectFull g).2⟩

end Tom.Machine.Fn.MulGroupT
