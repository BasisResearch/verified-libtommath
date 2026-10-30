import Tom.Machine.Fn.MpMulAMainG
import Tom.Machine.Fn.MulGroupK
import Tom.Machine.Fn.SqrGroupH
import Tom.Machine.Fn.ToomSqrClosed
import Tom.Machine.Fn.SMpMulDigsAMainG
import Tom.Machine.Fn.MulFastGAMainG
import Tom.Machine.Fn.KMulAMainG

/-!
# `mp_mul(a, b, a)` and the closures of the multiplication and squaring groups

`Fn.MpMulAG5.correct : Api.MpMulGA.Statement` (generated, `experiments/asm/mmula.asm.json`, the
in-place variant of `mmul.asm.json`) read back as `Api.MulRec.StatementAI` given the in-place
callees (`Api.MpMulGA.Gaps`), of which karatsuba and the two schoolbook multipliers are proved:
`Fn.KMulAG5.correct` (`s_mp_karatsuba_mul(a, b, a)`, `kmula.asm.json`),
`Fn.SMpMulDigsAG5.correct` (`s_mp_mul_digs(a, b, a)`, `smdigsa.asm.json`) and
`Fn.MulFastGAG5.correct` (the growing `s_mp_mul_digs_fast(a, b, a)`, `mfastga.asm.json`); balance
and toom in place stay premises.
-/

namespace Tom.Machine.Fn.MpMulAG5I

open Tom.Machine.Api

/-- **`mp_mul(a, b, a)` under the induction hypothesis**, given its in-place callees. -/
theorem correctAI (g : MpMulGA.Gaps) : MulRec.StatementAI := MpMulGA.stmtAI Fn.MpMulAG5.correct g

/-- The in-place algorithms: the premises of `mp_mul(a, b, a)` left. -/
structure GapsA : Prop where
  balA : BalMulA.Statement
  toomA : ToomMulA.Statement

theorem GapsA.full (g : GapsA) : MpMulGA.Gaps :=
  ⟨Fn.KMulAG5.correct, g.balA, g.toomA, Fn.SMpMulDigsAG5.correct, Fn.MulFastGAG5.correct⟩

/-- **`mp_mul(a, b, a)` under the induction hypothesis**, given the in-place algorithms. -/
theorem correctAI' (g : GapsA) : MulRec.StatementAI := correctAI g.full

end Tom.Machine.Fn.MpMulAG5I

namespace Tom.Machine.Fn.MulGroupK

open Tom.Machine.Api

/-- The multiplication group's premises left: balance and toom (`c` distinct), and the in-place
algorithms of `mp_mul(a, b, a)`. -/
structure GapsFull : Prop where
  bal : BalMul.Statement
  toom : ToomMul.Statement
  inpl : Fn.MpMulAG5I.GapsA

/-- **`mp_mul(a, b, c)` and `mp_mul(a, b, a)` on the machine**, given the premises left. -/
theorem correctFull (g : GapsFull) : MpMul.Statement ∧ MpMulA.Statement :=
  MulRec.close (correctI ⟨g.bal, g.toom⟩) (Fn.MpMulAG5I.correctAI' g.inpl)

end Tom.Machine.Fn.MulGroupK

namespace Tom.Machine.Fn.SqrGroupH

open Tom.Machine.Api

/-- The squaring group's premises left: the multiplication group's, and `s_mp_toom_sqr(a, a)`. -/
structure GapsFull : Prop where
  mul : MulGroupK.GapsFull
  toomA : ToomSqr.StatementA

/-- **`mp_sqr(a, b)` and `mp_sqr(a, a)` on the machine**, given the premises left. -/
theorem correctFull (g : GapsFull) : MpSqr.Statement ∧ MpSqrA.Statement :=
  correct (ToomSqrG5.correctClosed (MulGroupK.correctFull g.mul).2) g.toomA

end Tom.Machine.Fn.SqrGroupH
