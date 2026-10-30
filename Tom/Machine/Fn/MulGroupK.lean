import Tom.Machine.Fn.MpMulG5
import Tom.Machine.Fn.KMulMainG
import Tom.Machine.Fn.MulFastGMainG

/-!
# The multiplication group with karatsuba and the growing fast multiplier proved

`Fn.MpMulG5I` (`mp_mul(a, b, c)` under the induction hypothesis, given `Api.MpMulG.Gaps`)
with the gaps `kmul` (`Fn.KMulG5.correct`, `s_mp_karatsuba_mul`, `Fn/KMulMainG.lean`) and `fast`
(`Fn.MulFastGG5.correct`, `s_mp_mul_digs_fast` with growth, `Fn/MulFastGMainG.lean`) discharged.
Left: `s_mp_balance_mul`, `s_mp_toom_mul`, and `mp_mul(a, b, a)`.
-/

namespace Tom.Machine.Fn.MulGroupK

open Tom.Machine.Api

/-- The gaps of `mp_mul` left: balance and toom. -/
structure Gaps : Prop where
  bal : BalMul.Statement
  toom : ToomMul.Statement

theorem Gaps.full (g : Gaps) : MpMulG.Gaps := ⟨Fn.KMulG5.correct, g.bal, g.toom, Fn.MulFastGG5.correct⟩

/-- **`mp_mul(a, b, c)` under the induction hypothesis**, karatsuba and the fast multiplier proved. -/
theorem correctI (g : Gaps) : MulRec.StatementI := Fn.MpMulG5I.correctI g.full

/-- **`mp_mul(a, b, c)`**, karatsuba and the fast multiplier proved, given the other gaps and the in-place contract. -/
theorem correct (g : Gaps) (hA : MulRec.StatementAI) : MpMul.Statement := Fn.MpMulG5I.correct g.full hA

end Tom.Machine.Fn.MulGroupK
