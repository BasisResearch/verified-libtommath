import Tom.Machine.Fn.MpMulMainG

/-! `mp_mul(a, b, c)` on the machine: the generated assembly (`Fn/MpMulMainG.lean`, over
`Api/MpMulG.lean`) read back as `Api.MulRec.StatementI` (the contract under the induction
hypothesis), given the callees without a proof (`Api.MpMulG.Gaps`: karatsuba, balance, toom,
the growing fast multiplier). With `MulRec.StatementAI` (`mp_mul(a, b, a)`, not yet proved)
`MulRec.close` gives `Api.MpMul.Statement`. -/

namespace Tom.Machine.Fn.MpMulG5I

/-- **`mp_mul(a, b, c)` under the induction hypothesis**, given the named premises. -/
theorem correctI (g : Api.MpMulG.Gaps) : Api.MulRec.StatementI := Api.MpMulG.stmtI Fn.MpMulG5.correct g

/-- **`mp_mul(a, b, c)`**, given the named premises and the in-place contract under the hypothesis. -/
theorem correct (g : Api.MpMulG.Gaps) (hA : Api.MulRec.StatementAI) : Api.MpMul.Statement :=
  (Api.MulRec.close (correctI g) hA).1

end Tom.Machine.Fn.MpMulG5I
