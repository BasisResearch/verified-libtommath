import Tom.Machine.Api.Std_r6g

/-!
# `mp_mul(a, b, c)`: what its generated assembly proves

`Api.MulRec.StatementI` (the contract with the induction hypothesis `ih : MulBelow μ`) with
the callees' contracts in the residue (`Gaps`, named premises): the three algorithms and the
growing fast multiplier. `stmtI` turns it into `StatementI` given the gaps. All four are proved
(`Fn.KMulG5.correct`, `Fn.BalMulG5.correct`, `Fn.ToomMulG5.correct`, `Fn.MulFastGG5.correct`),
discharged in `Fn/MulGroupK.lean`, `Fn/MulGroupT.lean`, `Fn/MulGroupB.lean`.
-/

namespace Tom.Machine.Api.MpMulG

open Tom.Machine Tom.Machine.Api

/-- The callees of `mp_mul` (named premises, proved: see the module doc). -/
structure Gaps : Prop where
  kmul : KMul.Statement
  bal : BalMul.Statement
  toom : ToomMul.Statement
  fast : MulFastH.Statement

structure Res (p : MpMul.P) : Prop extends MulRec.ResI p where
  gaps : Gaps

def Statement : Prop := ∀ p : MpMul.P, MpMul.SpecR Res p

theorem stmtI (h : Statement) (g : Gaps) : MulRec.StatementI :=
  fun p _ _ _ _ hra hres => h p hra { toResI := hres, gaps := g }

end Tom.Machine.Api.MpMulG
