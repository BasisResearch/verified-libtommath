import Tom.Machine.Api.Std_r6g

/-!
# `mp_mul(a, b, c)`: what its generated assembly proves

`Api.MulRec.StatementI` (the contract with the induction hypothesis `ih : MulBelow μ`) with
the contracts of the callees that are not proved yet in the residue (`Gaps`): the three
algorithms and the growing fast multiplier. `stmtI` turns it into `StatementI` given the gaps.
-/

namespace Tom.Machine.Api.MpMulG

open Tom.Machine Tom.Machine.Api

/-- The callees of `mp_mul` without a proof (named premises). -/
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
