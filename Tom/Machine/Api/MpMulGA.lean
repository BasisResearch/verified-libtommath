import Tom.Machine.Api.Std_r9a

/-!
# `mp_mul(a, b, a)`: what its generated assembly proves

`Api.MulRec.StatementAI` (the in-place contract under the induction hypothesis) with the in-place
callees in the residue (`Gaps`, named premises). `stmtAI` turns it into `StatementAI`. All five
are proved (`Fn.KMulAG5.correct`, `Fn.BalMulAG5.correct`, `Fn.ToomMulAG5.correct`,
`Fn.SMpMulDigsAG5.correct`, `Fn.MulFastGAG5.correct`), discharged in `Fn/MulGroupA.lean`,
`Fn/MulGroupT.lean`, `Fn/MulGroupB.lean`.
-/

namespace Tom.Machine.Api.MpMulGA

open Tom.Machine Tom.Machine.Api

/-- The in-place callees of `mp_mul(a, b, a)` (named premises, proved: see the module doc). -/
structure Gaps : Prop where
  kmulA : KMulA.Statement
  balA : BalMulA.Statement
  toomA : ToomMulA.Statement
  digsA : SMpMulDigsA.Statement
  fastA : MulFastHA.Statement

structure Res (p : MpMulA.P) : Prop extends MulRec.AResI p where
  gaps : Gaps

def Statement : Prop := ∀ p : MpMulA.P, MpMulA.SpecR Res p

theorem stmtAI (h : Statement) (g : Gaps) : MulRec.StatementAI :=
  fun p _ _ _ _ hra hres => h p hra { toAResI := hres, gaps := g }

end Tom.Machine.Api.MpMulGA
