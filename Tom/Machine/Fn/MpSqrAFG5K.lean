import Tom.Machine.Api.MpSqrAF
import Tom.Machine.Fn.MpSqrG5K

/-! `mp_sqr(a, a)` on the comba path, growing: the Pre of the generated
`Fn/MpSqrAFMainG.lean` (`experiments/asm/msqraf.asm.json`, a variant of `msqra.asm.json`). -/

namespace Tom.Machine.Fn.MpSqrAFG5K

open Tom.Machine Tom.Machine.Api Tom.Machine.Std Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
open Tom.Machine.Api.MpSqrA (P isW kind hin)

/-- The Statement's hypotheses. -/
structure GPreAF (p : P) (m : Mem) (ra : BitVec 64) : Prop where
  ra4 : ra.toNat % 4 = 0
  res : MpSqrAF.Res p
  lay : Sound (MpSqrAF.lay p) isW
  bund : Bundle (MpSqrAF.lay p) (kind p) m
  heap : AHeap m (hin p)
  off : ∀ r, Off (MpSqrAF.lay p r) (hin p)

end Tom.Machine.Fn.MpSqrAFG5K
