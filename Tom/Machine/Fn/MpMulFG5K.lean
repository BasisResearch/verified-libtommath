import Tom.Machine.Api.MpMulF
import Tom.Machine.Fn.MpMulG5K

/-! `mp_mul(a, b, c)` on the comba path: the Pre of the generated `Fn/MpMulFMainG.lean`
(`experiments/asm/mmulf.asm.json`) and its exit's `Q` (`MpMulG5K.post_fast` with `grow`). -/

namespace Tom.Machine.Fn.MpMulFG5K

open Tom.Machine Tom.Machine.Api Tom.Machine.Std Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
open Tom.Machine.Api.MpMul (P)

/-- The Statement's hypotheses. -/
structure MPreF (p : P) (m : Mem) (ra : BitVec 64) : Prop where
  ra4 : ra.toNat % 4 = 0
  res : Api.MpMulGF.Res p
  lay : Sound (MpMul.lay p) MpMul.isW
  bund : Bundle (MpMul.lay p) (MpMul.kind p) m
  heap : AHeap m (MpMul.hin p)
  off : ∀ r, Off (MpMul.lay p r) (MpMul.hin p)

variable {p : P}

theorem postF (h : Api.MpMulGF.Res p) {ok : Bool} {c1 : MpInt} (hq : MulFastH.Out (MpMulG5K.digsP p) ok c1) :
    MpMulF.Out p ok (withSign p.a p.b c1) :=
  ⟨MpMulG5K.post_fast h.toG hq, hq.grow⟩

end Tom.Machine.Fn.MpMulFG5K
