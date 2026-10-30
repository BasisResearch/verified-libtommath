import Tom.Machine.Api.MpMulGAF
import Tom.Machine.Fn.MpMulAG5K

/-! `mp_mul(a, b, a)` on the comba path: the Pre of the generated `Fn/MpMulAFMainG.lean`
(`experiments/asm/mmulaf.asm.json`) and its exit's `Q` (`MpMulAG5K.outA` with `grow`). -/

namespace Tom.Machine.Fn.MpMulAFG5K

open Tom.Machine Tom.Machine.Api Tom.Machine.Std Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
open Tom.Machine.Api.MpMulA (P)

/-- The Statement's hypotheses. -/
structure MPreAF (p : P) (m : Mem) (ra : BitVec 64) : Prop where
  ra4 : ra.toNat % 4 = 0
  res : Api.MpMulGAF.Res p
  lay : Sound (MpMulA.lay p) MpMulA.isW
  bund : Bundle (MpMulA.lay p) (MpMulA.kind p) m
  heap : AHeap m (MpMulA.hin p)
  off : ∀ r, Off (MpMulA.lay p r) (MpMulA.hin p)

variable {p : P}

theorem outAF (h : Api.MpMulGAF.Res p) {ok : Bool} {c1 : MpInt} (hs : c1.Shape) (hp : 0 < c1.alloc)
    (ht : ok = true → 0 < c1.used → c1.digit (c1.used - 1) ≠ 0) (hm : ok = true → c1.mag = p.a.mag * p.b.mag)
    (hg : p.a.alloc ≤ c1.alloc) : MpMulAF.Out p ok (withSign p.a p.b c1) :=
  ⟨MpMulAG5K.outA h.toGA hs hp ht hm, hg⟩

end Tom.Machine.Fn.MpMulAFG5K
