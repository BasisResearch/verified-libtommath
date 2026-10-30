import Tom.Machine.Fn.MpSubGBMainG
import Tom.Machine.Kit.GrowBridge

/-!
# The growing `mp_sub(a, b, b)` read as values

`Api.MpSubHB.Statement` (result `(ok, q, x)`, value `a − b`) from `Fn.MpSubGBG5.correct`
(generated from `msubgb.asm.json`, the `b` variant of `msubg.asm.json`), as `Fn/GrowSubH.lean`
reads `mp_sub(a, b, a)`: `GrowPost.val` (Kit/GrowBridge.lean), the value by `SubG.specB`.
-/

namespace Tom.Machine.Fn.GrowSubHB

open Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Api Tom.Machine.Api.Heap

/-- **The growing `mp_sub(a, b, b)`**, read as values. -/
theorem mpSubHB : MpSubHB.Statement := fun {p _ _ _ _} hra hres hS hB hH hoff =>
  Triple.rmap (fun _ h => GrowPost.val (n0 := p.b.alloc) (V := p.a.val - p.b.val) (fun r => r) p.bdp
      (p.b.withSign (subSign p.a p.b)) ⟨hres.vb.toShape.withSign _, hres.bpos, Nat.le_refl _⟩ hres.bpos
      (fun _ _ hq => SubG.specB hres.va hres.vb hres.size_lt hq)
      (fun _ h => ⟨h.shape, h.pos, h.place, h.grow, h.valid, h.val⟩) h)
    (Fn.MpSubGBG5.correct hra hres hS hB hH hoff)

end Tom.Machine.Fn.GrowSubHB
