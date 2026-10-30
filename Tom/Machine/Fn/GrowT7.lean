import Tom.Machine.Fn.MpAddGAMainG
import Tom.Machine.Fn.MpAddGBMainG
import Tom.Machine.Api.MpAddHA
import Tom.Spec.GrowAStep
import Tom.Machine.Kit.GrowBridge

/-!
`Api.MpAddHA.Statement` / `Api.MpAddHB.Statement` from `Fn.MpAddGAG5.correct` /
`Fn.MpAddGBG5.correct`: `none` ↦ `(false, the old block, the destination with the code's sign)`, `some (q, x)` ↦
`(true, q, x)`, the value by `AddG.specA` / `AddG.specB`, through `GrowPost.val` (`Kit/GrowBridge.lean`).
-/

namespace Tom.Machine.Fn.GrowT7

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
  Tom.Machine.Std

/-- **`mp_add(a, b, a)` with growth, read as values.** -/
theorem mpAddHA : MpAddHA.Statement := fun {p _ _ _ _} hra hres hS hB hH hoff =>
  Triple.rmap (fun _ h => GrowPost.val (n0 := p.a.alloc) (V := p.a.val + p.b.val) (fun r => r) p.adp (p.a.withSign (addSign p.a p.b)) ⟨hres.va.toShape.withSign _, hres.apos, Nat.le_refl _⟩
      hres.apos (fun _ _ hq => AddG.specA hres.va hres.vb hres.size_lt hq)
      (fun _ h => ⟨h.shape, h.pos, h.place, h.grow, h.valid, h.val⟩) h)
    (Fn.MpAddGAG5.correct hra hres hS hB hH hoff)

/-- **`mp_add(a, b, b)` with growth, read as values.** -/
theorem mpAddHB : MpAddHB.Statement := fun {p _ _ _ _} hra hres hS hB hH hoff =>
  Triple.rmap (fun _ h => GrowPost.val (n0 := p.b.alloc) (V := p.a.val + p.b.val) (fun r => r) p.bdp (p.b.withSign (addSign p.a p.b)) ⟨hres.vb.toShape.withSign _, hres.bpos, Nat.le_refl _⟩
      hres.bpos (fun _ _ hq => AddG.specB hres.va hres.vb hres.size_lt hq)
      (fun _ h => ⟨h.shape, h.pos, h.place, h.grow, h.valid, h.val⟩) h)
    (Fn.MpAddGBG5.correct hra hres hS hB hH hoff)

end Tom.Machine.Fn.GrowT7
