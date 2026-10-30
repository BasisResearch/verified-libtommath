import Tom.Machine.Fn.MpSubGMainG
import Tom.Machine.Fn.MpSubGAMainG
import Tom.Machine.Fn.GrowH
import Tom.Machine.Api.MpSubH
import Tom.Machine.Kit.GrowBridge

/-!
# The growing `mp_sub`s read as values

`Api/MpSubH.lean` states the growing
`mp_sub(a, b, c)` and `mp_sub(a, b, a)` with result `(ok, q, x)` and the value `a − b`;
`Api/MpSubG.lean` proves them (`Fn.MpSubGG5.correct`, `Fn.MpSubGAG5.correct`, generated from
`msubg.asm.json` / `msubga.asm.json`) with result `Option (q, x)` and the branch posts over the
grown destination.
-/

namespace Tom.Machine.Fn.GrowSubH

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
  Tom.Machine.Std
open Tom.Machine.Fn.GrowH (rAdd pAdd)

/-- **The growing `mp_sub(a, b, c)`**. -/
theorem mpSubH : MpSubH.Statement := by
  intro p m v outp ra hra hres hS hB hH hoff
  obtain ⟨hres', hS', hB', hoff'⟩ := GrowH.pullAdd hres hS hB hoff
  exact Triple.rmap (fun _ h => GrowPost.val (n0 := p.c.alloc) (V := p.a.val - p.b.val) rAdd p.cdp
      (p.c.withSign (subSign p.a p.b)) ⟨hres.sc.withSign _, hres.cpos, Nat.le_refl _⟩ hres.cpos
      (fun _ _ hq => SubG.spec hres.va hres.vb hres.sc hres'.size_lt hq)
      (fun _ h => ⟨h.shape, h.pos, h.place, h.grow, h.valid, h.val⟩) h)
    (Fn.MpSubGG5.correct hra hres' hS' hB' hH hoff')

/-- **The growing `mp_sub(a, b, a)`**. -/
theorem mpSubHA : MpSubHA.Statement := fun {p _ _ _ _} hra hres hS hB hH hoff =>
  Triple.rmap (fun _ h => GrowPost.val (n0 := p.a.alloc) (V := p.a.val - p.b.val) (fun r => r) p.adp
      (p.a.withSign (subSign p.a p.b)) ⟨hres.va.toShape.withSign _, hres.apos, Nat.le_refl _⟩ hres.apos
      (fun _ _ hq => SubG.specA hres.va hres.vb hres.size_lt hq)
      (fun _ h => ⟨h.shape, h.pos, h.place, h.grow, h.valid, h.val⟩) h)
    (Fn.MpSubGAG5.correct hra hres hS hB hH hoff)

end Tom.Machine.Fn.GrowSubH
