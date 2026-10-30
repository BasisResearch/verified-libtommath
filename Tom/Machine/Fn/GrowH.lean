import Tom.Machine.Fn.MpAddGMainG
import Tom.Machine.Fn.MpLshdGMainG
import Tom.Machine.Api.MpAddH
import Tom.Machine.Api.MpLshdH
import Tom.Spec.GrowHStep
import Tom.Machine.Kit.Bridge
import Tom.Machine.Kit.ResFrom
import Tom.Machine.Kit.GrowBridge

/-!
Same entry, stack depth (608 / 576), registers and heap; the regions are the same names in two
types (`Api.Bin.R` / `Api.MpAddG.R`, `Api.Un.R` / `Api.MpLshdG.R`), renamed by `Sound.pull` /
`Bundle.pull` (`Entry.pull`, the post back by `HPost.rename`, Kit/Bridge.lean). Results: `none` ↦ `(false, c's old block, c as left)`, `some (q, c')` ↦
`(true, q, c')`; the values from `AddG.spec` / `LshdPost.grown_spec` (`Tom/Spec/GrowHStep.lean`).
-/

namespace Tom.Machine.Fn.GrowH

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
  Tom.Machine.Std

/-! ## `mp_add` -/

def rAdd : MpAddG.R → Bin.R
  | .stk => .stk | .aS => .aS | .aD => .aD | .bS => .bS | .bD => .bD | .cS => .cS | .cD => .cD
  | .code => .code

def pAdd (p : MpAddH.P) : MpAddG.P := ⟨p.sp, p.pa, p.adp, p.pb, p.bdp, p.pc, p.cdp, p.a, p.b, p.c, p.H⟩

theorem pullAdd {p : MpAddH.P} {m : Mem} (hres : MpAddH.Res p) (hS : Sound (MpAddH.lay p) Bin.isW)
    (hB : Bundle (MpAddH.lay p) (MpAddH.kind p) m) (hoff : ∀ r, Off (MpAddH.lay p r) (MpAddH.hin p)) :
    MpAddG.Res (pAdd p) ∧ Sound (MpAddG.lay (pAdd p)) MpAddG.isW ∧ Bundle (MpAddG.lay (pAdd p)) (MpAddG.kind (pAdd p)) m ∧
      ∀ r, Off (MpAddG.lay (pAdd p) r) (MpAddH.hin p) :=
  ⟨by res_from [pAdd] hres, Entry.pull rAdd _ MpAddG.all (fun r => by cases r <;> rfl) (fun r => by cases r <;> rfl) hS hB hoff⟩

theorem mpAddH : MpAddH.Statement := by
  intro p m v outp ra hra hres hS hB hH hoff
  obtain ⟨hres', hS', hB', hoff'⟩ := pullAdd hres hS hB hoff
  exact Triple.rmap (fun _ h => GrowPost.val (n0 := p.c.alloc) (V := p.a.val + p.b.val) rAdd p.cdp
      (p.c.withSign (addSign p.a p.b)) ⟨hres.sc.withSign _, hres.cpos, Nat.le_refl _⟩ hres.cpos
      (fun _ _ hq => AddG.spec hres.va hres.vb hres.sc hres'.size_lt hq)
      (fun _ h => ⟨h.shape, h.pos, h.place, h.grow, h.valid, h.val⟩) h)
    (Fn.MpAddGG5.correct hra hres' hS' hB' hH hoff')

/-! ## `mp_lshd` -/

def rLshd : MpLshdG.R → Un.R
  | .stk => .stk | .aS => .aS | .aD => .aD | .code => .code

def pLshd (p : MpLshdH.P) : MpLshdG.P := ⟨p.sp, p.pa, p.adp, p.a, p.k, p.H⟩

theorem mpLshdH : MpLshdH.Statement := by
  intro p m v outp ra hra hres hS hB hH hoff
  have hres' : MpLshdG.Res (pLshd p) := by res_from [pLshd] hres
  obtain ⟨hS', hB', hoff'⟩ := Entry.pull (lay' := MpLshdG.lay (pLshd p)) (kind' := MpLshdG.kind (pLshd p)) (isW' := MpLshdG.isW) rLshd _ MpLshdG.all (fun r => by cases r <;> rfl) (fun r => by cases r <;> rfl) hS hB hoff
  refine Triple.rmap ?_ (Fn.MpLshdGG5.correct hra hres' hS' hB' hH hoff')
  rintro cf ⟨x, M, hat, hq, hp⟩
  rcases x with _ | ⟨q, a'⟩
  · exact ⟨(false, p.adp, p.a), M, hat,
      { shape := hres.va.toShape, pos := hres.apos, place := hp.place, grow := Nat.le_refl _
        valid := fun h => absurd h Bool.false_ne_true, mag := fun h => absurd h Bool.false_ne_true
        sign := fun h => absurd h Bool.false_ne_true },
      hp.rename rLshd (fun r => by cases r <;> rfl) rfl (fun r => by cases r <;> rfl) (by decide) (by decide)⟩
  · have hs := LshdPost.grown_spec hres.va hres'.size_lt hq
    exact ⟨(true, q, a'), M, hat,
      { shape := hs.1.toShape, pos := by have := hres.apos; have := hs.2.2.2; show 0 < a'.alloc; omega
        place := hp.place, grow := hs.2.2.2, valid := fun _ => hs.1, mag := fun _ => hs.2.1
        sign := fun _ => hs.2.2.1 },
      hp.rename rLshd (fun r => by cases r <;> rfl) rfl (fun r => by cases r <;> rfl) (by decide) (by decide)⟩

end Tom.Machine.Fn.GrowH
