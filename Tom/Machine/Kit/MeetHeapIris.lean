import Tom.Machine.Kit.MeetHeap
import Tom.Machine.Fn.AllocBridge
import VsaIris.DlHeap

/-!
# The heap kind is iris-lean's heap (the bridge to the resources)

`Kit/MeetHeap.lean` states the heap over concrete memory: `AHeap m H` (the
allocator's `Heap`, `_impure_ptr`), regions `Off` it, `Sound` among them. The
separation-logic heap (`VsaIris/DlHeap.lean`) is `isHeap L H`: some image with
`L.Shape img H` and ownership of every byte of `heapFoot L H`; a live block is
`blockOwn p n`. For the relocated layout `vsaLayoutP`, `heapFoot = Foot` and
`Shape (img m) = Heap m` (`Fn/AllocBridge.lean`, `foot_eq`, `heap_iff`). So the
resources built from a memory `m` (each owned byte points to its value in `m`,
as `alloc_mach` hands them out) split as Meet says:

* `aheap_isHeap`: owning a byte set `D ⊇ Foot H` at `m`'s values, with
  `AHeap m H`, is `isHeap vsaLayoutP H` ∗ owning `D` minus the footprint;
* `off_split`: a region `Off` the allocator lies in that rest, and splits off;
* `region_blockOwn`: a region's bytes, forgetting their values, are the
  `blockOwn` (a live digit array, or a fresh block a call placed);
* `sound_split`: two `Sep` regions of a sound layout are separate resources.

So a later Iris client (SWP) can take Meet's allocator instances' pre/post
(`AHeap`, `Off`, `Place.fresh`) as `isHeap ∗ blockOwn ∗ …` without re-deriving
the heap.
-/

namespace Tom.Machine.HeapIris

open Iris Iris.BI Iris.ProofMode VsaIris VsaIris.VsaHeap
open Tom.Machine.Api.Alloc

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The bytes `D`, owned at the values of the memory `m`. -/
abbrev memOwn (m : Tom.Machine.Mem) (D : Nat → Prop) : IProp GF := ownSet D (fun a => a ↦ₘ Fn.Alloc.img m a)

/-- **The heap kind is `isHeap`.** -/
theorem aheap_isHeap {m : Tom.Machine.Mem} {H : List (Nat × Nat)} {D : Nat → Prop} (h : AHeap m H)
    (hD : ∀ a, Foot H a → D a) :
    memOwn (GF := GF) m D ⊢ isHeap vsaLayoutP H ∗ memOwn m (fun a => D a ∧ ¬ Foot H a) := by
  iintro Hm
  ihave ⟨H1, H2⟩ := ownSet_split D (Foot H) _ $$ Hm
  iframe H2
  unfold isHeap
  iexists Fn.Alloc.img m
  isplitr
  · ipureintro; exact (Fn.Alloc.heap_iff m H).1 h.heap
  iapply ownSet_iff (S := fun a => D a ∧ Foot H a) (T := heapFoot vsaLayoutP H) _
    (fun a => by rw [Fn.Alloc.foot_eq]; exact ⟨fun h => h.2, fun h => ⟨hD a h, h⟩⟩) $$ H1

/-- **A region off the allocator splits off the rest.** -/
theorem off_split {m : Tom.Machine.Mem} {H : List (Nat × Nat)} {D : Nat → Prop} {I : Iv} (ho : Off I H)
    (hD : ∀ a, I.In a → D a) :
    memOwn (GF := GF) m (fun a => D a ∧ ¬ Foot H a) ⊢
      memOwn m I.In ∗ memOwn m (fun a => (D a ∧ ¬ Foot H a) ∧ ¬ I.In a) := by
  iintro Hm
  ihave ⟨H1, H2⟩ := ownSet_split (fun a => D a ∧ ¬ Foot H a) I.In _ $$ Hm
  iframe H2
  iapply ownSet_iff (S := fun a => (D a ∧ ¬ Foot H a) ∧ I.In a) _
    (fun a => ⟨fun h => h.2, fun h => ⟨⟨hD a h, fun hf => ho.pt a h (.inl hf)⟩, h⟩⟩) $$ H1

/-- **A region's bytes are the `blockOwn`** (values forgotten). -/
theorem region_blockOwn {m : Tom.Machine.Mem} (I : Iv) : memOwn (GF := GF) m I.In ⊢ blockOwn I.base I.len :=
  (ownSet_forget _ _).trans (ownSet_iff _ fun _ => Iff.rfl)

/-- **Two `Sep` regions are separate resources.** -/
theorem sound_split {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} (hS : Sound ρ isW)
    {m : Tom.Machine.Mem} {r t : ι} (hsep : Sep isW r t = true) :
    memOwn (GF := GF) m (fun a => (ρ r).In a ∨ (ρ t).In a) ⊢ memOwn m (ρ r).In ∗ memOwn m (ρ t).In := by
  iintro Hm
  ihave ⟨H1, H2⟩ := ownSet_split (fun a => (ρ r).In a ∨ (ρ t).In a) (ρ r).In _ $$ Hm
  have hd := hS r t hsep
  isplitl [H1]
  · iapply ownSet_iff (S := fun a => ((ρ r).In a ∨ (ρ t).In a) ∧ (ρ r).In a) _
      (fun a => ⟨fun h => h.2, fun h => ⟨.inl h, h⟩⟩) $$ H1
  · iapply ownSet_iff (S := fun a => ((ρ r).In a ∨ (ρ t).In a) ∧ ¬ (ρ r).In a) _
      (fun a => ⟨fun h => h.1.resolve_left h.2, fun h => ⟨.inr h, fun h' => by
        unfold Iv.Disj Disj Iv.In at *; omega⟩⟩) $$ H2

end Tom.Machine.HeapIris
