import VsaIris.Vsa.MallocRunAll

/-!
# `_malloc_r` from its own entry

ship-your-interpreter's `mallocLocalRun_proved` starts at the `malloc`
wrapper (`mv a1,a0; ld a0,_impure_ptr; j _malloc_r`). `_calloc_r` calls
`_malloc_r` directly, with `a0 = &_impure_data` (`reentV`) and `a1 = n`. This
is the same proof from `_malloc_r`'s entry: the `malloc_all` (its run from
`0x8000796c`) with the entry `MEntry` read off the registers, instead of
`malloc_entry`'s three wrapper steps.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- `_malloc_r`'s entry. -/
def mallocREntryBV : BitVec 64 := 0x8000796c#64

/-- **`_malloc_r(reent, n)`'s run, first-order** (`MallocLocalRun` with `a0 =
reentV` and the request in `a1`). -/
def MallocRLocalRun (M : MachineModel) (L : DlLayout) (SpOK : BitVec 64 → Prop) (entry gpv : BitVec 64)
    (clob savedRegs : List Nat) (headroom : Nat) (text : List (Nat × BitVec 8)) : Prop :=
  ∀ (H : List (Nat × Nat)) (n s r : BitVec 64) (saved : List (Nat × BitVec 64))
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8),
    saved.map Prod.fst = savedRegs → SpOK s → r.toNat % 4 = 0 → EntryRegs rv entry r reentV s saved →
    rv a1 = n → L.Shape mv H → (∀ a, stackWin s headroom a → ¬ heapFoot L H a) →
    ∃ fuel, LocalRun M [(gp, gpv)] text (allocRegs clob savedRegs) (mallocBytes L H s headroom)
      (MallocEnd L H n r s saved) fuel rv mv

theorem mallocRLocalRun_proved (live : Nat → Prop) (hl : AllocLive live) :
    MallocRLocalRun (vsaModel live) vsaLayoutP SpOKA mallocREntryBV gpV vsaClob vsaSaved
      allocHeadroom allocText := by
  intro H n s r saved rv mv hsv hsp hral he ha1 hshape hdisj
  obtain ⟨hst, m1, top, brkv, chunks, bins, him, hheap⟩ := hshape
  have O := mOK_loc (H := H) (n := n) (Mt0 := mt0 m1 s mv) (top0 := top) hl hsv hsp hral he hst
  have Hp := mHeap_entry (C := mLocCtx live H n r s saved rv (mt0 m1 s mv) top) rfl
    (by simp only [mLocCtx]) hsp him hheap hdisj
  have h := malloc_all O ⟨he.ra, he.sp, he.a0, ha1, rfl, rfl, rfl, rfl⟩ Hp
  simp only [mLocCtx] at h
  exact aw_run h he.pc him hdisj

end VsaIris.VsaHeap
