import Tom.Machine.Fn.AllocFree

/-!
# `realloc(p, nNew)`, growing, on the machine: `Realloc_Statement`

From the `reallocLocalRun_proved` (relocated), on `Fn/AllocRun.lean`'s run
(as `free_correct`): the old block's bytes are the run's `old` image; the
result is read off `ReallocEnd` (NULL with the heap and block kept, or a fresh
block holding the old bytes).
-/

namespace Tom.Machine.Fn.Alloc

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Vsa.Machine (Config)
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc
open VsaIris VsaIris.VsaHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- **`realloc(p, nNew)` on the machine** (grow). -/
theorem realloc_correct : Realloc_Statement := by
  intro m v outp H sp p n nNew ra hC hH hlt h64 c hA
  have N := Entry.of hC (Nat.le_refl _) hA (by simp [reallocL])
  have hblk := Heap.blk hH (e := (p, n)) (List.mem_cons_self ..)
  have hspl : heapEnd + 512 ≤ sp := hC.sp_lo
  have hpn := blk_toNat (p := p) (n := n) hblk.2
  obtain ⟨fuel, hrun⟩ := reallocLocalRun_proved liveT liveT_alloc H (BitVec.ofNat 64 p) n nNew
    (BitVec.ofNat 64 sp) ra (savedOf v) (vsaReg c) (img m) (img m) rfl N.spok hC.ra_al
    ⟨(vsaReg_pc hA.pcv).trans rfl, N.rra, at_vsaReg hA (by decide) (by simp [reallocL, VsaIris.a0, VsaIris.a1]), N.rsp, N.saved⟩
    (at_vsaReg hA (by decide) (by simp [reallocL, VsaIris.a0, VsaIris.a1])) hlt h64
    (by rw [hpn]; exact (heap_iff m _).1 hH) (fun _ _ => rfl)
    (fun a hs => by rw [hpn]; exact stack_off hspl N.spn hblk.2 hs)
  obtain ⟨c', E⟩ := LocalRun.reach
    (fun q hq => by simp only [freeBytes, hpn]; exact text_off_run hspl N.spn hblk.1 hq)
    (by decide) fuel _ _ hrun c N.ok N.ro (fun _ _ => rfl) (fun a _ => by rw [hA.mem]; rfl)
  obtain ⟨rv', mv', F, hrv, hmv⟩ := E.post
  have hAt := exit_at hA hC.sp_v E hrv F.frame
  have hS : ∀ a, Foot H a → freeBytes vsaLayoutP H (BitVec.ofNat 64 p) n (BitVec.ofNat 64 sp)
      allocHeadroom a := fun a ha => by simp only [freeBytes, hpn]; exact .inr (foot_split ha)
  have hkp : Keep (blkW H p n sp) m c'.σ.mem := fun a ha => by
    rw [E.mem a fun hS => ha (blkW_of_freeBytes hpn N.spn (by omega) hS), hA.mem]
  refine ⟨c', E.steps, (rv' VsaIris.a0).toNat, c'.σ.mem, ?_, ?_⟩
  · rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hAt
  · rcases F.result with ⟨h0, hsh, hcp⟩ | ⟨hfr, hal, hsh, hcp⟩
    · rw [h0]
      refine .null ⟨heap_of_shape (by rw [hpn] at hsh; exact hsh) fun a ha => hmv a ?_, hkp⟩ fun k hk => ?_
      · simp only [freeBytes, hpn]; rw [foot_eq]; exact .inr (.inl ha)
      · rw [hmv (p + k) (by simp only [freeBytes, hpn, stackWin, InExt]; exact .inr (.inr ⟨by omega, by omega⟩))]
        have := hcp k hk
        rw [hpn] at this; exact this
    · obtain ⟨hnz, hlo, hhi, hdj⟩ := hfr
      refine .ok ⟨⟨hnz, hal, hlo, hhi, fun e he a ha => hdj e he a ha⟩,
        heap_of_shape hsh fun a ha => hmv a (hS a (foot_tail ha)), hkp⟩ fun k hk => ?_
      have hlo' : heapStart ≤ (rv' VsaIris.a0).toNat := hlo
      have hhi' : (rv' VsaIris.a0).toNat + nNew ≤ heapEnd := hhi
      have hin : Foot H ((rv' VsaIris.a0).toNat + k) := by
        have hkn : (rv' VsaIris.a0).toNat + k < (rv' VsaIris.a0).toNat + nNew :=
          Nat.add_lt_add_left (Nat.lt_trans hk hlt) _
        exact .inr ⟨Nat.le_trans hlo' (Nat.le_add_right _ _), Nat.lt_of_lt_of_le hkn hhi',
          fun e he hin => hdj e he _ ⟨Nat.le_add_right _ _, hkn⟩ hin⟩
      rw [hmv _ (hS _ hin)]
      have := hcp k hk
      rw [hpn] at this; exact this

end Tom.Machine.Fn.Alloc
