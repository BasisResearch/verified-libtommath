import Tom.Machine.Fn.AllocRun

/-!
# `free(p)` on the machine: `Free_Statement` from the `freeLocalRun_proved`

The run is `Fn/AllocRun.lean`'s: `Entry.of` at the call, `LocalRun.reach`,
`exit_at` at the return; the post is the `FreeEnd` in this repository's terms
(`heap_of_shape`, and the frame off `freeBytes` = `blkW`).
-/

namespace Tom.Machine.Fn.Alloc

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Vsa.Machine (Config)
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc
open VsaIris VsaIris.VsaHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- The run's owned bytes (`freeBytes`, the same for `free` and `realloc`) are
`blkW`. -/
theorem blkW_of_freeBytes {H : List (Nat × Nat)} {p n sp a : Nat}
    (hpn : (BitVec.ofNat 64 p).toNat = p) (hsn : (BitVec.ofNat 64 sp).toNat = sp)
    (hsp : 512 ≤ sp) (h : freeBytes vsaLayoutP H (BitVec.ofNat 64 p) n (BitVec.ofNat 64 sp)
      allocHeadroom a) : blkW H p n sp a := by
  simp only [freeBytes, stackWin, InExt, allocHeadroom, hsn, hpn] at h
  rw [foot_eq] at h
  unfold blkW Stk InBlk
  rcases h with h | h | h
  · exact .inr (.inr ⟨by unfold depth; exact h.1, by omega⟩)
  · exact .inl h
  · exact .inr (.inl h)

/-- A live block's address fits in a word. -/
theorem blk_toNat {p n : Nat} (h : p + n ≤ heapEnd) : (BitVec.ofNat 64 p).toNat = p := by
  have : heapEnd = 0x87800000 := rfl
  rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega

/-- **`free(p)` on the machine.** -/
theorem free_correct : Free_Statement := by
  intro m v outp H sp p n ra hC hH c hA
  have N := Entry.of hC (Nat.le_refl _) hA (by simp [freeL])
  have hblk := Heap.blk hH (e := (p, n)) (List.mem_cons_self ..)
  have hspl : heapEnd + 512 ≤ sp := hC.sp_lo
  have hpn := blk_toNat (p := p) (n := n) hblk.2
  obtain ⟨fuel, hrun⟩ := freeLocalRun_proved liveT liveT_alloc H (BitVec.ofNat 64 p) n
    (BitVec.ofNat 64 sp) ra (savedOf v) (vsaReg c) (img m) rfl N.spok hC.ra_al
    ⟨(vsaReg_pc hA.pcv).trans rfl, N.rra, at_vsaReg hA (by decide) (by simp [freeL, VsaIris.a0]), N.rsp, N.saved⟩
    (by rw [hpn]; exact (heap_iff m _).1 hH)
    (fun a hs => by rw [hpn]; exact stack_off hspl N.spn hblk.2 hs)
  obtain ⟨c', E⟩ := LocalRun.reach
    (fun q hq => by simp only [freeBytes, hpn]; exact text_off_run hspl N.spn hblk.1 hq)
    (by decide) fuel _ _ hrun c N.ok N.ro (fun _ _ => rfl) (fun a _ => by rw [hA.mem]; rfl)
  obtain ⟨rv', mv', F, hrv, hmv⟩ := E.post
  have hAt := exit_at hA hC.sp_v E hrv F.frame
  refine ⟨c', E.steps, c'.σ.mem, hAt.weaken (by simp), ?_⟩
  refine ⟨heap_of_shape F.shape fun a ha => hmv a (by simp only [freeBytes, hpn]; exact .inr (foot_split ha)),
    fun a ha => ?_⟩
  rw [E.mem a fun hS => ha (blkW_of_freeBytes hpn N.spn (by omega) hS), hA.mem]

end Tom.Machine.Fn.Alloc
