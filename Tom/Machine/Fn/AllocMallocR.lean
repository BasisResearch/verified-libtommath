import Tom.Machine.Fn.AllocFree
import VsaIris.Vsa.MallocREntry

/-!
# `_malloc_r(reent, n)` on the machine (for `calloc`)

`_calloc_r` calls `_malloc_r` directly. Its contract here, from
`VsaIris.VsaHeap.mallocRLocalRun_proved` (the `malloc_all` from
`_malloc_r`'s entry) on `Fn/AllocRun.lean`'s run: NULL with the heap kept, or a
fresh 16-aligned block of `n` bytes, now live; memory changed only in the
footprint and `[sp - 512, sp)`.
-/

namespace Tom.Machine.Fn.Alloc

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Vsa.Machine (Config)
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc
open VsaIris VsaIris.VsaHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-- `_malloc_r`'s entry. -/
def mallocREntry : BitVec 64 := 0x8000796c#64

/-- `&_impure_data`, `_malloc_r`'s first argument. -/
def reent : BitVec 64 := 0x800190c8#64

/-- What `_malloc_r` writes: the footprint and its stack. -/
def mallocW (H : List (Nat × Nat)) (sp : Nat) (a : Nat) : Prop := Foot H a ∨ Stk sp depth a

/-- What `_malloc_r(reent, n)` leaves with result `q`. -/
inductive MallocRPost (m M : Mem) (H : List (Nat × Nat)) (sp N : Nat) : Nat → Prop
  | null (h : Null m M H (mallocW H sp)) : MallocRPost m M H sp N 0
  | ok {q : Nat} (h : Got m M H (mallocW H sp) q N) : MallocRPost m M H sp N q

def mallocRL (ra : BitVec 64) (N : Nat) : GRegs := [(1, ra), (10, reent), (11, BitVec.ofNat 64 N)]

/-- **`_malloc_r(reent, N)` on the machine.** -/
theorem mallocR_correct {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)}
    {sp N : Nat} {ra : BitVec 64} (hC : Ctx m v sp depth ra) (hH : Heap m H) (hN : N < 2 ^ 64) :
    Triple (At mallocREntry (mallocRL ra N) m v.keep outp)
      (fun c => ∃ q M, At ra [(1, ra), (10, BitVec.ofNat 64 q)] M v.keep outp c ∧
        MallocRPost m M H sp N q) := by
  intro c hA
  have N' := Entry.of hC (Nat.le_refl _) hA (by simp [mallocRL])
  have hspl : heapEnd + 512 ≤ sp := hC.sp_lo
  have hNn : (BitVec.ofNat 64 N).toNat = N := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hN
  have eS : heapStart = 0x80019d10 := rfl
  obtain ⟨fuel, hrun⟩ := mallocRLocalRun_proved liveT liveT_alloc H (BitVec.ofNat 64 N)
    (BitVec.ofNat 64 sp) ra (savedOf v) (vsaReg c) (img m) rfl N'.spok hC.ra_al
    ⟨(vsaReg_pc hA.pcv).trans rfl, N'.rra, at_vsaReg hA (by decide) (by simp [mallocRL, VsaIris.a0, reent, reentV]),
      N'.rsp, N'.saved⟩
    (at_vsaReg hA (by decide) (by simp [mallocRL, VsaIris.a1])) ((heap_iff m H).1 hH)
    (fun a hs hf => stack_off (e := (0, 0)) hspl N'.spn (by decide) hs (.inl hf))
  obtain ⟨c', E⟩ := LocalRun.reach
    (fun q hq hS => text_off_run (e := (heapStart + 16, 0)) hspl N'.spn (Nat.le_refl _) hq
      (by rcases hS with h | h
          · exact .inl h
          · exact .inr (.inl h)))
    (by decide) fuel _ _ hrun c N'.ok N'.ro (fun _ _ => rfl) (fun a _ => by rw [hA.mem]; rfl)
  obtain ⟨rv', mv', F, hrv, hmv⟩ := E.post
  have hAt := exit_at hA hC.sp_v E hrv F.frame
  have hS : ∀ a, Foot H a → mallocBytes vsaLayoutP H (BitVec.ofNat 64 sp) allocHeadroom a :=
    fun a ha => .inr (by rw [foot_eq]; exact ha)
  have hkp : Keep (mallocW H sp) m c'.σ.mem := fun a ha => by
    rw [E.mem a fun hS' => ha ?_, hA.mem]
    rcases hS' with h | h
    · simp only [stackWin, InExt, allocHeadroom, N'.spn] at h
      exact .inr ⟨by unfold depth; exact h.1, by omega⟩
    · rw [foot_eq] at h; exact .inl h
  refine ⟨c', E.steps, (rv' VsaIris.a0).toNat, c'.σ.mem, ?_, ?_⟩
  · rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact hAt
  · rcases F.result with ⟨h0, hsh⟩ | ⟨hfr, hal, hsh⟩
    · rw [h0]
      exact .null ⟨heap_of_shape hsh fun a ha => hmv a (hS a ha), hkp⟩
    · obtain ⟨hnz, hlo, hhi, hdj⟩ := hfr
      rw [hNn] at hhi hdj hsh
      exact .ok ⟨⟨hnz, hal, hlo, hhi, fun e he a ha => hdj e he a ha⟩,
        heap_of_shape hsh fun a ha => hmv a (hS a (foot_tail ha)), hkp⟩

end Tom.Machine.Fn.Alloc
