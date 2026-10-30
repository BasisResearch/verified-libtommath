import Tom.Machine.Fn.AllocBridge

/-!
# Running the allocator from an `At` call state

the allocator theorems (`*LocalRun_proved`, relocated) are `LocalRun`s over
`vsaModel liveT`. `Entry.of` supplies their entry facts from this repository's
call state (`Ctx`, `At`); `exit_at` reads the `At` return state
off it from the `RetFrame`. `free_correct`, `realloc_correct` and `calloc`'s
`_malloc_r` call are instances.
-/

namespace Tom.Machine.Fn.Alloc

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Vsa.Machine (Config)
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc
open VsaIris VsaIris.VsaHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast

/-! ## Registers -/

theorem vsaReg_of_get {c : Config} {k : Nat} (hk : k ≠ VsaIris.PC) {v : BitVec 64}
    (h : gprGet c.σ k = some v) : vsaReg c k = v := by
  rw [vsaReg_gpr hk, h]; rfl

theorem pc_of_vsaReg {live : Nat → Prop} {c : Config} (hok : VsaOk live c) {v : BitVec 64}
    (h : vsaReg c VsaIris.PC = v) : c.σ.regs.get? Register.PC = some v := by
  obtain ⟨w, hw⟩ := hok.good.PC
  have : pcVal c.σ = v := h
  unfold pcVal at this; rw [hw] at this ⊢; exact congrArg some this

theorem vsaReg_pc {c : Config} {v : BitVec 64} (h : c.σ.regs.get? Register.PC = some v) :
    vsaReg c VsaIris.PC = v := by
  show pcVal c.σ = v
  unfold pcVal; rw [h]; rfl

/-! ## The live blocks lie in the arena -/

/-- A live block lies inside the arena (its chunk is in use, below the top). -/
theorem Heap.blk {m : Mem} {H : List (Nat × Nat)} (h : Heap m H) {e : Nat × Nat} (he : e ∈ H) :
    heapStart + 16 ≤ e.1 ∧ e.1 + e.2 ≤ heapEnd := by
  obtain ⟨_, m', ⟨_, top, brk, chunks, bins, W⟩⟩ := h
  obtain ⟨c, hc, _, h1, h2⟩ := W.heap.live e he
  have hb := W.heap.walk.chunk_bounds c hc
  have := W.heap.brk_le
  have := W.top_room
  have e1 : Vsa.Sim.DlHeap.heapEnd = heapEnd := rfl
  have e2 : Vsa.Sim.DlHeap.heapStart = heapStart := rfl
  omega

/-! ## The text is off every owned byte -/

def globalB (a : Nat) : Bool :=
  (0x800188a0 ≤ a && a < 0x800190b0) || (0x800190c8 ≤ a && a < 0x800190cc) ||
  (0x80019500 ≤ a && a < 0x80019510) || (0x80019530 ≤ a && a < 0x80019550) ||
  (0x80019558 ≤ a && a < 0x8001955c) || (0x800195b8 ≤ a && a < 0x80019608)

theorem global_of {a : Nat} (h : Global a) : globalB a = true := by
  unfold Global at h; unfold globalB
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem allocText_low : allocText.all (fun p => decide (p.1 < 0x80019d10) && !globalB p.1) = true := by
  decide +kernel

theorem text_off {p : Nat × BitVec 8} (hp : p ∈ allocText) : p.1 < heapStart ∧ ¬ Global p.1 := by
  have := List.all_eq_true.1 allocText_low p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
  exact ⟨this.1, fun hg => by rw [global_of hg] at this; exact absurd this.2 (by decide)⟩

/-! ## Registers at the ends -/

/-- Pins read back from `vsaReg` on a configuration with every GPR mapped. -/
theorem gholds_of_vsaReg {live : Nat → Prop} {c : Config} (hok : VsaOk live c) :
    ∀ {L : GRegs}, (∀ q ∈ L, 1 ≤ q.1 ∧ q.1 ≤ 31 ∧ vsaReg c q.1 = q.2) → GHolds c.σ L
  | [], _ => trivial
  | (k, w) :: L, h => by
    obtain ⟨h1, h2, h3⟩ := h (k, w) (List.mem_cons_self ..)
    exact ⟨gprGet_eq_of_vsaReg hok h1 h2 h3, gholds_of_vsaReg hok fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

/-- The registers `free`'s run restores (`vsaSaved`). -/
def savedOf (v : Abi) : List (Nat × BitVec 64) := [(8, v.s0), (9, v.s.s1), (18, v.s.s2), (19, v.s.s3)]

theorem keep_mem {v : Abi} {q : Nat × BitVec 64} (hq : q ∈ v.keep) :
    q = (2, v.sp) ∨ q = (3, v.gp) ∨ q = (4, v.tp) ∨ q ∈ savedOf v ∨ q = (20, v.s.s4) ∨
      q = (21, v.s.s5) ∨ q = (22, v.s.s6) ∨ q = (23, v.s.s7) ∨ q = (24, v.s.s8) ∨ q = (25, v.s.s9) ∨
      q = (26, v.s.s10) ∨ q = (27, v.s.s11) := by
  simp only [Abi.keep, sKeepL, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [savedOf]

theorem keep_le {v : Abi} {q : Nat × BitVec 64} (hq : q ∈ v.keep) : 1 ≤ q.1 ∧ q.1 ≤ 27 := by
  simp only [Abi.keep, sKeepL, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem ne_pc {k : Nat} (h : k ≤ 31) : k ≠ VsaIris.PC := by unfold VsaIris.PC; omega

/-! ## Entry and exit -/

/-- The live bytes of the run: the allocator's text. -/
def liveT : Nat → Prop := fun a => ∃ b, (a, b) ∈ allocText

theorem liveT_alloc : AllocLive liveT := fun q hq => ⟨q.2, hq⟩

/-- The owned registers of every allocator run. -/
abbrev aRs : List Nat := allocRegs vsaClob vsaSaved

/-- What a run of the allocator needs from the call state. -/
structure Entry (c : Config) (v : Abi) (ra : BitVec 64) (sp : Nat) : Prop where
  ok : VsaOk liveT c
  ro : ROHolds (vsaModel liveT) c roR allocText
  rra : vsaReg c VsaIris.ra = ra
  rsp : vsaReg c VsaIris.sp = BitVec.ofNat 64 sp
  saved : ∀ q ∈ savedOf v, vsaReg c q.1 = q.2
  spok : SpOKA (BitVec.ofNat 64 sp)
  spn : (BitVec.ofNat 64 sp).toNat = sp

/-- A pinned register of an `At` state, as `vsaReg` reads it. -/
theorem at_vsaReg {pc : BitVec 64} {L : GRegs} {m : Mem} {K : GRegs} {outp : Array String}
    {c : Config} (hA : At pc L m K outp c) {k : Nat} {w : BitVec 64} (hk : k ≤ 31)
    (h : (k, w) ∈ L) : vsaReg c k = w :=
  vsaReg_of_get (ne_pc hk) (gholds_mem hA.regs h)

theorem Entry.of {pc : BitVec 64} {L : GRegs} {m : Mem} {v : Abi} {outp : Array String}
    {sp F : Nat} {ra : BitVec 64} {c : Config} (hC : Ctx m v sp F ra) (hF : 512 ≤ F)
    (hA : At pc L m v.keep outp c) (h1 : (1, ra) ∈ L) : Entry c v ra sp := by
  have hT := textLoaded hC
  have hspl := hC.sp_lo
  have hsph := hC.sp_hi
  have eE : heapEnd = 0x87800000 := rfl
  have hsn : (BitVec.ofNat 64 sp).toNat = sp := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  have gk : ∀ q ∈ v.keep, gprGet c.σ q.1 = some q.2 := fun q hq => gholds_mem hA.keep hq
  have kreg : ∀ q ∈ v.keep, vsaReg c q.1 = q.2 := fun q hq =>
    vsaReg_of_get (ne_pc (by have := keep_le hq; omega)) (gk q hq)
  refine ⟨⟨hA.good, hA.tick, hA.gprs, fun a ⟨b, hb⟩ => by rw [hA.mem, hT _ hb]; rfl, hA.pw⟩,
    ⟨fun q hq => ?_, fun q hq => ?_⟩, at_vsaReg hA (by decide) h1,
    (kreg (2, v.sp) (by simp [Abi.keep])).trans hC.sp_v, fun q hq => kreg q ?_,
    ⟨by rw [hsn]; unfold allocHeadroom Vsa.Sim.tohostAddr; omega, by rw [hsn]; exact hsph,
      by rw [hsn]; exact hC.sp_al⟩, hsn⟩
  · simp only [roR, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact (kreg (3, v.gp) (by simp [Abi.keep])).trans (hC.gp.trans rfl)
  · show (c.σ.mem[q.1]?).getD 0 = q.2
    rw [hA.mem, hT q hq]; rfl
  · simp only [savedOf, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp [Abi.keep, sKeepL]

/-- **The return state**: a run that ends in the `RetFrame` returns to `ra`
with `a0` its result, the ABI registers kept. -/
theorem exit_at {pc : BitVec 64} {L : GRegs} {m : Mem} {v : Abi} {outp : Array String}
    {sp : Nat} {ra : BitVec 64} {c c' : Config} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hA : At pc L m v.keep outp c) (hsv : v.sp = BitVec.ofNat 64 sp)
    (E : RunEnd liveT aRs S Q c c') {rv' : Nat → BitVec 64}
    (hr : ∀ k ∈ aRs, vsaReg c' k = rv' k) (F : RetFrame rv' ra (BitVec.ofNat 64 sp) (savedOf v)) :
    At ra [(1, ra), (10, rv' VsaIris.a0)] c'.σ.mem v.keep outp c' := by
  have gk : ∀ q ∈ v.keep, gprGet c.σ q.1 = some q.2 := fun q hq => gholds_mem hA.keep hq
  have hun : ∀ q ∈ v.keep, q.1 ∉ aRs → vsaReg c' q.1 = q.2 := fun q hq hn =>
    (E.regs _ hn).trans (vsaReg_of_get (ne_pc (by have := keep_le hq; omega)) (gk q hq))
  have hkeep' : ∀ q ∈ v.keep, vsaReg c' q.1 = q.2 := by
    intro q hq
    rcases keep_mem hq with rfl | rfl | rfl | hs | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hr 2 (by decide)).trans (F.sp.trans hsv.symm)
    · exact hun _ hq (by first | decide | (dsimp only; decide))
    · exact hun _ hq (by first | decide | (dsimp only; decide))
    · simp only [savedOf, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;>
        exact (hr _ (by first | decide | (dsimp only; decide))).trans (F.saved _ (by simp [savedOf]))
    all_goals exact hun _ hq (by first | decide | (dsimp only; decide))
  exact { good := E.ok.good, tick := E.ok.tick, mem := rfl
          pcv := pc_of_vsaReg E.ok ((hr VsaIris.PC (by decide)).trans F.pc)
          minstret := E.ok.good.minstret
          regs := ⟨gprGet_eq_of_vsaReg E.ok (by decide) (by decide) ((hr 1 (by decide)).trans F.ra),
            gprGet_eq_of_vsaReg E.ok (by decide) (by decide) (hr 10 (by decide)), trivial⟩
          keep := gholds_of_vsaReg E.ok fun q hq =>
            ⟨(keep_le hq).1, by have := (keep_le hq).2; omega, hkeep' q hq⟩
          out := E.out.trans hA.out
          pw := E.ok.htifIdle
          th := E.ok.good.htif_tohost
          gprs := E.ok.gpr }

/-! ## Footprints -/

/-- A text byte is off every byte a run owns: footprint, a live block, the stack. -/
theorem text_off_run {H : List (Nat × Nat)} {sp : Nat} {e : Nat × Nat} (hsp : heapEnd + 512 ≤ sp)
    (hsn : (BitVec.ofNat 64 sp).toNat = sp) (he : heapStart + 16 ≤ e.1) {q : Nat × BitVec 8}
    (hq : q ∈ allocText) :
    ¬ (stackWin (BitVec.ofNat 64 sp) allocHeadroom q.1 ∨ heapFoot vsaLayoutP H q.1 ∨ InExt e q.1) := by
  obtain ⟨hlo, hng⟩ := text_off hq
  rw [foot_eq]
  rintro (⟨h1, _⟩ | (hg | ⟨h1, _⟩) | ⟨h1, _⟩)
  · simp only [allocHeadroom] at h1; rw [hsn] at h1
    have : heapEnd = 0x87800000 := rfl; have : heapStart = 0x80019d10 := rfl; omega
  · exact hng hg
  · omega
  · omega

/-- The stack window of a call above the arena misses the footprint and the arena. -/
theorem stack_off {H : List (Nat × Nat)} {sp : Nat} (hsp : heapEnd + 512 ≤ sp)
    (hsn : (BitVec.ofNat 64 sp).toNat = sp) {e : Nat × Nat} (he : e.1 + e.2 ≤ heapEnd) {a : Nat}
    (hs : stackWin (BitVec.ofNat 64 sp) allocHeadroom a) :
    ¬ (heapFoot vsaLayoutP H a ∨ InExt e a) := by
  simp only [stackWin, InExt, allocHeadroom, hsn] at hs
  have : heapStart = 0x80019d10 := rfl
  have : heapEnd = 0x87800000 := rfl
  rw [foot_eq]
  rintro ((hg | ⟨_, h2, _⟩) | ⟨_, h2⟩)
  · have := Global.lt hg; omega
  · omega
  · omega

/-- The arena outside the blocks `H` lies in the footprint of `e :: H` or in `e`. -/
theorem foot_split {H : List (Nat × Nat)} {e : Nat × Nat} {a : Nat} (ha : Foot H a) :
    heapFoot vsaLayoutP (e :: H) a ∨ InExt e a := by
  rw [foot_eq]
  by_cases hb : InExt e a
  · exact .inr hb
  · refine .inl ?_
    rcases ha with hg | ⟨h1, h2, h3⟩
    · exact .inl hg
    · refine .inr ⟨h1, h2, fun e' he' => ?_⟩
      rcases List.mem_cons.1 he' with rfl | he'
      · exact hb
      · exact h3 e' he'

theorem foot_tail {H : List (Nat × Nat)} {e : Nat × Nat} {a : Nat} (ha : Foot (e :: H) a) : Foot H a := by
  rcases ha with hg | ⟨h1, h2, h3⟩
  · exact .inl hg
  · exact .inr ⟨h1, h2, fun e' he' => h3 e' (List.mem_cons_of_mem _ he')⟩

end Tom.Machine.Fn.Alloc
