import Tom.Machine.Api.Libgcc
import Vsa.Reloc.Libgcc.Muldi3Any
import Vsa.Reloc.Libgcc.DivAny
import Vsa.Reloc.Libgcc.DivSpec3

/-!
# libgcc's multiply and divide on the machine

The contracts of `Tom/Machine/Api/Libgcc.lean` from the relocated sibling
proofs (`Vsa/Reloc/Libgcc/`, namespace `Vsa.Sim.Libgcc`):

The scratch registers mapped at the return, for `At.gprs`) over
  ship-your-interpreter's `muldi3_spec` lemmas;

* `__moddi3`, `__divdi3`: the contracts of `Api/Libgcc.lean` are
  `Fn/LibgccSigned.lean`'s. (The weaker bridges from the relocated
  `moddi3_spec`/`divdi3_spec`, `relocatedK`, were removed when `At` gained
  `gprs`: those specs do not say that `ra`, `t0`, `a1`–`a3` stay mapped.)

Each proof is the same bridge: the entry `At` state gives the relocated
precondition with the entry register file as its ghost frame `g` (the
`…Loaded` byte pins from `Img` by `loaded_of`), and the relocated post gives
the return `At` state (the caller's keep-set across the ghost frame by
`keep_of_frame`; the HTIF pins are outside every write set).
-/

namespace Tom.Machine.Fn.Libgcc

open LeanRV64DExecutable Vsa Vsa.Logic
open Vsa.Sim (noiseRegs gprReg GRegs GHolds)
open Tom.Machine Tom.Machine.Api.Libgcc
open Vsa.Machine (Config MState)

/-! ## The code, as the relocated proofs pin it -/

theorem muldi3_loaded {m : Mem} (h : Img m) : Vsa.Sim.Libgcc.Code.__muldi3Loaded m := by
  unfold Vsa.Sim.Libgcc.Code.__muldi3Loaded Vsa.Sim.Libgcc.Code.__muldi3Chunk0
  loaded_of h.muldi3

theorem udivdi3_loaded {m : Mem} (h : Img m) : Vsa.Sim.Libgcc.Code.__hidden___udivdi3Loaded m := by
  unfold Vsa.Sim.Libgcc.Code.__hidden___udivdi3Loaded Vsa.Sim.Libgcc.Code.__hidden___udivdi3Chunk0
    Vsa.Sim.Libgcc.Code.__hidden___udivdi3Chunk1
  loaded_of h.hiddenUdivdi3

theorem moddi3_loaded {m : Mem} (h : Img m) : Vsa.Sim.Libgcc.Code.__moddi3Loaded m := by
  unfold Vsa.Sim.Libgcc.Code.__moddi3Loaded Vsa.Sim.Libgcc.Code.__moddi3Chunk0
  loaded_of h.moddi3

theorem divdi3_loaded {m : Mem} (h : Img m) : Vsa.Sim.Libgcc.Code.__divdi3Loaded m := by
  unfold Vsa.Sim.Libgcc.Code.__divdi3Loaded Vsa.Sim.Libgcc.Code.__divdi3Chunk0
  loaded_of h.divdi3

/-! ## The write sets, as the relocated frames state them -/

section frames

variable {R : Register} (hn : ∀ rr ∈ noiseRegs, (rr == R) = false)

include hn in
theorem notWrittenM_of (hw : ∀ k ∈ mulWrites, (gprReg k == R) = false) :
    Vsa.Sim.Libgcc.NotWrittenM R :=
  ⟨hw 10 (by simp), hw 11 (by simp), hw 12 (by simp), hw 13 (by simp),
   hn _ (by simp [noiseRegs]), hn _ (by simp [noiseRegs]), hn _ (by simp [noiseRegs]),
   hn _ (by simp [noiseRegs]), hn _ (by simp [noiseRegs]), hn _ (by simp [noiseRegs]),
   hn _ (by simp [noiseRegs])⟩

include hn in
theorem notWritten_of (hw : ∀ k ∈ mulWrites, (gprReg k == R) = false) :
    Vsa.Sim.Libgcc.NotWritten R :=
  notWrittenM_of hn hw

include hn in
theorem notWrittenD_of (hw : ∀ k ∈ divWrites, (gprReg k == R) = false) :
    Vsa.Sim.Libgcc.NotWrittenD R :=
  ⟨notWritten_of hn (fun k hk => hw k (by simp at hk ⊢; omega)), hw 1 (by simp), hw 5 (by simp)⟩

end frames

/-! ## `__muldi3` -/

namespace Muldi3

theorem correctK : Api.Libgcc.Muldi3.StatementK := by
  intro m K outp ra x y hm hra hK c h
  obtain ⟨c', hs, ⟨hG, hmem, hout, hpc, ha0, hra', htick, hfr⟩, b1, b2, b3, h11, h12, h13⟩ :=
    Vsa.Sim.Libgcc.muldi3_spec_present (fun R => c.σ.regs.get? R) x y ra m outp c
      ⟨⟨none, none,
        { good := h.good, loaded := h.mem ▸ muldi3_loaded hm, mem := h.mem, sailOut := h.out,
          pc := h.pcv, a0 := h.regs.2.1, a1 := h.regs.2.2.1, a2 := fun _ e => (nomatch e),
          a3 := fun _ e => (nomatch e), ra := h.regs.1, minstret := h.minstret, tick := h.tick,
          hframe := fun _ _ => rfl }⟩, hra⟩
  refine ⟨c', hs,
    { good := hG, tick := htick, mem := hmem, pcv := hpc, minstret := hG.minstret,
      regs := ⟨hra', ha0, trivial⟩, out := hout, th := hG.htif_tohost,
      keep := keep_of_frame hK (fun R hn hw => hfr R (notWrittenM_of hn hw)) h.keep,
      pw := (hfr _ (by decide)).trans h.pw
      gprs := allGprs_of_frame h.gprs (fun R hn hw => hfr R (notWrittenM_of hn hw)) fun k hk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl
        · exact ⟨by decide, by show (c'.σ.regs.get? Register.x10).isSome = true; rw [ha0]; rfl⟩
        · exact ⟨by decide, by show (c'.σ.regs.get? Register.x11).isSome = true; rw [h11]; rfl⟩
        · exact ⟨by decide, by show (c'.σ.regs.get? Register.x12).isSome = true; rw [h12]; rfl⟩
        · exact ⟨by decide, by show (c'.σ.regs.get? Register.x13).isSome = true; rw [h13]; rfl⟩ }⟩

theorem correct : Api.Libgcc.Muldi3.Statement := by
  intro m v outp ra x y hm hra
  exact correctK hm hra (keepOK_sub (keepOK_abi v) (by decide))

end Muldi3

/-! ## `__udivdi3` -/

namespace Udivdi3

theorem correctK : Api.Libgcc.Udivdi3.StatementK := by
  intro m K outp ra n d hm hra hd hK c h
  have hpos : 0 < d.toNat := by
    rcases Nat.eq_zero_or_pos d.toNat with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq h0) hd
    · exact h0
  obtain ⟨c', hs, hG, hmem, hout, hpc, hq, hr, hra', htick, hfr, ⟨b2, h12⟩, ⟨b3, h13⟩⟩ :=
    Vsa.Sim.Libgcc.udivdi3_spec_any (fun R => c.σ.regs.get? R) n d ra m outp c
      ⟨⟨none, none,
        { good := h.good, loaded := h.mem ▸ udivdi3_loaded hm, mem := h.mem, sailOut := h.out,
          pc := h.pcv, a0 := h.regs.2.1, a1 := h.regs.2.2.1, a2 := fun _ e => (nomatch e),
          a3 := fun _ e => (nomatch e), ra := h.regs.1, minstret := h.minstret, tick := h.tick,
          hframe := fun _ _ => rfl }⟩, hpos, hra⟩
  refine ⟨c', hs,
    { good := hG, tick := htick, mem := hmem, pcv := hpc, minstret := hG.minstret,
      regs := ⟨hra', hq, hr, trivial⟩, out := hout, th := hG.htif_tohost,
      keep := keep_of_frame hK (fun R hn hw => hfr R (notWritten_of hn hw)) h.keep,
      pw := (hfr _ (by decide)).trans h.pw
      gprs := allGprs_of_frame h.gprs (fun R hn hw => hfr R (notWritten_of hn hw)) fun k hk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl
        · exact ⟨by decide, by show (c'.σ.regs.get? Register.x10).isSome = true; rw [hq]; rfl⟩
        · exact ⟨by decide, by show (c'.σ.regs.get? Register.x11).isSome = true; rw [hr]; rfl⟩
        · exact ⟨by decide, by show (c'.σ.regs.get? Register.x12).isSome = true; rw [h12]; rfl⟩
        · exact ⟨by decide, by show (c'.σ.regs.get? Register.x13).isSome = true; rw [h13]; rfl⟩ }⟩

theorem correct : Api.Libgcc.Udivdi3.Statement := by
  intro m v outp ra n d hm hra hd
  exact correctK hm hra hd (keepOK_sub (keepOK_abi v) (by decide))

end Udivdi3

theorem toInt_ne_zero {d : BitVec 64} (hd : d ≠ 0#64) : d.toInt ≠ 0 := by
  have := BitVec.toInt_ne.2 hd
  rwa [BitVec.toInt_zero] at this

/-! ## `__moddi3` -/


/-! ## `__divdi3` -/

theorem umoddi3_loaded {m : Mem} (h : Img m) : Vsa.Sim.Libgcc.Code.__umoddi3Loaded m := by
  unfold Vsa.Sim.Libgcc.Code.__umoddi3Loaded Vsa.Sim.Libgcc.Code.__umoddi3Chunk0
  loaded_of h.umoddi3

/-- The relocated precondition's form of "not `intMin / -1`". -/
theorem no_overflow {n d : BitVec 64} (h : n ≠ BitVec.intMin 64 ∨ d ≠ -1#64) :
    ¬(n.toInt = -2^63 ∧ d.toInt = -1) := by
  rintro ⟨hn, hd⟩
  rcases h with h | h
  · exact h (BitVec.toInt_inj.1 (by rw [hn]; decide))
  · exact h (BitVec.toInt_inj.1 (by rw [hd]; decide))


end Tom.Machine.Fn.Libgcc
