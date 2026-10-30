import Tom.Machine.Fn.SAdd
import Tom.Machine.Kit.SymTac

/-!
# `s_mp_add`'s loop-1 body (`l1_step`: two digit loads, a digit store) through the executor

The three digits are owned; the
conclusion is `TripleZ` (`tripleZ_of_swp`), with three premises more than the incumbent's: `gp`
pinned, and the three digits above `tohost` (the executor's store check `StOK` and the
code/owned-bytes separation).
-/


namespace Tom.Machine.Fn.SAdd.SymP

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Sym
open VsaIris VsaIris.Sym VsaIris.SymExec VsaIris.SymExec.Interp VsaIris.MallocFast

/-- The tracked registers (`regsOf sMpAddCode`). -/
abbrev rsL : List Nat := [32, 1, 2, 6, 8, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]
abbrev C (stops : List (BitVec 64)) := cfg sMpAddBase sMpAddCode rsL stops

theorem l1_step (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pc cdp ou mn mx xp adp bdp i u x y : Nat)
    (M : Mem) (hc : CodeAt M sMpAddBase sMpAddCode) (hx : DRead M adp i x) (hy : DRead M bdp i y)
    (hs : CStore cdp i) (hu : u ≤ 1) (hi : i + 1 < mn) (hmn : adp + 4 * mn ≤ 4294967296)
    (hgp : v.gp = gpV) (hta : tohostAddr + 16 ≤ adp + 4 * i) (htb : tohostAddr + 16 ≤ bdp + 4 * i)
    (htc : tohostAddr + 16 ≤ cdp + 4 * i) :
    TripleZ (At 0x80002218#64 (l1L ra sp pc cdp ou mn mx xp adp bdp i u) M v.keepR outp)
      (At 0x80002218#64 (l1L ra sp pc cdp ou mn mx xp adp bdp (i + 1) ((x + y + u) / 268435456))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((x + y + u) % 268435456))]) v.keepR outp) := by
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hx.r
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hy.r
  have ⟨hc1, hc2, hc3⟩ := ram_bounds hs.rc
  have := hs.al; have := hx.lt; have := hy.lt
  simp only [Vsa.Sim.tohostAddr] at hta htb htc
  refine tripleZ_of_swp (rs := rsL)
    (S := fun a => (adp + 4 * i ≤ a ∧ a < adp + 4 * i + 4) ∨ (bdp + 4 * i ≤ a ∧ a < bdp + 4 * i + 4) ∨
      (cdp + 4 * i ≤ a ∧ a < cdp + 4 * i + 4)) (DA := []) hc
    (by simp [Abi.keepR, *]) (by decide)
    (fun a ha h => by
      rw [inRanges_rT, show sMpAddCode.length = 108 from rfl, show sMpAddBase = 0x8000219c from rfl] at ha
      omega)
    (fun _ h => nomatch h)
    (fun a ha => by rw [writeLog_out]; simp only [OutL, and_true]; omega)
    (by simp [l1L]) (by simp [Abi.keepR, sKeepL]) ?_
  intro R hL hK
  have h11 : R 11 = BitVec.ofNat 64 (cdp + 4 * i) := hL (11, BitVec.ofNat 64 (cdp + 4 * i)) (by simp [l1L])
  have h13 : R 13 = BitVec.ofNat 64 u := hL (13, BitVec.ofNat 64 u) (by simp [l1L])
  have h14 : R 14 = BitVec.ofNat 64 (adp + 4 * i) := hL (14, BitVec.ofNat 64 (adp + 4 * i)) (by simp [l1L])
  have h16 : R 16 = BitVec.ofNat 64 (bdp + 4 * i) := hL (16, BitVec.ofNat 64 (bdp + 4 * i)) (by simp [l1L])
  have h6 : R 6 = BitVec.ofNat 64 (adp + 4 * mn) := hL (6, BitVec.ofNat 64 (adp + 4 * mn)) (by simp [l1L])
  have h29 : R 29 = 268435455#64 := hL (29, 268435455#64) (by simp [l1L])
  have e11 : (BitVec.ofNat 64 (cdp + 4 * i)).toNat = cdp + 4 * i := by rw [BitVec.toNat_ofNat]; omega
  have e14 : (BitVec.ofNat 64 (adp + 4 * i)).toNat = adp + 4 * i := by rw [BitVec.toNat_ofNat]; omega
  have e16 : (BitVec.ofNat 64 (bdp + 4 * i)).toNat = bdp + 4 * i := by rw [BitVec.toNat_ofNat]; omega
  have hxv : BitVec.signExtend 64 (bytesT4 M (adp + 4 * i)) = BitVec.ofNat 64 x := by
    rw [hx.v, signExtend_ofNat32 _ (by omega)]
  have hyv : BitVec.signExtend 64 (bytesT4 M (bdp + 4 * i)) = BitVec.ofNat 64 y := by
    rw [hy.v, signExtend_ofNat32 _ (by omega)]
  refine sym_at (stops := []) (dpcs := [])
    (geom% (geomRun (C []) 11 ⟨0x80002218#64, [], [], []⟩)) 11 0x80002218#64 R M
    (by decide) ?_ ?_
  · geom_auto [h11, h14, h16, e11, e14, e16, tohostAddr]
  · sym_close_st [l1L] [l1L] [h11, h13, h14, h16, h6, h29, e11, e14, e16, hxv, hyv]

end Tom.Machine.Fn.SAdd.SymP
