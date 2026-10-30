import Tom.Machine.Fn.MpLshd
import Tom.Machine.Kit.SymTac

/-!
# `mp_lshd`'s `e2_step` (a store, then a load from the same struct) through the executor

The struct is owned (`S`): the load
after the store is forwarded by the executor (`symLoad`, same base, disjoint offsets). Without a
presence premise for the owned bytes the adequacy is `tripleZ_of_swp`: the conclusion is
`TripleZ` (the run ends zero-equivalent to the incumbent's `At` state).
-/


namespace Tom.Machine.Fn.MpLshd.SymP

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Sym
open VsaIris VsaIris.Sym VsaIris.SymExec VsaIris.SymExec.Interp VsaIris.MallocFast

/-- The tracked registers (`regsOf mpLshdCode`, and `s0`, which `e1L` pins). -/
abbrev rsL : List Nat := [32, 1, 2, 8, 10, 11, 12, 13, 14, 15, 16, 17]
abbrev C (stops : List (BitVec 64)) := cfg mpLshdBase mpLshdCode rsL stops

/-- `e2_step` (store `used`, then load `dp` from the same struct) through the executor:
the struct owned, the conclusion up to zero-equivalence (`TripleZ`), and two premises more
(`gp` pinned, the struct above `tohost`). -/
theorem e2_step (s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa dp u al b : Nat) (M : Mem)
    (hc : CodeAt M mpLshdBase mpLshdCode) (hp : Ram pa 24) (hpa : pa % 8 = 0)
    (hcode : pa + 24 ≤ mpLshdBase ∨ mpLshdBase + 200 ≤ pa)
    (hdp : bytesT8 M (pa + 16) = BitVec.ofNat 64 dp)
    (hu : 0 < u) (hal : u + b ≤ al) (hal' : al < 2 ^ 31)
    (hgp : v.gp = gpV) (htp : tohostAddr + 16 ≤ pa) :
    TripleZ (At 0x800015e0#64 (e1L s0 sp pa u al b) M v.keepR outp)
      (At 0x800015ec#64 (e2L' s0 sp dp u b) (writeLog M [(pa, 4, BitVec.ofNat 64 (u + b))]) v.keepR outp) := by
  have ⟨hp1, hp2, hp3⟩ := ram_bounds hp
  simp only [Vsa.Sim.tohostAddr] at htp
  refine tripleZ_of_swp (rs := rsL) (S := fun a => pa ≤ a ∧ a < pa + 24) (DA := []) hc
    (by simp [Abi.keepR, *]) (by decide)
    (fun a ha h => by
      rw [inRanges_rT, show mpLshdCode.length = 50 from rfl, show mpLshdBase = 0x800015b8 from rfl] at ha
      omega)
    (fun _ h => nomatch h)
    (fun a ha => by rw [writeLog_out]; simp only [OutL, and_true]; omega)
    (by simp [e2L']) (by simp [Abi.keepR, sKeepL]) ?_
  intro R hL hK
  have h14 : R 14 = BitVec.ofNat 64 pa := hL (14, BitVec.ofNat 64 pa) (by simp [e1L])
  have h11 : R 11 = BitVec.ofNat 64 (u + b) := hL (11, BitVec.ofNat 64 (u + b)) (by simp [e1L])
  have h12 : R 12 = BitVec.ofNat 64 b := hL (12, BitVec.ofNat 64 b) (by simp [e1L])
  have e14 : (BitVec.ofNat 64 pa).toNat = pa := by rw [BitVec.toNat_ofNat]; omega
  have f14 : (BitVec.ofNat 64 pa + 16#64).toNat = pa + 16 := by rw [toNat_ofNat_add]; omega
  refine sym_at (stops := [0x800015ec#64]) (dpcs := [])
    (geom% (geomRun (C [0x800015ec#64]) 10 ⟨0x800015e0#64, [], [], []⟩)) 10 0x800015e0#64 R M
    (by decide) ?_ ?_
  · geom_auto [h14, e14, tohostAddr]
  · sym_close_st [e2L'] [e1L] [h11, h12, h14, e14, f14, hdp]

end Tom.Machine.Fn.MpLshd.SymP
