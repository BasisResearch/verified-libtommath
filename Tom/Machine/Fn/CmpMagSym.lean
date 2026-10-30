import Tom.Machine.Fn.CmpMag
import Tom.Machine.Kit.SymTac

/-!
# `mp_cmp_mag`'s segments through ship-your-interpreter's symbolic executor

The eight segment lemmas of `Fn/CmpMag.lean`, re-proved by one executor run each
(`Kit/Sym.lean`: `triple_of_swp`, `sym_at`; `Kit/SymTac.lean`: `sym_close`), statements as the
incumbent's plus one premise, `hgp : v.gp = gpV` (the executor's `SWP` fixes `gp`). No generated
segment chain is used. `entry_run` proves the four entry segments (three branches, four exits)
by ONE run.

The runs are read-only: no byte is owned (`S = ⊥`); the loads read the data view (`DA = ramA`,
every RAM byte), so the conclusion is the incumbent's exact `Triple (At …) (At …)`.
-/


namespace Tom.Machine.Fn.CmpMag.SymP

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Sym
open VsaIris VsaIris.Sym VsaIris.SymExec VsaIris.SymExec.Interp VsaIris.MallocFast

/-- The tracked registers (`regsOf mpCmpMagCode`). -/
abbrev rs : List Nat := [32, 1, 10, 11, 12, 13, 14, 15]
abbrev C (stops : List (BitVec 64)) := cfg mpCmpMagBase mpCmpMagCode rs stops (loadPcs mpCmpMagBase mpCmpMagCode)

set_option hygiene false in
/-- The read-only adequacy for this function, its run residual closed by `cmp_close`. -/
macro "cmp_ro" ds:term : tactic => `(tactic|
  (refine triple_of_swp (rs := rs) (S := fun _ => False) (DA := ramA) hc
    (by simp [Abi.keep, *]) (by decide) (fun _ _ h => h) (fun _ _ h => h) (fun _ h => h.elim)
    (fun _ _ => rfl) (fun _ h => h.elim) (by simp [$ds:term]) (by simp [Abi.keep, sKeepL]) ?_
   intro R hL hK))

/-! ## The entry runs (stops at the loop head) -/

theorem gt_step (ra : BitVec 64) (v : Abi) (outp : Array String) (pa pb ua ub : Nat) (m : Mem)
    (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hra : ra.toNat % 4 = 0)
    (hu : UsedRead m pa pb ua ub) (hlt : ub < ua) (hgp : v.gp = gpV) :
    Triple (At entry (entryL ra pa pb) m v.keep outp) (At ra (retL ra 1#64) m v.keep outp) := by
  cmp_ro retL
  have h1 : R 1 = ra := hL (_, _) (by simp [entryL])
  have h10 : R 10 = BitVec.ofNat 64 pa := hL (10, BitVec.ofNat 64 pa) (by simp [entryL])
  have h11 : R 11 = BitVec.ofNat 64 pb := hL (11, BitVec.ofNat 64 pb) (by simp [entryL])
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hu.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hu.rb
  have ⟨hsa, hsb⟩ := hu.sx
  have := hu.ua_lt; have := hu.ub_lt
  have e10 : (BitVec.ofNat 64 pa).toNat = pa := by rw [BitVec.toNat_ofNat]; omega
  have e11 : (BitVec.ofNat 64 pb).toNat = pb := by rw [BitVec.toNat_ofNat]; omega
  refine sym_at (stops := [0x800007a8#64]) (dpcs := loadPcs mpCmpMagBase mpCmpMagCode)
    (geom% (geomRun (C [0x800007a8#64]) 20 ⟨entry, [], [], []⟩)) 20 entry R m (by decide) ?_ ?_
  · geom_auto [h10, h11, e10, e11, mem_ramA, tohostAddr]
  · sym_close [retL] [entryL] [h1, h10, h11, e10, e11, hsa, hsb]

theorem lt_step (ra : BitVec 64) (v : Abi) (outp : Array String) (pa pb ua ub : Nat) (m : Mem)
    (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hra : ra.toNat % 4 = 0)
    (hu : UsedRead m pa pb ua ub) (hlt : ua < ub) (hgp : v.gp = gpV) :
    Triple (At entry (entryL ra pa pb) m v.keep outp) (At ra (retL ra neg1) m v.keep outp) := by
  cmp_ro retL
  have h1 : R 1 = ra := hL (_, _) (by simp [entryL])
  have h10 : R 10 = BitVec.ofNat 64 pa := hL (10, BitVec.ofNat 64 pa) (by simp [entryL])
  have h11 : R 11 = BitVec.ofNat 64 pb := hL (11, BitVec.ofNat 64 pb) (by simp [entryL])
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hu.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hu.rb
  have ⟨hsa, hsb⟩ := hu.sx
  have := hu.ua_lt; have := hu.ub_lt
  have e10 : (BitVec.ofNat 64 pa).toNat = pa := by rw [BitVec.toNat_ofNat]; omega
  have e11 : (BitVec.ofNat 64 pb).toNat = pb := by rw [BitVec.toNat_ofNat]; omega
  refine sym_at (stops := [0x800007a8#64]) (dpcs := loadPcs mpCmpMagBase mpCmpMagCode)
    (geom% (geomRun (C [0x800007a8#64]) 20 ⟨entry, [], [], []⟩)) 20 entry R m (by decide) ?_ ?_
  · geom_auto [h10, h11, e10, e11, mem_ramA, tohostAddr]
  · sym_close [retL] [entryL] [h1, h10, h11, e10, e11, hsa, hsb]

theorem zero_step (ra : BitVec 64) (v : Abi) (outp : Array String) (pa pb : Nat) (m : Mem)
    (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hra : ra.toNat % 4 = 0)
    (hu : UsedRead m pa pb 0 0) (hgp : v.gp = gpV) :
    Triple (At entry (entryL ra pa pb) m v.keep outp) (At ra (retL ra 0#64) m v.keep outp) := by
  cmp_ro retL
  have h1 : R 1 = ra := hL (_, _) (by simp [entryL])
  have h10 : R 10 = BitVec.ofNat 64 pa := hL (10, BitVec.ofNat 64 pa) (by simp [entryL])
  have h11 : R 11 = BitVec.ofNat 64 pb := hL (11, BitVec.ofNat 64 pb) (by simp [entryL])
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hu.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hu.rb
  have ⟨hsa, hsb⟩ := hu.sx
  have e10 : (BitVec.ofNat 64 pa).toNat = pa := by rw [BitVec.toNat_ofNat]; omega
  have e11 : (BitVec.ofNat 64 pb).toNat = pb := by rw [BitVec.toNat_ofNat]; omega
  refine sym_at (stops := [0x800007a8#64]) (dpcs := loadPcs mpCmpMagBase mpCmpMagCode)
    (geom% (geomRun (C [0x800007a8#64]) 20 ⟨entry, [], [], []⟩)) 20 entry R m (by decide) ?_ ?_
  · geom_auto [h10, h11, e10, e11, mem_ramA, tohostAddr]
  · sym_close [retL] [entryL] [h1, h10, h11, e10, e11, hsa, hsb]

theorem enter_step (ra : BitVec 64) (v : Abi) (outp : Array String) (pa pb u adp bdp : Nat)
    (m : Mem) (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hu : UsedRead m pa pb u u) (hu1 : 1 ≤ u)
    (hda : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp) (hdb : bytesT8 m (pb + 16) = BitVec.ofNat 64 bdp)
    (hra : Ram adp (4 * u)) (hrb : Ram bdp (4 * u)) (hgp : v.gp = gpV) :
    Triple (At entry (entryL ra pa pb) m v.keep outp)
      (At 0x800007a8#64 (headL ra adp bdp (u - 1)) m v.keep outp) := by
  cmp_ro headL
  have h1 : R 1 = ra := hL (_, _) (by simp [entryL])
  have h10 : R 10 = BitVec.ofNat 64 pa := hL (10, BitVec.ofNat 64 pa) (by simp [entryL])
  have h11 : R 11 = BitVec.ofNat 64 pb := hL (11, BitVec.ofNat 64 pb) (by simp [entryL])
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hu.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hu.rb
  have ⟨hA1, hA2, hA3⟩ := ram_bounds hra
  have ⟨hB1, hB2, hB3⟩ := ram_bounds hrb
  have ⟨hsa, hsb⟩ := hu.sx
  have := hu.ua_lt
  have e10 : (BitVec.ofNat 64 pa).toNat = pa := by rw [BitVec.toNat_ofNat]; omega
  have e11 : (BitVec.ofNat 64 pb).toNat = pb := by rw [BitVec.toNat_ofNat]; omega
  have f10 : (BitVec.ofNat 64 pa + 16#64).toNat = pa + 16 := by
    rw [toNat_ofNat_add]; omega
  have f11 : (BitVec.ofNat 64 pb + 16#64).toNat = pb + 16 := by
    rw [toNat_ofNat_add]; omega
  refine sym_at (stops := [0x800007a8#64]) (dpcs := loadPcs mpCmpMagBase mpCmpMagCode)
    (geom% (geomRun (C [0x800007a8#64]) 20 ⟨entry, [], [], []⟩)) 20 entry R m (by decide) ?_ ?_
  · geom_auto [h10, h11, e10, e11, mem_ramA, tohostAddr]
  · sym_close [headL] [entryL] [h1, h10, h11, e10, e11, f10, f11, hsa, hsb, hda, hdb]

/-! ## The loop-head runs (fuel-bounded: one iteration) -/

theorem dgt_step (ra : BitVec 64) (v : Abi) (outp : Array String) (adp bdp i da db : Nat) (m : Mem)
    (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hra : ra.toNat % 4 = 0)
    (hd : DigRead m adp bdp i da db) (hgt : db < da) (hgp : v.gp = gpV) :
    Triple (At 0x800007a8#64 (headL ra adp bdp i) m v.keep outp) (At ra (retL ra 1#64) m v.keep outp) := by
  cmp_ro retL
  have h1 : R 1 = ra := hL (_, _) (by simp [headL])
  have h14 : R 14 = BitVec.ofNat 64 (bdp + 4 * i) := hL (14, BitVec.ofNat 64 (bdp + 4 * i)) (by simp [headL])
  have h15 : R 15 = BitVec.ofNat 64 (adp + 4 * i) := hL (15, BitVec.ofNat 64 (adp + 4 * i)) (by simp [headL])
  have h11 : R 11 = BitVec.ofNat 64 (adp - 4) := hL (11, BitVec.ofNat 64 (adp - 4)) (by simp [headL])
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hd.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hd.rb
  have ⟨hsa, hsb⟩ := hd.sx
  have := hd.da_lt; have := hd.db_lt
  have e14 : (BitVec.ofNat 64 (bdp + 4 * i)).toNat = bdp + 4 * i := by rw [BitVec.toNat_ofNat]; omega
  have e15 : (BitVec.ofNat 64 (adp + 4 * i)).toNat = adp + 4 * i := by rw [BitVec.toNat_ofNat]; omega
  refine sym_at (stops := []) (dpcs := loadPcs mpCmpMagBase mpCmpMagCode)
    (geom% (geomRun (C []) 7 ⟨0x800007a8#64, [], [], []⟩)) 8 0x800007a8#64 R m (by decide) ?_ ?_
  · geom_auto [h14, h15, e14, e15, mem_ramA, tohostAddr]
  · sym_close [retL] [headL] [h1, h11, h14, h15, e14, e15, hsa, hsb]

theorem dlt_step (ra : BitVec 64) (v : Abi) (outp : Array String) (adp bdp i da db : Nat) (m : Mem)
    (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hra : ra.toNat % 4 = 0)
    (hd : DigRead m adp bdp i da db) (hlt : da < db) (hgp : v.gp = gpV) :
    Triple (At 0x800007a8#64 (headL ra adp bdp i) m v.keep outp) (At ra (retL ra neg1) m v.keep outp) := by
  cmp_ro retL
  have h1 : R 1 = ra := hL (_, _) (by simp [headL])
  have h14 : R 14 = BitVec.ofNat 64 (bdp + 4 * i) := hL (14, BitVec.ofNat 64 (bdp + 4 * i)) (by simp [headL])
  have h15 : R 15 = BitVec.ofNat 64 (adp + 4 * i) := hL (15, BitVec.ofNat 64 (adp + 4 * i)) (by simp [headL])
  have h11 : R 11 = BitVec.ofNat 64 (adp - 4) := hL (11, BitVec.ofNat 64 (adp - 4)) (by simp [headL])
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hd.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hd.rb
  have ⟨hsa, hsb⟩ := hd.sx
  have := hd.da_lt; have := hd.db_lt
  have e14 : (BitVec.ofNat 64 (bdp + 4 * i)).toNat = bdp + 4 * i := by rw [BitVec.toNat_ofNat]; omega
  have e15 : (BitVec.ofNat 64 (adp + 4 * i)).toNat = adp + 4 * i := by rw [BitVec.toNat_ofNat]; omega
  refine sym_at (stops := []) (dpcs := loadPcs mpCmpMagBase mpCmpMagCode)
    (geom% (geomRun (C []) 7 ⟨0x800007a8#64, [], [], []⟩)) 9 0x800007a8#64 R m (by decide) ?_ ?_
  · geom_auto [h14, h15, e14, e15, mem_ramA, tohostAddr]
  · sym_close [retL] [headL] [h1, h11, h14, h15, e14, e15, hsa, hsb]

theorem dend_step (ra : BitVec 64) (v : Abi) (outp : Array String) (adp bdp i da db : Nat) (m : Mem)
    (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hra : ra.toNat % 4 = 0)
    (hd : DigRead m adp bdp i da db) (heq : da = db) (hi : i = 0) (hgp : v.gp = gpV) :
    Triple (At 0x800007a8#64 (headL ra adp bdp i) m v.keep outp) (At ra (retL ra 0#64) m v.keep outp) := by
  cmp_ro retL
  have h1 : R 1 = ra := hL (_, _) (by simp [headL])
  have h14 : R 14 = BitVec.ofNat 64 (bdp + 4 * i) := hL (14, BitVec.ofNat 64 (bdp + 4 * i)) (by simp [headL])
  have h15 : R 15 = BitVec.ofNat 64 (adp + 4 * i) := hL (15, BitVec.ofNat 64 (adp + 4 * i)) (by simp [headL])
  have h11 : R 11 = BitVec.ofNat 64 (adp - 4) := hL (11, BitVec.ofNat 64 (adp - 4)) (by simp [headL])
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hd.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hd.rb
  have ⟨hsa, hsb⟩ := hd.sx
  have := hd.da_lt; have := hd.db_lt
  have e14 : (BitVec.ofNat 64 (bdp + 4 * i)).toNat = bdp + 4 * i := by rw [BitVec.toNat_ofNat]; omega
  have e15 : (BitVec.ofNat 64 (adp + 4 * i)).toNat = adp + 4 * i := by rw [BitVec.toNat_ofNat]; omega
  refine sym_at (stops := []) (dpcs := loadPcs mpCmpMagBase mpCmpMagCode)
    (geom% (geomRun (C []) 7 ⟨0x800007a8#64, [], [], []⟩)) 10 0x800007a8#64 R m (by decide) ?_ ?_
  · geom_auto [h14, h15, e14, e15, mem_ramA, tohostAddr]
  · sym_close [retL] [headL] [h1, h11, h14, h15, e14, e15, hsa, hsb]

theorem dnext_step (ra : BitVec 64) (v : Abi) (outp : Array String) (adp bdp i da db : Nat) (m : Mem)
    (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hd : DigRead m adp bdp i da db) (heq : da = db)
    (hi : 1 ≤ i) (hgp : v.gp = gpV) :
    Triple (At 0x800007a8#64 (headL ra adp bdp i) m v.keep outp)
      (At 0x800007a8#64 (headL ra adp bdp (i - 1)) m v.keep outp) := by
  cmp_ro headL
  have h14 : R 14 = BitVec.ofNat 64 (bdp + 4 * i) := hL (14, BitVec.ofNat 64 (bdp + 4 * i)) (by simp [headL])
  have h15 : R 15 = BitVec.ofNat 64 (adp + 4 * i) := hL (15, BitVec.ofNat 64 (adp + 4 * i)) (by simp [headL])
  have h11 : R 11 = BitVec.ofNat 64 (adp - 4) := hL (11, BitVec.ofNat 64 (adp - 4)) (by simp [headL])
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hd.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hd.rb
  have ⟨hsa, hsb⟩ := hd.sx
  have := hd.da_lt; have := hd.db_lt
  have e14 : (BitVec.ofNat 64 (bdp + 4 * i)).toNat = bdp + 4 * i := by rw [BitVec.toNat_ofNat]; omega
  have e15 : (BitVec.ofNat 64 (adp + 4 * i)).toNat = adp + 4 * i := by rw [BitVec.toNat_ofNat]; omega
  refine sym_at (stops := []) (dpcs := loadPcs mpCmpMagBase mpCmpMagCode)
    (geom% (geomRun (C []) 7 ⟨0x800007a8#64, [], [], []⟩)) 7 0x800007a8#64 R m (by decide) ?_ ?_
  · geom_auto [h14, h15, e14, e15, mem_ramA, tohostAddr]
  · sym_close [headL] [headL] [h11, h14, h15, e14, e15, hsa, hsb]

/-- The exits of the entry run: the three returns and the loop head. -/
def entryExits (ra : BitVec 64) (ua ub adp bdp : Nat) (m : Mem) : List Exit :=
  [⟨ub < ua, ra, retL ra 1#64, m⟩, ⟨ua < ub, ra, retL ra neg1, m⟩, ⟨ua = 0 ∧ ub = 0, ra, retL ra 0#64, m⟩,
   ⟨ua = ub ∧ 1 ≤ ua, 0x800007a8#64, headL ra adp bdp (ua - 1), m⟩]

/-- **The whole entry stretch in one run**: `gt_step`, `lt_step`, `zero_step` and `enter_step`
(three branches, four exits). -/
theorem entry_run (ra : BitVec 64) (v : Abi) (outp : Array String) (pa pb ua ub adp bdp : Nat)
    (m : Mem) (hc : CodeAt m mpCmpMagBase mpCmpMagCode) (hra : ra.toNat % 4 = 0)
    (hu : UsedRead m pa pb ua ub)
    (hda : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp) (hdb : bytesT8 m (pb + 16) = BitVec.ofNat 64 bdp)
    (hrA : Ram adp (4 * ua)) (hrB : Ram bdp (4 * ua)) (hgp : v.gp = gpV) :
    Triple (At entry (entryL ra pa pb) m v.keep outp)
      (fun c => ∃ x ∈ entryExits ra ua ub adp bdp m, x.guard ∧ At x.pc x.L x.m v.keep outp c) := by
  refine triple_of_swp_any (rs := rs) (S := fun _ => False) (DA := ramA) hc
    (by simp [Abi.keep, *]) (by decide) (fun _ _ h => h) (fun _ _ h => h) (fun _ h => h.elim)
    (by intro x hx a _; simp only [entryExits, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> rfl)
    (fun _ _ _ h => h.elim)
    (by simp only [entryExits, retL, headL, List.forall_mem_cons, List.not_mem_nil, false_implies,
          implies_true, and_true]; decide)
    (by simp [Abi.keep, sKeepL]) ?_
  intro R hL hK
  have h1 : R 1 = ra := hL (_, _) (by simp [entryL])
  have h10 : R 10 = BitVec.ofNat 64 pa := hL (10, BitVec.ofNat 64 pa) (by simp [entryL])
  have h11 : R 11 = BitVec.ofNat 64 pb := hL (11, BitVec.ofNat 64 pb) (by simp [entryL])
  have ⟨ha1, ha2, ha3⟩ := ram_bounds hu.ra
  have ⟨hb1, hb2, hb3⟩ := ram_bounds hu.rb
  have ⟨hA1, hA2, hA3⟩ := ram_bounds hrA
  have ⟨hB1, hB2, hB3⟩ := ram_bounds hrB
  have ⟨hsa, hsb⟩ := hu.sx
  have := hu.ua_lt; have := hu.ub_lt
  have e10 : (BitVec.ofNat 64 pa).toNat = pa := by rw [BitVec.toNat_ofNat]; omega
  have e11 : (BitVec.ofNat 64 pb).toNat = pb := by rw [BitVec.toNat_ofNat]; omega
  have f10 : (BitVec.ofNat 64 pa + 16#64).toNat = pa + 16 := by rw [toNat_ofNat_add]; omega
  have f11 : (BitVec.ofNat 64 pb + 16#64).toNat = pb + 16 := by rw [toNat_ofNat_add]; omega
  refine sym_at (stops := [0x800007a8#64]) (dpcs := loadPcs mpCmpMagBase mpCmpMagCode)
    (geom% (geomRun (C [0x800007a8#64]) 20 ⟨entry, [], [], []⟩)) 20 entry R m (by decide) ?_ ?_
  · geom_auto [h10, h11, e10, e11, mem_ramA, tohostAddr]
  · sym_close_any [entryExits, retL, headL] [entryL] [h1, h10, h11, e10, e11, f10, f11, hsa, hsb, hda, hdb]

end Tom.Machine.Fn.CmpMag.SymP
