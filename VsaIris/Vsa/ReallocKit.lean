import VsaIris.Vsa.AllocKit

/-!
# Two word facts of the `MallocFastSegs` that its `realloc` proofs use

ship-your-interpreter's `VsaIris/Vsa/MallocFastSegs.lean` (its fast-path
segment tables, at the WHILE ELF's addresses) is not in this repository. These
two theorems are verbatim from it (lines 147-148 and 691-694 @0534d832); the
relocated `ReallocCtx` imports this module (`modules.json` `add`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace VsaIris.MallocFast

open Vsa.Sim

theorem ult_false_iff (a b : BitVec 64) : zopz0zI_u a b = false ↔ b.toNat ≤ a.toNat := by
  unfold zopz0zI_u; simp [Sail.BitVec.toNatInt]

theorem and_m2_toNat (a : BitVec 64) :
    (a &&& sign_extend (m := 64) (0xffe#12)).toNat = a.toNat / 2 * 2 := by
  rw [show (sign_extend (m := 64) (0xffe#12) : BitVec 64) = BitVec.allOnes 64 <<< 1 by decide,
    and_high_toNat a 1 (by decide)]

end VsaIris.MallocFast
