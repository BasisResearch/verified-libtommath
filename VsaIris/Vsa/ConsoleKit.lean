import Vsa.Machine

/-!
# The image-free excerpt of `VsaIris/Vsa/Console.lean` that `SymObs` uses
-/

namespace VsaIris.Inst

open Sail

theorem addInt_ofNat_four (p : Nat) :
    BitVec.addInt (BitVec.ofNat 64 p) 4 = BitVec.ofNat 64 (p + 4) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.addInt, BitVec.toNat_add]

end VsaIris.Inst
