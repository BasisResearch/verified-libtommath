import Tom.Machine.Img
import Tom.Machine.Kit.Rodata
import Tom.Machine.Kit.Gen
import Tom.Spec.Radix

/-! `mp_to_radix`'s reads (per-function helper): the pointer `mp_s_rmap` and the 64
bytes it points to, from the image (`Img.ro1`, `Img.ro8`, Kit/Rodata.lean), in the forms the
assembly's `cfacts` applies. -/

namespace Tom.Machine.Fn.MpToRadixG5K

open Vsa.Sim Tom.Machine.Code Tom.Radix

/-! ## `mp_s_rmap`: the pointer at `0x80018808` and the 64 bytes at `0x80017818` -/

theorem rmap_bytes : ∀ j, j < 64 → rodataBytes[344 + j]? = some (BitVec.ofNat 8 (rmapAt j)) := by
  unfold rmapAt rmap; decide +kernel

theorem rmap_byte : ∀ M : Mem, Img M → ∀ j, j ≤ 63 → ∀ x, x = 0x80017818 + j →
    bytesT1 M x = BitVec.ofNat 8 (rmapAt j) := by
  intro M hM j hj x hx; subst hx
  rw [show 0x80017818 + j = rodataBase + (344 + j) by simp [rodataBase]; omega]
  exact (Img.ro1 hM (by have : rodataBytes.length = 4544 := by decide +kernel
                        omega)).trans (by rw [roByte, rmap_bytes j (by omega)]; rfl)

theorem rmap_ptr : ∀ M : Mem, Img M → bytesT8 M 0x80018808 = BitVec.ofNat 64 0x80017818 := fun M hM => by
  rw [show (0x80018808 : Nat) = rodataBase + 4424 from rfl, Img.ro8 hM (by decide +kernel)]; decide +kernel

end Tom.Machine.Fn.MpToRadixG5K
