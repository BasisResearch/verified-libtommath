import Tom.Machine.Img

/-!
# Reads of the image's `.rodata`

`Img M` holds the `.rodata` bytes (`RoAt`). A byte or an 8-byte word read inside it is the table's
(`roByte`, `roWord8`: computed, so a concrete read closes by `decide +kernel`). Before, each function
reading a table proved the word byte by byte (`Fn/MpToRadixG5K.lean`'s `rmap_ptr`, 14 lines).
-/

namespace Tom.Machine

open Vsa.Sim Tom.Machine.Code

/-- The `.rodata` byte at offset `i` (0 past the end). -/
def roByte (i : Nat) : BitVec 8 := (rodataBytes[i]?).getD 0

/-- The little-endian word at offset `i`. -/
def roWord8 (i : Nat) : BitVec 64 :=
  (((((((roByte (i + 7)).append (roByte (i + 6))).append (roByte (i + 5))).append (roByte (i + 4))).append
    (roByte (i + 3))).append (roByte (i + 2))).append (roByte (i + 1))).append (roByte i)

theorem Img.ro1 {M : Mem} (hM : Img M) {i : Nat} (hi : i < rodataBytes.length) :
    bytesT1 M (rodataBase + i) = roByte i := by
  unfold roByte bytesT1
  rw [hM.rodata i _ (List.getElem?_eq_getElem hi), List.getElem?_eq_getElem hi]

theorem Img.ro8 {M : Mem} (hM : Img M) {i : Nat} (hi : i + 8 ≤ rodataBytes.length) :
    bytesT8 M (rodataBase + i) = roWord8 i := by
  have h : ∀ k, k < 8 → (M[rodataBase + i + k]?).getD 0 = roByte (i + k) := fun k hk => by
    rw [Nat.add_assoc]; exact Img.ro1 hM (by omega)
  have h0 := h 0 (by omega)
  simp only [Nat.add_zero] at h0
  unfold bytesT8 roWord8
  rw [h0, h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega), h 6 (by omega),
    h 7 (by omega)]

end Tom.Machine
