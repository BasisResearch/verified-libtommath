import Tom.Machine.Api.ReadRadix
import Tom.Machine.Kit.Run

/-! `mp_read_radix`'s reads (per-function helper): a byte of the string, a byte of
`mp_s_rmap_reverse` and the word `mp_s_rmap_reverse_sz` from the image, in the forms the
assembly's `cfacts` applies (`∀ j, j ≤ n → ∀ x, x = base + j → …`). -/

namespace Tom.Machine.Fn.ReadRadixG5

open Vsa.Sim Tom.Machine.Code Tom.Radix

theorem str_byte {m : Mem} {pstr : Nat} {s : List Nat} (h : Api.ReadRadix.StrAt m pstr s) :
    ∀ j, j ≤ s.length → ∀ x, x = pstr + j → bytesT1 m x = BitVec.ofNat 8 (s.getD j 0) := by
  intro j hj x hx; subst hx
  rcases Nat.lt_or_eq_of_le hj with hj | rfl
  · rw [h.bytes j hj]; simp [List.getD_eq_getElem?_getD, hj]
  · rw [h.nul]; simp [List.getD_eq_getElem?_getD]

theorem rev_bytes : ∀ j, j < 89 → rodataBytes[0x600 + j]? = some (BitVec.ofNat 8 (revAt j)) := by
  unfold revAt rmapRev rmapRevPast; decide +kernel

theorem ty_byte : ∀ M : Mem, Img M → ∀ j, j ≤ 88 → ∀ x, x = 0x80017cc0 + j →
    bytesT1 M x = BitVec.ofNat 8 (revAt j) := by
  intro M hM j hj x hx; subst hx
  have := hM.rodata (0x600 + j) _ (rev_bytes j (by omega))
  rw [show 0x80017cc0 + j = rodataBase + (0x600 + j) by simp [rodataBase]; omega]
  simp [bytesT1, this]

theorem tz_word : ∀ M : Mem, Img M → bytesT8 M 0x80018800 = BitVec.ofNat 64 88 := by
  intro M hM
  have h : ∀ k, k < 8 → M[0x80018800 + k]? = some (if k = 0 then 88#8 else 0#8) := by
    intro k hk
    have e : 0x80018800 + k = rodataBase + (4416 + k) := by simp [rodataBase]; omega
    rw [e]
    refine hM.rodata _ _ ?_
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k
    all_goals first | omega | decide +kernel
  have h0 := h 0 (by decide); rw [Nat.add_zero] at h0
  unfold bytesT8
  rw [h0, h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide),
    h 7 (by decide)]
  decide

end Tom.Machine.Fn.ReadRadixG5
