import Tom.Machine.Kit.Mem

/-!
# A digit store into an `mp_int`

`MpAt.set_digit`: one `sw` of `v` into digit `i < alloc` keeps the
representation with that digit changed (`digits.set i v`), the companion of
`MpAt.set_used`/`MpAt.set_sign` (`Kit/Mem.lean`). `MpInt.digit_set` reads it.
-/

namespace Tom.Machine

open Vsa.Sim

theorem MpInt.digit_set (a : MpInt) (i v j : Nat) (hi : i < a.digits.length) :
    ({ a with digits := a.digits.set i v } : MpInt).digit j = if j = i then v else a.digit j := by
  simp only [MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = i
  · subst h; simp [hi]
  · simp [Ne.symm h, h]

/-- Storing digit `i := v`. -/
theorem MpAt.set_digit {m : Mem} {p dp : Nat} {a : MpInt} (h : MpAt m p dp a)
    (hg : MpGeom p dp a.alloc) (hl : a.digits.length = a.alloc) (i v : Nat) (hi : i < a.alloc)
    (hv : v < 2 ^ 32) :
    MpAt (writeLog m [(dp + 4 * i, 4, BitVec.ofNat 64 v)]) p dp { a with digits := a.digits.set i v } := by
  have hd := hg.disj
  simp only [Layout.sizeofMpInt, Layout.sizeofDigit] at hd
  refine { used := ?_, alloc := ?_, sign := ?_, dpv := ?_, digits := ?_ }
  · rw [bytesT4_sw_out _ _ _ _ (by simp only [Layout.offUsed]; omega)]; exact h.used
  · rw [bytesT4_sw_out _ _ _ _ (by simp only [Layout.offAlloc]; omega)]; exact h.alloc
  · rw [bytesT4_sw_out _ _ _ _ (by simp only [Layout.offSign]; omega)]; exact h.sign
  · rw [bytesT8_sw_out _ _ _ _ (by simp only [Layout.offDp]; omega)]; exact h.dpv
  · intro j hj
    rw [MpInt.digit_set a i v j (by omega)]
    simp only [Layout.sizeofDigit] at *
    by_cases hji : j = i
    · subst hji; simp only [ite_true]; exact bytesT4_sw_self m _ v hv
    · simp only [hji, ite_false]
      rw [bytesT4_sw_out _ _ _ _ (by omega)]
      simpa [Layout.sizeofDigit] using h.digits j hj

end Tom.Machine
