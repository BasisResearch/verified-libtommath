import Tom.Machine.Kit.Arr
import Tom.Machine.Repr
import Tom.Spec.Signed

/-!
# A struct copied by doubleword loads and stores

`mp_add_d` and `mp_sub_d` call each other on a stack copy `a_ = *a` with the
sign changed (`mp_int a_ = *a; a_.sign = MP_ZPOS;`): GCC copies the 24-byte
struct by three `ld`/`sd` pairs and stores the new sign by one `sw`. The
copy holds `a.withSign s` (`MpAt.copy`) when its two doublewords at `x`
and `x + 16` read as the source's and its sign word as `s`: a doubleword's
halves are the two words (`bytesT4_lo`, `bytesT4_hi`).
-/

namespace Tom.Machine

open Vsa.Sim

theorem cat8_lo (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0).extractLsb' 0 32) =
      (((b3.append b2).append b1).append b0) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bv_append_eq, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have h1 : i < 64 := by omega
  repeat' split
  all_goals first | rfl | omega | (simp_all; done) | (congr 1; omega) | (simp only [hi, decide_true, Bool.true_and]; congr 1; omega) | skip
theorem cat8_hi (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0).extractLsb' 32 32) =
      (((b7.append b6).append b5).append b4) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bv_append_eq, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  repeat' split
  all_goals first | rfl | omega | (simp_all; done) | (congr 1; omega) | (simp only [hi, decide_true, Bool.true_and]; congr 1; omega) | skip

/-- The low word of a doubleword. -/
theorem bytesT4_lo (M : Mem) (a : Nat) : bytesT4 M a = (bytesT8 M a).extractLsb' 0 32 :=
  (cat8_lo _ _ _ _ _ _ _ _).symm

/-- The high word of a doubleword. -/
theorem bytesT4_hi (M : Mem) (a : Nat) : bytesT4 M (a + 4) = (bytesT8 M a).extractLsb' 32 32 := by
  have h := (cat8_hi ((M[a]?).getD 0) ((M[a + 1]?).getD 0) ((M[a + 2]?).getD 0) ((M[a + 3]?).getD 0)
    ((M[a + 4]?).getD 0) ((M[a + 5]?).getD 0) ((M[a + 6]?).getD 0) ((M[a + 7]?).getD 0)).symm
  simp only [bytesT4, bytesT8, Nat.add_assoc] at h ⊢
  exact h

/-- **The copy**: doublewords at `x` and `x + 16` as the source's at `p`, the
sign word `s`, the digits where they were. -/
theorem MpAt.copy {m M : Mem} {p x dp : Nat} {a : MpInt} (h : MpAt m p dp a) (s : Nat)
    (h0 : bytesT8 M x = bytesT8 m p) (h16 : bytesT8 M (x + 16) = bytesT8 m (p + 16))
    (hs : bytesT4 M (x + 8) = BitVec.ofNat 32 s) (hd : ArrAt M dp a.alloc a.digit) :
    MpAt M x dp (a.withSign s) :=
  { used := by
      simp only [Layout.offUsed, Nat.add_zero, MpInt.withSign]
      rw [bytesT4_lo, h0, ← bytesT4_lo]; simpa [Layout.offUsed] using h.used
    alloc := by
      simp only [Layout.offAlloc, MpInt.withSign]
      rw [bytesT4_hi, h0, ← bytesT4_hi]; simpa [Layout.offAlloc] using h.alloc
    sign := by simpa [Layout.offSign] using hs
    dpv := by simp only [Layout.offDp]; rw [h16]; simpa [Layout.offDp] using h.dpv
    digits := fun i hi => by simpa [Layout.sizeofDigit, MpInt.withSign, MpInt.digit] using hd i hi }

end Tom.Machine
