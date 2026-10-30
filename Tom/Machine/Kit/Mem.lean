import Tom.Machine.Repr
import Vsa.Sim.Mfr

/-!
# Total reads through stores

A `sw` is the write-log entry `(a, 4, v)`, i.e. `writeMap4 m a (swData v)`.
`bytesT4_sw_self`: reading it back gives the low word; `bytesT4_sw_out`,
`bytesT8_sw_out`: reads off it are unchanged.

`MpAt.set_used`, `MpAt.set_sign`: storing a new `used` or `sign` into an
`mp_int` keeps its representation with that field changed.
-/

namespace Tom.Machine

open Vsa.Sim

theorem bytesT4_wm4_self (m : Mem) (a : Nat) (d : BitVec (8 * 4)) :
    bytesT4 (writeMap4 m a d) a = d := by
  simp only [bytesT4, writeMap4, Std.ExtHashMap.getElem?_insert, beq_iff_eq,
    show ¬ a + 3 = a + 1 by omega, show ¬ a + 3 = a + 2 by omega, show ¬ a + 3 = a by omega,
    show ¬ a + 2 = a + 1 by omega, show ¬ a + 2 = a by omega, show ¬ a + 1 = a by omega,
    show ¬ a + 2 = a + 3 by omega, show ¬ a + 1 = a + 3 by omega, show ¬ a = a + 3 by omega,
    show ¬ a + 1 = a + 2 by omega, show ¬ a = a + 2 by omega, show ¬ a = a + 1 by omega,
    if_true, if_false, Option.getD_some]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  show (((BitVec.extractLsb' 24 8 d ++ BitVec.extractLsb' 16 8 d) ++ BitVec.extractLsb' 8 8 d) ++
    BitVec.extractLsb' 0 8 d).getLsbD i = d.getLsbD i
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h1 : i < 8
  · simp [h1]
  · by_cases h2 : i - 8 < 8
    · simp [h1, h2]; congr 1; omega
    · by_cases h3 : i - 8 - 8 < 8
      · simp [h1, h2, h3]; congr 1; omega
      · simp [h1, h2, h3, show i - 8 - 8 - 8 < 8 by omega]; congr 1; omega

theorem swData_ofNat (n : Nat) (h : n < 2 ^ 32) : swData (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp [swData, Sail.BitVec.extractLsb, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]

theorem writeLog_sw (m : Mem) (a : Nat) (v : BitVec 64) :
    writeLog m [(a, 4, v)] = writeMap4 m a (swData v) := rfl

theorem bytesT4_sw_self (m : Mem) (a n : Nat) (h : n < 2 ^ 32) :
    bytesT4 (writeLog m [(a, 4, BitVec.ofNat 64 n)]) a = BitVec.ofNat 32 n := by
  rw [writeLog_sw, bytesT4_wm4_self, swData_ofNat n h]

theorem bytesT4_sw_out (m : Mem) (a x : Nat) (v : BitVec 64) (h : x + 4 ≤ a ∨ a + 4 ≤ x) :
    bytesT4 (writeLog m [(a, 4, v)]) x = bytesT4 m x := by
  rw [writeLog_sw]
  simp only [bytesT4]
  rw [getElem?_writeMap4_out m a _ x (by omega), getElem?_writeMap4_out m a _ (x + 1) (by omega),
    getElem?_writeMap4_out m a _ (x + 2) (by omega), getElem?_writeMap4_out m a _ (x + 3) (by omega)]

theorem bytesT8_sw_out (m : Mem) (a x : Nat) (v : BitVec 64) (h : x + 8 ≤ a ∨ a + 4 ≤ x) :
    bytesT8 (writeLog m [(a, 4, v)]) x = bytesT8 m x := by
  rw [writeLog_sw]
  simp only [bytesT8]
  rw [getElem?_writeMap4_out m a _ x (by omega), getElem?_writeMap4_out m a _ (x + 1) (by omega),
    getElem?_writeMap4_out m a _ (x + 2) (by omega), getElem?_writeMap4_out m a _ (x + 3) (by omega),
    getElem?_writeMap4_out m a _ (x + 4) (by omega), getElem?_writeMap4_out m a _ (x + 5) (by omega),
    getElem?_writeMap4_out m a _ (x + 6) (by omega), getElem?_writeMap4_out m a _ (x + 7) (by omega)]

theorem getElem?_sw_out (m : Mem) (a x : Nat) (v : BitVec 64) (h : x < a ∨ a + 4 ≤ x) :
    (writeLog m [(a, 4, v)])[x]? = m[x]? := by
  rw [writeLog_sw]; exact getElem?_writeMap4_out m a _ x h

/-- Storing `used := n`. -/
theorem MpAt.set_used {m : Mem} {p dp : Nat} {a : MpInt} (h : MpAt m p dp a)
    (hg : MpGeom p dp a.alloc) (n : Nat) (hn : n < 2 ^ 32) :
    MpAt (writeLog m [(p, 4, BitVec.ofNat 64 n)]) p dp { a with used := n } := by
  have hd := hg.disj
  simp only [Layout.sizeofMpInt, Layout.sizeofDigit] at hd
  refine { used := ?_, alloc := ?_, sign := ?_, dpv := ?_, digits := ?_ }
  · simp only [Layout.offUsed, Nat.add_zero]; exact bytesT4_sw_self m p n hn
  · rw [bytesT4_sw_out _ _ _ _ (by simp [Layout.offAlloc])]; exact h.alloc
  · rw [bytesT4_sw_out _ _ _ _ (by simp [Layout.offSign])]; exact h.sign
  · rw [bytesT8_sw_out _ _ _ _ (by simp [Layout.offDp])]; exact h.dpv
  · intro i hi
    rw [bytesT4_sw_out _ _ _ _ (by simp only [Layout.sizeofDigit] at *; omega)]
    exact h.digits i hi

/-- Storing `sign := s`. -/
theorem MpAt.set_sign {m : Mem} {p dp : Nat} {a : MpInt} (h : MpAt m p dp a)
    (hg : MpGeom p dp a.alloc) (s : Nat) (hs : s < 2 ^ 32) :
    MpAt (writeLog m [(p + 8, 4, BitVec.ofNat 64 s)]) p dp { a with sign := s } := by
  have hd := hg.disj
  simp only [Layout.sizeofMpInt, Layout.sizeofDigit] at hd
  refine { used := ?_, alloc := ?_, sign := ?_, dpv := ?_, digits := ?_ }
  · rw [bytesT4_sw_out _ _ _ _ (by simp [Layout.offUsed])]; exact h.used
  · rw [bytesT4_sw_out _ _ _ _ (by simp [Layout.offAlloc])]; exact h.alloc
  · simp only [Layout.offSign]; exact bytesT4_sw_self m (p + 8) s hs
  · rw [bytesT8_sw_out _ _ _ _ (by simp [Layout.offDp])]; exact h.dpv
  · intro i hi
    rw [bytesT4_sw_out _ _ _ _ (by simp only [Layout.sizeofDigit] at *; omega)]
    exact h.digits i hi

end Tom.Machine
