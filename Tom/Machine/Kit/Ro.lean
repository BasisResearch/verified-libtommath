import Tom.Machine.Img
import Tom.Spec.Bits

/-!
# Reading `.rodata`

`Img m` carries `RoAt m`: the bytes of `.rodata` (`Code.rodataBytes`) are in
`m` at `rodataBase`. `ro_word`/`ro_word8` read a word of it, the byte
lookups by `decide +kernel` on the literal list; `lnz_word` is
`mp_cnt_lsb`'s nibble table `lnz` (`Tom.lnzTab`).
-/

namespace Tom.Machine

open Tom.Machine.Code Vsa.Sim

/-- A word of `.rodata`. -/
theorem ro_word {m : Mem} (h : RoAt m) (i : Nat) (b0 b1 b2 b3 : BitVec 8)
    (h0 : rodataBytes[i]? = some b0) (h1 : rodataBytes[i + 1]? = some b1)
    (h2 : rodataBytes[i + 2]? = some b2) (h3 : rodataBytes[i + 3]? = some b3) :
    bytesT4 m (rodataBase + i) = b3 ++ b2 ++ b1 ++ b0 := by
  simp only [bytesT4, show rodataBase + i + 1 = rodataBase + (i + 1) by omega,
    show rodataBase + i + 2 = rodataBase + (i + 2) by omega, show rodataBase + i + 3 = rodataBase + (i + 3) by omega,
    h i b0 h0, h (i + 1) b1 h1, h (i + 2) b2 h2, h (i + 3) b3 h3, Option.getD_some]
  rfl

/-- A small word of `.rodata`. -/
theorem ro_word8 {m : Mem} (h : RoAt m) (i n : Nat) (hn : n < 256)
    (h0 : rodataBytes[i]? = some (BitVec.ofNat 8 n)) (h1 : rodataBytes[i + 1]? = some 0#8)
    (h2 : rodataBytes[i + 2]? = some 0#8) (h3 : rodataBytes[i + 3]? = some 0#8) :
    bytesT4 m (rodataBase + i) = BitVec.ofNat 32 n := by
  rw [ro_word h i _ _ _ _ h0 h1 h2 h3]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega)]
  show (0#24 ++ BitVec.ofNat 8 n).toNat = n
  rw [BitVec.toNat_append]; simp [Nat.mod_eq_of_lt hn]

/-- `lnz[j]` (`mp_cnt_lsb`'s table at `0x80017c80`). -/
theorem lnz_word {m : Mem} (h : RoAt m) : ∀ j, j < 16 →
    bytesT4 m (0x80017c80 + 4 * j) = BitVec.ofNat 32 (lnzTab j) := by
  intro j hj
  have e : 0x80017c80 + 4 * j = rodataBase + (0x5c0 + 4 * j) := by simp [rodataBase]; omega
  rw [e]
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals first | omega | exact ro_word8 h _ _ (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Tom.Machine
