import Tom.Machine.Fn.DrIsModulus
import Tom.Machine.Api.DrIsModulus

/-!
# `mp_dr_is_modulus` on the machine: the whole function

`used < 2`: one chain. Otherwise the entry chain to the loop head at index
`1`, then the loop by induction on `used - i`, with the digits `1 … i-1`
known to be `MP_MASK`. No store: memory is unchanged.
-/

namespace Tom.Machine.Fn.DrIsModulus

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

/-- The loop from index `i`. -/
theorem loop (ra : BitVec 64) (v : Abi) (outp : Array String) (pa adp : Nat) (a : MpInt) (m : Mem)
    (hP : Api.DrIsModulus.Pre m pa adp a ra) (hu2 : 2 ≤ a.used) :
    ∀ k i, i + k = a.used → 1 ≤ i → i < a.used → (∀ j, 1 ≤ j → j < i → a.digit j = Layout.mpMask) →
      Triple (At 0x800055c4#64 (headL ra adp a.used i) m v.keep outp)
        (At ra (retL ra (BitVec.ofNat 64 (if IsDrModulus a then 1 else 0))) m v.keep outp) := by
  have hc := hP.img.mpDrIsModulus
  have hra := hP.ra_al
  have hd := hP.ga.ds
  simp only [Layout.sizeofDigit] at hd
  have hul := hP.sa.used_le
  intro k
  induction k with
  | zero => intro i h1 _ h3; omega
  | succ k ih =>
    intro i h1 h2 h3 h4
    have hdl := hP.sa.digit_lt i
    simp only [radix, Layout.digitBits] at hdl
    have hf : DFacts m adp a.used i (a.digit i) :=
      { rd := ⟨by have := hd.lo_ge; omega, by have := hd.hi_le; omega, by have := hd.off; omega⟩
        arr := by have := hd.hi_le; omega
        d_v := by simpa [Layout.sizeofDigit] using hP.ra_.digits i (by omega)
        d_lt := by omega
        i_lt := h3 }
    by_cases hm : a.digit i = 268435455
    · by_cases hlast : i + 1 = a.used
      · have hdm : IsDrModulus a := ⟨hu2, fun j hj1 hj2 => by
            rcases Nat.lt_or_ge j i with hj | hj
            · exact h4 j hj1 hj
            · rw [show j = i by omega, hm]; rfl⟩
        simp only [hdm, ↓reduceIte]
        exact yes_step ra v outp m hc adp a.used i _ hra hf hm hlast
      · refine Triple.seq (next_step ra v outp m hc adp a.used i _ hf hm (by omega)) ?_
        exact ih (i + 1) (by omega) (by omega) (by omega) fun j hj1 hj2 => by
          rcases Nat.lt_or_ge j i with hj | hj
          · exact h4 j hj1 hj
          · rw [show j = i by omega, hm]; rfl
    · have hdm : ¬ IsDrModulus a := fun h => hm (by have := h.2 i (by omega) h3; simpa [Layout.mpMask] using this)
      simp only [hdm, ↓reduceIte]
      exact no_step ra v outp m hc adp a.used i _ hra hf hm

/-- **`mp_dr_is_modulus` on the machine.** -/
theorem correct : Api.DrIsModulus.Statement := by
  intro m v outp pa adp a ra hP
  have hc := hP.img.mpDrIsModulus
  have hal := hP.sa.alloc_lt; have hul := hP.sa.used_le
  have hu : UFacts m pa a.used := UFacts.of hP.ra_ hP.ga hP.sa
  show Triple _ (At ra (retL ra (BitVec.ofNat 64 (if IsDrModulus a then 1 else 0))) m v.keep outp)
  by_cases h2 : a.used < 2
  · have hdm : ¬ IsDrModulus a := fun h => by have := h.1; omega
    simp only [hdm, ↓reduceIte]
    exact small_step ra v outp m hc pa a.used hP.ra_al hu h2
  have hd := hP.ga.ds
  simp only [Layout.sizeofDigit] at hd
  refine Triple.seq (enter_step ra v outp m hc pa adp a.used hu (by omega)
    (by simpa [Layout.offDp] using hP.ra_.dpv) (by have := hd.hi_le; omega)) ?_
  exact loop ra v outp pa adp a m hP (by omega) (a.used - 1) 1 (by omega) (Nat.le_refl _) (by omega)
    (fun j h1 h2 => by omega)

end Tom.Machine.Fn.DrIsModulus
