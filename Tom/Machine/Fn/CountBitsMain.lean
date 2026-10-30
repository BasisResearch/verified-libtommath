import Tom.Machine.Fn.CountBits
import Tom.Machine.Api.CountBits

/-!
# `mp_count_bits` on the machine: the whole function

Zero: one chain. Otherwise the entry chain to the loop head with `q` the top
digit and `r = 28 (used - 1)`, then the loop by induction on `q`
(`bitLen_step`). No store: memory is unchanged.
-/

namespace Tom.Machine.Fn.CountBits

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

/-- The loop from the head with `q ≠ 0`: returns `r + bitLen q`. -/
theorem loop (ra : BitVec 64) (v : Abi) (outp : Array String) (m : Mem)
    (hc : CodeAt m mpCountBitsBase mpCountBitsCode) (hra : ra.toNat % 4 = 0) :
    ∀ n q r, q ≤ n → q ≠ 0 → q < 2 ^ 31 → r + bitLen q < 2 ^ 31 →
      Triple (At 0x8000511c#64 (loopL ra q r) m v.keep outp)
        (At ra (retL ra (BitVec.ofNat 64 (r + bitLen q))) m v.keep outp) := by
  intro n
  induction n with
  | zero => intro q r h1 h2; omega
  | succ n ih =>
    intro q r h1 h2 h3 h4
    rw [bitLen_step h2] at h4 ⊢
    by_cases h5 : q / 2 = 0
    · rw [h5, bitLen_zero]
      rw [h5, bitLen_zero] at h4
      exact exit_step ra v outp q r m hc hra h3 (by omega) h5
    · refine Triple.seq (loop_step ra v outp q r m hc h3 (by omega) h5) ?_
      rw [show r + (bitLen (q / 2) + 1) = (r + 1) + bitLen (q / 2) by omega]
      exact ih (q / 2) (r + 1) (by omega) h5 (by omega) (by omega)

/-- **`mp_count_bits` on the machine.** -/
theorem correct : Api.CountBits.Statement := by
  intro m v outp pa adp a ra hP
  have hc := hP.img.mpCountBits
  have hra := hP.ra_al
  have hul := hP.va.used_le; have hal := hP.va.alloc_lt; have hb := hP.bits
  simp only [Layout.digitBits] at hb
  have hu : UFacts m pa a.used := UFacts.of hP.ra_ hP.ga hP.va.toShape
  show Triple _ (At ra (retL ra (BitVec.ofNat 64 (countBits a))) m v.keep outp)
  unfold countBits
  by_cases h0 : a.used = 0
  · simp only [h0, ↓reduceIte]
    rw [h0] at hu
    exact zero_step ra v outp pa m hc hra hu
  simp only [h0, ↓reduceIte, Layout.digitBits]
  have htop := hP.va.top (by omega)
  have htl := hP.va.digit_lt (a.used - 1)
  simp only [radix, Layout.digitBits] at htl
  have hd := hP.ga.ds
  simp only [Layout.sizeofDigit] at hd
  have ht : TFacts m pa adp a.used (a.digit (a.used - 1)) :=
    { rt := ⟨by have := hd.lo_ge; omega, by have := hd.hi_le; omega, by have := hd.off; omega⟩
      dp_v := by simpa [Layout.offDp] using hP.ra_.dpv
      t_v := by simpa [Layout.sizeofDigit] using hP.ra_.digits (a.used - 1) (by omega)
      t_lt := by omega
      u_pos := by omega
      r_lt := hb }
  have hbl := bitLen_le (k := 28) htl
  refine Triple.seq (enter_step ra v outp pa adp a.used _ m hc hu ht htop) ?_
  exact loop ra v outp m hc hra _ _ _ (Nat.le_refl _) htop (by omega) (by omega)

end Tom.Machine.Fn.CountBits
