import Tom.Machine.Fn.Reduce2kL
import Tom.Machine.Api.Reduce2kL

/-!
# `mp_reduce_is_2k_l` on the machine: the whole function

`used ≤ 1`: one chain each. Otherwise the entry chain to the loop head at
index `0` with count `0`, the loop by induction on `used - i` with the count
`countMax a.digit i`, and after the last digit the `seqz` and the return.
No store: memory is unchanged.
-/

namespace Tom.Machine.Fn.Reduce2kL

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

/-- After the loop: `seqz`, then return `!(c < used / 2)`. -/
theorem tail (ra : BitVec 64) (v : Abi) (outp : Array String) (m : Mem)
    (hc : CodeAt m mpReduceIs2kLBase mpReduceIs2kLCode) (hra : ra.toNat % 4 = 0) (c u : Nat) :
    Triple (At 0x80001df8#64 (a4L ra (BitVec.ofNat 64 (if c < u / 2 then 1 else 0))) m v.keep outp)
      (At ra (retL ra (BitVec.ofNat 64 (if u / 2 ≤ c then 1 else 0))) m v.keep outp) := by
  refine Triple.seq (seqz_step ra v outp m hc _ (by split <;> omega)) ?_
  rw [show (if (if c < u / 2 then 1 else 0) = 0 then 1 else 0) = (if u / 2 ≤ c then 1 else 0) by
    by_cases h : c < u / 2
    · simp [h, show ¬ u / 2 ≤ c by omega]
    · simp [h, show u / 2 ≤ c by omega]]
  exact ret_step ra v outp m hc hra _

theorem loop (ra : BitVec 64) (v : Abi) (outp : Array String) (pa adp : Nat) (a : MpInt) (m : Mem)
    (hP : Api.Reduce2kL.Pre m pa adp a ra) :
    ∀ k i, i + k = a.used → i < a.used →
      Triple (At 0x80001de0#64 (headL ra adp a.used i (countMax a.digit i)) m v.keep outp)
        (At ra (retL ra (BitVec.ofNat 64 (if a.used / 2 ≤ countMax a.digit a.used then 1 else 0))) m v.keep outp) := by
  have hc := hP.img.mpReduceIs2kL
  have hra := hP.ra_al
  have hd := hP.ga.ds
  simp only [Layout.sizeofDigit] at hd
  have hul := hP.sa.used_le; have hal := hP.sa.alloc_lt
  intro k
  induction k with
  | zero => intro i h1 h3; omega
  | succ k ih =>
    intro i h1 h3
    have hdl := hP.sa.digit_lt i
    simp only [radix, Layout.digitBits] at hdl
    have hf : DFacts m adp a.used i (a.digit i) (countMax a.digit i) :=
      { rd := ⟨by have := hd.lo_ge; omega, by have := hd.hi_le; omega, by have := hd.off; omega⟩
        arr := by have := hd.hi_le; omega
        d_v := by simpa [Layout.sizeofDigit] using hP.ra_.digits i (by omega)
        d_lt := by omega
        i_lt := h3
        u_lt := by omega
        c_le := countMax_le _ _ }
    have hcs : countMax a.digit (i + 1) = countMax a.digit i + if a.digit i = Layout.mpMask then 1 else 0 := rfl
    by_cases hm : a.digit i = 268435455
    · have hcs' : countMax a.digit (i + 1) = countMax a.digit i + 1 := by
        rw [hcs]; simp [Layout.mpMask, hm]
      by_cases hlast : i + 1 = a.used
      · refine Triple.seq (eqEnd_step ra v outp m hc adp a.used i _ _ hf hm hlast) ?_
        rw [← hlast, hcs']
        exact tail ra v outp m hc hra _ _
      · refine Triple.seq (eqNext_step ra v outp m hc adp a.used i _ _ hf hm (by omega)) ?_
        rw [← hcs']
        exact ih (i + 1) (by omega) (by omega)
    · have hcs' : countMax a.digit (i + 1) = countMax a.digit i := by
        rw [hcs]; simp [Layout.mpMask, hm]
      by_cases hlast : i + 1 = a.used
      · refine Triple.seq (neEnd_step ra v outp m hc adp a.used i _ _ hf hm hlast) ?_
        rw [← hlast, hcs']
        exact tail ra v outp m hc hra _ _
      · refine Triple.seq (neNext_step ra v outp m hc adp a.used i _ _ hf hm (by omega)) ?_
        rw [← hcs']
        exact ih (i + 1) (by omega) (by omega)

/-- **`mp_reduce_is_2k_l` on the machine.** -/
theorem correct : Api.Reduce2kL.Statement := by
  intro m v outp pa adp a ra hP
  have hc := hP.img.mpReduceIs2kL
  have hal := hP.sa.alloc_lt; have hul := hP.sa.used_le
  have hu : UFacts m pa a.used := UFacts.of hP.ra_ hP.ga hP.sa
  show Triple _ (At ra (retL ra (BitVec.ofNat 64 (isReduce2kL a))) m v.keep outp)
  unfold isReduce2kL
  by_cases h0 : a.used = 0
  · simp only [h0, ↓reduceIte]; rw [h0] at hu
    exact zero_step ra v outp m hc pa hP.ra_al hu
  by_cases h1 : a.used = 1
  · simp only [h1, ↓reduceIte]; rw [h1] at hu
    exact one_step ra v outp m hc pa hP.ra_al hu
  simp only [h0, h1, ↓reduceIte]
  refine Triple.seq (enter_step ra v outp m hc pa adp a.used hu (by omega)
    (by simpa [Layout.offDp] using hP.ra_.dpv)) ?_
  exact loop ra v outp pa adp a m hP a.used 0 (by omega) (by omega)

end Tom.Machine.Fn.Reduce2kL
