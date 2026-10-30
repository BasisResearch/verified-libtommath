import Tom.Machine.Fn.CmpS
import Tom.Machine.Fn.CmpMag
import Tom.Machine.Api.CmpS

/-!
# `mp_cmp` on the machine: the whole function

Different signs: one chain each. Equal signs: a chain to `mp_cmp_mag`'s
entry (operands swapped when both are negative), then `CmpMag.correct`.
-/

namespace Tom.Machine.Fn.CmpS

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code
open Tom.Machine.Fn.MpSub (SFacts)

theorem sfacts {m : Mem} {pa adp pb bdp : Nat} {a b : MpInt} {ra : BitVec 64}
    (hP : Api.CmpS.Pre m pa adp pb bdp a b ra) : SFacts m pa pb a.sign b.sign :=
  have ha := hP.va.sign_ok; have hb := hP.vb.sign_ok
  { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
    sa_v := by simpa [Layout.offSign] using hP.ra_.sign
    sb_v := by simpa [Layout.offSign] using hP.rb.sign
    sa_lt := by simp only [Layout.mpZpos, Layout.mpNeg] at ha; omega
    sb_lt := by simp only [Layout.mpZpos, Layout.mpNeg] at hb; omega }

/-- **`mp_cmp` on the machine.** -/
theorem correct : Api.CmpS.Statement := by
  intro m v outp pa adp pb bdp a b ra hP
  have hc := hP.img.mpCmp
  have hf := sfacts hP
  have hra := hP.ra_al
  have hsa := hP.va.sign_ok; have hsb := hP.vb.sign_ok
  simp only [Layout.mpZpos, Layout.mpNeg] at hsa hsb
  show Triple _ (At ra (retL ra (BitVec.ofInt 64 (ordCode (cmpS a b)))) m v.keep outp)
  unfold cmpS
  by_cases he : a.sign = b.sign
  · simp only [he, ne_eq, not_true_eq_false, ↓reduceIte]
    by_cases hn : b.sign = Layout.mpNeg
    · simp only [hn, ↓reduceIte]
      rw [cmpMag_eq hP.vb hP.va]
      refine Triple.seq (neg_step ra v outp pa pb _ _ m hc hf he (by simpa [Layout.mpNeg] using hn)) ?_
      exact CmpMag.correct ra v outp pb bdp pa adp b a m hra
        { ra := hP.rb, rb := hP.ra_, va := hP.vb, vb := hP.va, ga := hP.gb, gb := hP.ga
          code := hP.img.mpCmpMag }
    · simp only [hn, ↓reduceIte]
      rw [cmpMag_eq hP.va hP.vb]
      refine Triple.seq (pos_step ra v outp pa pb _ _ m hc hf he (by simpa [Layout.mpNeg] using hn)) ?_
      exact CmpMag.correct ra v outp pa adp pb bdp a b m hra
        { ra := hP.ra_, rb := hP.rb, va := hP.va, vb := hP.vb, ga := hP.ga, gb := hP.gb
          code := hP.img.mpCmpMag }
  · simp only [ne_eq, he, not_false_eq_true, ↓reduceIte]
    by_cases hn : a.sign = Layout.mpNeg
    · simp only [hn, ↓reduceIte]; rw [show BitVec.ofInt 64 (ordCode .lt) = neg1 by decide]
      exact lt_step ra v outp pa pb _ _ m hc hf hra he (by simpa [Layout.mpNeg] using hn)
    · simp only [hn, ↓reduceIte]; rw [show BitVec.ofInt 64 (ordCode .gt) = 1#64 by decide]
      exact gt_step ra v outp pa pb _ _ m hc hf hra he (by simpa [Layout.mpNeg] using hn)

end Tom.Machine.Fn.CmpS
