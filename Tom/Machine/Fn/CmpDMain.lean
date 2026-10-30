import Tom.Machine.Fn.CmpD
import Tom.Machine.Api.CmpD

/-!
# `mp_cmp_d` on the machine: the whole function

The four branches of `Tom.Spec.cmpD`, each a chain of `Tom.Machine.Fn.CmpD`
(the last through the `sltu` step). No store: memory is unchanged.
-/

namespace Tom.Machine.Fn.CmpD

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

theorem facts {m : Mem} {pa adp : Nat} {a : MpInt} {b : Nat} {ra : BitVec 64}
    (hP : Api.CmpD.Pre m pa adp a b ra) : Facts m pa adp a.sign a.used (a.digit 0) :=
  have hd := hP.ga.ds
  have := hP.va.alloc_lt; have := hP.va.used_le; have := hP.va.digit_lt 0; have := hP.va.sign_ok
  have := hP.alloc_pos
  { rs := by simpa [Layout.sizeofMpInt] using hP.ga.st
    rd := ⟨hd.lo_ge, by have := hd.hi_le; simp only [Layout.sizeofDigit] at this; omega,
      by have := hd.off; simp only [Layout.sizeofDigit] at this; omega⟩
    s_v := by simpa [Layout.offSign] using hP.ra_.sign
    u_v := by simpa [Layout.offUsed] using hP.ra_.used
    dp_v := by simpa [Layout.offDp] using hP.ra_.dpv
    d_v := by simpa [Layout.sizeofDigit] using hP.ra_.digits 0 (by omega)
    s_lt := by simp only [Layout.mpZpos, Layout.mpNeg] at *; omega
    u_lt := by omega
    d_lt := by simp only [radix, Layout.digitBits] at *; omega }

/-- **`mp_cmp_d` on the machine.** -/
theorem correct : Api.CmpD.Statement := by
  intro m v outp pa adp a b ra hP
  have hc := hP.img.mpCmpD
  have hf := facts hP
  have hra := hP.ra_al
  have hb : b < 2 ^ 31 := by have := hP.db; simp only [radix, Layout.digitBits] at this; omega
  show Triple _ (At ra (retL ra (BitVec.ofInt 64 (ordCode (cmpD a b)))) m v.keep outp)
  unfold cmpD
  by_cases hn : a.sign = Layout.mpNeg
  · simp only [hn, ↓reduceIte]; rw [show BitVec.ofInt 64 (ordCode .lt) = neg1 by decide]
    exact neg_step ra v outp pa adp b _ _ _ m hc hf hra (by simpa [Layout.mpNeg] using hn)
  have hn' : a.sign ≠ 1 := by simpa [Layout.mpNeg] using hn
  simp only [hn, ↓reduceIte]
  by_cases hu : 1 < a.used
  · simp only [hu, ↓reduceIte]; rw [show BitVec.ofInt 64 (ordCode .gt) = 1#64 by decide]
    exact gt1_step ra v outp pa adp b _ _ _ m hc hf hra hn' hu
  simp only [hu, ↓reduceIte]
  by_cases hgt : b < a.digit 0
  · rw [Nat.compare_eq_gt.2 hgt, show BitVec.ofInt 64 (ordCode .gt) = 1#64 by decide]
    exact gt2_step ra v outp pa adp b _ _ _ m hc hf hra hb hn' (by omega) hgt
  refine Triple.seq (le_step ra v outp pa adp b _ _ _ m hc hf hb hn' (by omega) (by omega))
    (Triple.seq (sltu_step ra v outp b _ m hc hb hf.d_lt) ?_)
  by_cases hlt : a.digit 0 < b
  · simp only [hlt, ↓reduceIte]; rw [Nat.compare_eq_lt.2 hlt, show BitVec.ofInt 64 (ordCode .lt) = neg1 by decide]
    exact tail_lt ra v outp m hc hra
  · simp only [hlt, ↓reduceIte]; rw [show compare (a.digit 0) b = .eq from Nat.compare_eq_eq.2 (by omega),
      show BitVec.ofInt 64 (ordCode .eq) = 0#64 by decide]
    exact tail_eq ra v outp m hc hra

end Tom.Machine.Fn.CmpD
