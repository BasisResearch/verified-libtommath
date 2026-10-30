import Tom.Machine.Fn.Exch
import Tom.Machine.Api.Exch
import Tom.Machine.Api.Bin
import Tom.Machine.Kit.Bytes

/-!
# `mp_exch` on the machine: the whole function

The four segments of `Tom.Machine.Fn.Exch`, the code kept by `Frm.keep`.
The log is `logA ++ logB`; each field of the swapped structs is read back
from its entry (`bytesT4_log_sd`, `bytesT4_log_sw`, `bytesT8_log`), the
digit arrays by `Frm.keep`.
-/

namespace Tom.Machine.Fn.Exch

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api
open Tom.Machine.Api.Two (R isW2)

section
variable {m : Mem} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra : BitVec 64}

local notation "ρ" => Two.lay 0 sp pa adp pb bdp a b

theorem facts (hP : Exch.Pre m sp pa adp pb bdp a b ra) : Facts m pa pb a.sign :=
  have hab := hP.lay.disj (r := R.aS) (s := R.bS)
  have hac := hP.lay.sub (r := R.aS) (s := R.code) (Iv.sub_self _) (Bin.sub_text (b := mpExchBase) (k := 52))
  have hbc := hP.lay.sub (r := R.bS) (s := R.code) (Iv.sub_self _) (Bin.sub_text (b := mpExchBase) (k := 52))
  { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
    pa_al := hP.ga.st_al, pb_al := hP.gb.st_al
    ab := by simpa [Iv.Disj, Disj, Two.lay] using hab
    a_code := by simp only [Iv.Disj, Disj, Two.lay] at hac; omega
    b_code := by simp only [Iv.Disj, Disj, Two.lay] at hbc; omega
    sa_v := by simpa [Layout.offSign] using hP.ra_.sign
    sa_lt := hP.sgn }

theorem logA_in : LogIn ρ R.aS (logA m pa pb) :=
  ⟨by simp only [Iv.Sub, Two.lay]; omega, by simp only [Iv.Sub, Two.lay]; omega,
   by simp only [Iv.Sub, Two.lay]; omega, trivial⟩

theorem logB_in : LogIn ρ R.bS (logB m pa pb a.sign) :=
  ⟨by simp only [Iv.Sub, Two.lay]; omega, by simp only [Iv.Sub, Two.lay]; omega,
   by simp only [Iv.Sub, Two.lay]; omega, trivial⟩

/-- The swapped structs, read back from the log. -/
theorem post (hP : Exch.Pre m sp pa adp pb bdp a b ra) :
    Exch.Post m sp pa adp pb bdp a b (writeLog m (logA m pa pb ++ logB m pa pb a.sign)) := by
  have hf := facts hP
  have hab := hf.ab
  have hF : Frm ρ [R.aS, R.bS] m (writeLog m (logA m pa pb ++ logB m pa pb a.sign)) := by
    rw [writeLog_append]; exact (Frm.store logA_in).trans (Frm.store logB_in)
  have hAa := hF.keep hP.lay (ArrAt.reads (r := R.aD) (Iv.sub_self _)) hP.ra_.arr
  have hAb := hF.keep hP.lay (ArrAt.reads (r := R.bD) (Iv.sub_self _)) hP.rb.arr
  have hs := hP.sgn
  refine { ra_ := ?_, rb := ?_, frame := hF }
  · refine { used := ?_, alloc := ?_, sign := ?_, dpv := ?_, digits := ?_ }
    · rw [← hP.rb.used]
      exact bytesT4_log_sd _ m m 0 pa pb 0 (by omega) rfl (by simp [OutLRange, logA, logB]; omega)
    · rw [← hP.rb.alloc]
      exact bytesT4_log_sd _ m m 0 pa pb 4 (by omega) rfl (by simp [OutLRange, logA, logB]; omega)
    · rw [← hP.rb.sign]
      have := bytesT4_log_sd (logA m pa pb ++ logB m pa pb a.sign) m m 1 (pa + 8) (pb + 8) 0 (by omega) rfl
        (by simp [OutLRange, logA, logB]; omega)
      simp only [Nat.add_zero] at this
      exact this
    · rw [← hP.rb.dpv]
      exact bytesT8_log _ m 2 (pa + 16) _ rfl (by simp [OutLRange, logA, logB]; omega)
    · intro i hi; simpa [Layout.sizeofDigit] using hAb i hi
  · refine { used := ?_, alloc := ?_, sign := ?_, dpv := ?_, digits := ?_ }
    · rw [← hP.ra_.used]
      exact bytesT4_log_sd _ m m 3 pb pa 0 (by omega) rfl (by simp [OutLRange, logA, logB])
    · rw [← hP.ra_.alloc]
      exact bytesT4_log_sd _ m m 3 pb pa 4 (by omega) rfl (by simp [OutLRange, logA, logB])
    · exact bytesT4_log_sw _ m 4 (pb + 8) a.sign (by omega) rfl (by simp [OutLRange, logA, logB])
    · rw [← hP.ra_.dpv]
      exact bytesT8_log _ m 5 (pb + 16) _ rfl (by simp [OutLRange, logA, logB])
    · intro i hi; simpa [Layout.sizeofDigit] using hAa i hi

end

/-- **`mp_exch` on the machine.** -/
theorem correct : Api.Exch.Statement := by
  intro m v outp sp pa adp pb bdp a b ra hP
  have hf := facts hP
  have hab := hf.ab
  have hra := hP.ra_al
  have hS := hP.lay
  have hF1 : Frm (Two.lay 0 sp pa adp pb bdp a b) [R.aS] m (writeLog m [(pa, 8, bytesT8 m pb)]) :=
    Frm.store (by simp only [LogIn, Iv.Sub, Two.lay, and_true]; omega)
  have hF2 : Frm (Two.lay 0 sp pa adp pb bdp a b) [R.aS] (writeLog m [(pa, 8, bytesT8 m pb)])
      (writeLog (writeLog m [(pa, 8, bytesT8 m pb)]) [(pa + 8, 8, bytesT8 m (pb + 8))]) :=
    Frm.store (by simp only [LogIn, Iv.Sub, Two.lay, and_true]; omega)
  have hF3 : Frm (Two.lay 0 sp pa adp pb bdp a b) [R.aS]
      (writeLog (writeLog m [(pa, 8, bytesT8 m pb)]) [(pa + 8, 8, bytesT8 m (pb + 8))])
      (writeLog (writeLog (writeLog m [(pa, 8, bytesT8 m pb)]) [(pa + 8, 8, bytesT8 m (pb + 8))])
        [(pa + 16, 8, bytesT8 m (pb + 16))]) :=
    Frm.store (by simp only [LogIn, Iv.Sub, Two.lay, and_true]; omega)
  have hI1 := hF1.keep hS (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
  have hI2 := (hF1.trans hF2).keep hS (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
  have hI3 := ((hF1.trans hF2).trans hF3).keep hS (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
  have hM : writeLog (writeLog (writeLog (writeLog m [(pa, 8, bytesT8 m pb)]) [(pa + 8, 8, bytesT8 m (pb + 8))])
      [(pa + 16, 8, bytesT8 m (pb + 16))]) (logB m pa pb a.sign) = writeLog m (logA m pa pb ++ logB m pa pb a.sign) := by
    rw [← writeLog_append, ← writeLog_append, ← writeLog_append]; rfl
  refine Triple.seq (s1 ra v outp pa pb a.sign m hf hP.img.mpExch)
    (Triple.seq (s2 ra v outp pa pb a.sign m hf _ hI1.mpExch
      (bytesT8_sd_out _ _ _ _ (by omega)) (bytesT8_sd_out _ _ _ _ (by omega)))
    (Triple.seq (s3 ra v outp pa pb a.sign m hf _ hI2.mpExch
      (by rw [bytesT8_sd_out _ _ _ _ (by omega), bytesT8_sd_out _ _ _ _ (by omega)]))
    (Triple.rmap (fun cf h => ⟨_, hM ▸ h, post hP⟩) (s4 ra v outp pa pb a.sign m hf _ hI3.mpExch hra))))

end Tom.Machine.Fn.Exch
