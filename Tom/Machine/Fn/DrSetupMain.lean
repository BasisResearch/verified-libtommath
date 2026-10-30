import Tom.Machine.Fn.DrSetup
import Tom.Machine.Api.DrSetup
import Tom.Machine.Api.Bin

/-!
# `mp_dr_setup` on the machine: the whole function

One segment; its one store is the frame (`Frm.sw`) and the result
(`bytesT4_sw_self`).
-/

namespace Tom.Machine.Fn.DrSetup

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api
open Tom.Machine.Api.DrSetup (R)

/-- **`mp_dr_setup` on the machine.** -/
theorem correct : Api.DrSetup.Statement := by
  intro m v outp pa adp pd a ra hP
  have hd := hP.ga.ds
  simp only [Layout.sizeofDigit] at hd
  have := hP.alloc_pos
  have hdl := hP.sa.digit_lt 0
  simp only [radix, Layout.digitBits] at hdl
  have hpc := hP.lay.sub (r := R.dW) (s := R.code) (Iv.sub_self _) (Bin.sub_text (b := mpDrSetupBase) (k := 24))
  simp only [Iv.Disj, Disj, DrSetup.lay] at hpc
  have hf : Facts m pa adp pd (a.digit 0) :=
    { rs := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rd := ⟨hd.lo_ge, by have := hd.hi_le; omega, by have := hd.off; omega⟩
      rw_ := hP.rd
      dp_v := by simpa [Layout.offDp] using hP.ra_.dpv
      d_v := by simpa [Layout.sizeofDigit] using hP.ra_.digits 0 (by omega)
      d_le := by omega
      pd_al := hP.pd_al
      pd_code := by omega }
  refine Triple.rmap (fun cf h => ⟨_, h, ?_, Frm.sw (by simp only [Iv.Sub, DrSetup.lay]; omega)⟩)
    (step ra v outp pa adp pd _ m hP.img.mpDrSetup hP.ra_al hf)
  exact bytesT4_sw_self m pd _ (by omega)

end Tom.Machine.Fn.DrSetup
