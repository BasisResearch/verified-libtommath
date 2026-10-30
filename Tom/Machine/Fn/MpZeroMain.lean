import Tom.Machine.Api.MpZero
import Tom.Machine.Kit.Frame
import Tom.Machine.Kit.Call

/-!
# `mp_zero` on the machine: the whole function

The two segments of `Tom.Machine.Fn.MpZero`; on the `alloc > 0` path the
tail-called `memset` (`Memset.correct_zero`, entered with our `ra` and ABI
registers). Regions are `Un`'s; the stores are in `aS` (`Frm.store`), the
fill in `aD` (`ArrFrm.fill`).
-/

namespace Tom.Machine.Fn.MpZero

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api
open Tom.Machine.Api.Un (R isW ws)

section
variable {m : Mem} {sp pa adp : Nat} {a : MpInt} {ra : BitVec 64}

local notation "ρ" => Un.lay 0 sp pa adp a

theorem sfacts (hP : MpZero.Pre m sp pa adp a ra) : SFacts m pa adp a.alloc :=
  have h := hP.lay.disj (r := R.aS) (s := R.code)
  { rp := by simpa [Layout.sizeofMpInt] using hP.ga.st, p_al := hP.ga.st_al
    al_v := by simpa [Layout.offAlloc] using hP.ra_.alloc
    dp_v := by simpa [Layout.offDp] using hP.ra_.dpv
    al_lt := hP.sa.alloc_lt
    code_off := by
      simp only [Iv.Disj, Disj, Un.lay, textIv, textBase, textLen] at h
      simp only [mpZeroBase]; omega }

/-- The header stores, in `aS`. -/
theorem f1 : Frm ρ [R.aS] m (writeLog m (zlog pa)) :=
  Frm.store (by simp only [LogIn, zlog, Iv.Sub, Un.lay, and_true]; omega)

/-- After the header stores: `a` with `sign := 0`, `used := 0`. -/
theorem hdr (hP : MpZero.Pre m sp pa adp a ra) :
    MpAt (writeLog m (zlog pa)) pa adp { a with sign := 0, used := 0 } := by
  have h := (hP.ra_.set_sign hP.ga 0 (by decide)).set_used hP.ga 0 (by decide)
  rw [← writeLog_append] at h
  exact h

end

/-- **`mp_zero` on the machine.** -/
theorem correct : Api.MpZero.Statement := by
  intro m v outp sp pa adp a ra hP
  have hS := hP.lay
  have hsf := sfacts hP
  have hF1 := f1 (sp := sp) (pa := pa) (adp := adp) (a := a) (m := m)
  have hA1 := hdr hP
  have himg := hF1.keep hS (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
  by_cases h0 : a.alloc = 0
  · rw [h0] at hsf
    refine Triple.rmap (fun cf h => ⟨a.zeroed, _, h, ?_⟩)
      (e_step ra v outp pa adp m hP.img.mpZero hsf hP.ra_al)
    exact { repr := hA1.of_hdr (fun _ _ _ => rfl) (fun j hj => absurd hj (by simp [h0])) rfl rfl rfl
            zero := ZeroPost.zeroed a
            frame := hF1.mono }
  have hrd : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have hms : Memset.Pre (writeLog m (zlog pa)) adp 0 (4 * a.alloc) :=
    memset_pre hS (r := R.aD) (c := R.code) himg (Iv.sub_self _) (Iv.sub_self _) hrd
  refine Triple.seq (m_step ra v outp pa adp a.alloc m hP.img.mpZero hsf (by omega))
    (Triple.rmap (fun cf ⟨M, hat, hpost⟩ => ⟨a.zeroed, M, hat.weaken (by simp), ?_⟩)
      (Memset.correct_zero ra v outp _ adp (4 * a.alloc) hP.ra_al hms))
  have hI0 : ArrFrm (Un.lay 0 sp pa adp a) R.aD (writeLog m (zlog pa)) (writeLog m (zlog pa)) adp a.alloc
      (ovl (fun _ => 0) a.digit 0) :=
    ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; exact hA1.arr)
  have hI := hI0.fill (k := a.alloc) (Nat.zero_le _) (Nat.le_refl _)
    (fun t ht => by simpa using hpost.fill t (by omega)) (fun x hx => hpost.frame x (by omega))
    (fun _ _ _ => rfl)
  exact { repr := hA1.of_hdr (fun x h1 h2 => (Frm.on (r := R.aS) hS hI.fr) x ⟨h1, h2⟩)
            (hI.arr.congr fun j hj => by simp [ovl, MpInt.zeroed, MpInt.ofDigits_digit, hj]) rfl rfl rfl
          zero := ZeroPost.zeroed a
          frame := (hF1.trans hI.fr).mono }

end Tom.Machine.Fn.MpZero
