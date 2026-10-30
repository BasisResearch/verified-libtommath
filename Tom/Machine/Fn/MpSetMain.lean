import Tom.Machine.Api.MpSet
import Tom.Machine.Kit.Frame
import Tom.Machine.Kit.MpStore
import Tom.Machine.Kit.Call

/-!
# `mp_set` on the machine: the whole function

The segments of `Tom.Machine.Fn.MpSet`: the stores `dp[0] := d`,
`sign := 0` (`a_step`), the reloads and the `snez` (`b_step`, `z_step`), the
`used` store, then either the return (`alloc = used`) or the tail-called
`memset` of digits `[used, alloc)` (`ArrFrm.fill` from the memory after the
`used` store). Regions are `Un`'s.
-/

namespace Tom.Machine.Fn.MpSet

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api
open Tom.Machine.Api.Un (R isW ws)

section
variable {m : Mem} {sp pa adp : Nat} {a : MpInt} {ra : BitVec 64}

local notation "ρ" => Un.lay 0 sp pa adp a

theorem sfacts (hP : MpSet.Pre m sp pa adp a ra) : SFacts m pa adp :=
  have h1 := hP.lay.disj (r := R.aS) (s := R.code)
  have h2 := hP.lay.disj (r := R.aD) (s := R.code)
  have hr := hP.ga.ds
  have := hP.room
  { rp := by simpa [Layout.sizeofMpInt] using hP.ga.st, p_al := hP.ga.st_al
    rd := ⟨hr.lo_ge, by have := hr.hi_le; simp only [Layout.sizeofDigit] at this; omega,
      by have := hr.off; simp only [Layout.sizeofDigit] at this; omega⟩
    dp_al := hP.ga.ds_al
    dp_v := by simpa [Layout.offDp] using hP.ra_.dpv
    code_p := by
      simp only [Iv.Disj, Disj, Un.lay, textIv, textBase, textLen] at h1
      simp only [mpSetBase]; omega
    code_d := by
      simp only [Iv.Disj, Disj, Un.lay, textIv, textBase, textLen] at h2
      simp only [mpSetBase]; omega }

/-- `a` after `dp[0] := d`, `sign := 0`, `used := u`. -/
abbrev a3 (a : MpInt) (d u : Nat) : MpInt := { { { a with digits := a.digits.set 0 d } with sign := 0 } with used := u }

theorem a3_digit (hl : a.digits.length = a.alloc) (hal : 1 ≤ a.alloc) (d u j : Nat) :
    (a3 a d u).digit j = if j = 0 then d else a.digit j :=
  MpInt.digit_set a 0 d j (by omega)

end

/-- **`mp_set` on the machine.** -/
theorem correct : Api.MpSet.Statement := by
  intro m v outp sp pa adp a bn ra hP
  have hS := hP.lay
  have hsf := sfacts hP
  have hal := hP.room; have hal2 := hP.sa.alloc_lt; have hl := hP.sa.len
  have ⟨hp1, hp2, hp3⟩ := ram_bounds hsf.rp
  have hrd : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  generalize hd : bn % 268435456 = d
  have hdl : d < 268435456 := hd ▸ Nat.mod_lt _ (by decide)
  generalize hu : (if d = 0 then 0 else 1) = u
  have hu1 : u ≤ 1 := by rw [← hu]; split <;> omega
  -- the stores
  have h1 : MpAt (writeLog m [(adp, 4, BitVec.ofNat 64 d)]) pa adp { a with digits := a.digits.set 0 d } := by
    simpa using hP.ra_.set_digit hP.ga hl 0 d (by omega) (by omega)
  have h2 := h1.set_sign hP.ga 0 (by decide)
  have hF1 : Frm (Un.lay 0 sp pa adp a) [R.aD] m (writeLog m [(adp, 4, BitVec.ofNat 64 d)]) :=
    Frm.sw (by simp only [Iv.Sub, Un.lay]; omega)
  have hF2 : Frm (Un.lay 0 sp pa adp a) [R.aS] (writeLog m [(adp, 4, BitVec.ofNat 64 d)])
      (writeLog (writeLog m [(adp, 4, BitVec.ofNat 64 d)]) [(pa + 8, 4, 0#64)]) :=
    Frm.sw (by simp only [Iv.Sub, Un.lay]; omega)
  have he : writeLog m (alog pa adp d) =
      writeLog (writeLog m [(adp, 4, BitVec.ofNat 64 d)]) [(pa + 8, 4, 0#64)] :=
    writeLog_append m [(adp, 4, BitVec.ofNat 64 d)] [(pa + 8, 4, 0#64)]
  have hF12 := hF1.trans hF2
  rw [← he] at h2 hF12
  have himg := hF12.keep hS (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
  have hdv : bytesT4 (writeLog m (alog pa adp d)) adp = BitVec.ofNat 32 d := by
    have h := h2.digits 0 (by simp only; omega)
    simp only [Layout.sizeofDigit, Nat.mul_zero, Nat.add_zero] at h
    rw [h]; congr 1
    simp [MpInt.digit, List.getD_eq_getElem?_getD, hl, show 0 < a.alloc by omega]
  have hav : bytesT4 (writeLog m (alog pa adp d)) (pa + 4) = BitVec.ofNat 32 a.alloc := by
    simpa [Layout.offAlloc] using h2.alloc
  refine Triple.seq (hd ▸ a_step ra v outp pa adp bn m hP.img.mpSet hsf)
    (Triple.seq (b_step ra v outp pa adp d a.alloc _ himg.mpSet hsf.rp hsf.rd hdv hav (by omega) hal2)
      (Triple.seq (z_step ra v outp pa adp d a.alloc _ himg.mpSet (by omega)) ?_))
  rw [hu]
  have hF3 : Frm (Un.lay 0 sp pa adp a) [R.aS] (writeLog m (alog pa adp d))
      (writeLog (writeLog m (alog pa adp d)) [(pa, 4, BitVec.ofNat 64 u)]) :=
    Frm.sw (by simp only [Iv.Sub, Un.lay]; omega)
  have h3 : MpAt _ pa adp (a3 a d u) := h2.set_used hP.ga u (by omega)
  have hF123 := hF12.trans hF3
  have hcode := hsf.code_p
  -- the result, from `a3` and the final digits
  have hfin : ∀ {M : Mem}, (∀ x, pa ≤ x → x < pa + 24 →
      M[x]? = (writeLog (writeLog m (alog pa adp d)) [(pa, 4, BitVec.ofNat 64 u)])[x]?) →
      ArrAt M adp a.alloc (a.setTo d).digit → Frm (Un.lay 0 sp pa adp a) ws m M →
      MpSet.Post m sp pa adp a bn (a.setTo d) M := fun hs harr hF =>
    { repr := h3.of_hdr hs harr (by rw [← hu]; rfl) rfl rfl
      set := by rw [show bn % radix = d by rw [← hd]; rfl]; exact SetPost.setTo d hal
      frame := hF }
  by_cases hc0 : a.alloc ≤ u
  · refine Triple.rmap (fun cf h => ⟨a.setTo d, _, h, hfin (fun _ _ _ => rfl) ?_ hF123.mono⟩)
      (c0_step ra v outp pa adp u a.alloc _ himg.mpSet hsf.rp hsf.p_al hcode hP.ra_al hu1 hc0)
    refine h3.arr.congr fun j hj => ?_
    have hj0 : j = 0 := by simp only at hj; omega
    have hd0 : d ≠ 0 := fun h0 => by rw [h0] at hu; simp at hu; omega
    subst hj0
    simp [a3_digit hl hal, MpInt.setTo, MpInt.ofDigits_digit, show 0 < a.alloc by omega]
  · have hms : Memset.Pre (writeLog (writeLog m (alog pa adp d)) [(pa, 4, BitVec.ofNat 64 u)])
        (adp + 4 * u) 0 (4 * (a.alloc - u)) :=
      memset_pre hS (r := R.aD) (c := R.code) (hF3.keep hS (Img.reads (r := R.code) (Iv.sub_self _)) himg)
        (Iv.sub_self _) (by simp only [Iv.Sub, Un.lay]; omega)
        ⟨by have := hrd.lo_ge; omega, by have := hrd.hi_le; omega, by have := hrd.off; omega⟩
    refine Triple.seq (c1_step ra v outp pa adp u a.alloc _ himg.mpSet hsf.rp hsf.p_al hcode
        (by have := hrd.hi_le; omega) hu1 (by omega) hal2)
      (Triple.rmap (fun cf ⟨M, hat, hpost⟩ => ⟨a.setTo d, M, hat.weaken (by simp), ?_⟩)
        (Memset.correct_zero ra v outp _ _ _ hP.ra_al hms))
    let g : Nat → Nat := fun j => if j = 0 then d else 0
    have hI0 : ArrFrm (Un.lay 0 sp pa adp a) R.aD _ _ adp a.alloc (ovl g (a3 a d u).digit u) :=
      ArrFrm.init (Iv.sub_self _) (h3.arr.congr fun j hj => by
        by_cases h0 : j = 0
        · subst h0; simp [ovl, g, a3_digit hl hal]
        · have : ¬ j < u := by omega
          simp [ovl, g, a3_digit hl hal, h0, this])
    have hI := hI0.fill (k := a.alloc) (by omega) (Nat.le_refl _) hpost.fill hpost.frame (fun j hj _ => by
      simp only [g]; split
      · rename_i h0; subst h0
        by_cases hd0 : d = 0
        · exact hd0
        · exfalso; rw [← hu] at hj; simp [hd0] at hj
      · rfl)
    exact hfin (fun x h1 h2 => (Frm.on (r := R.aS) hS hI.fr) x ⟨h1, h2⟩)
      (hI.arr.congr fun j hj => by simp [ovl, hj, g, MpInt.setTo, MpInt.ofDigits_digit])
      (hF123.trans hI.fr).mono

end Tom.Machine.Fn.MpSet
