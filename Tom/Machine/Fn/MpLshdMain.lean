import Tom.Machine.Api.MpLshd
import Tom.Machine.Kit.Frame
import Tom.Machine.Kit.ArrSet
import Tom.Machine.Kit.Call

/-!
# `mp_lshd` on the machine: the whole function

The branches of `Tom.Machine.Fn.MpLshd`: `b = 0` or `used = 0` return;
otherwise the prologue (`ra` saved, `used := used + b`, the snapshot `m0Of`),
the loop from the top (`ASt.set`: `t` digits moved, overlay `fD`), the
`memset` of `[0, b)` (`ArrFrm.fill`), the epilogue. Regions are `Un`'s.
-/


namespace Tom.Machine.Fn.MpLshd

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api
open Tom.Machine.Api.Un (R isW ws)

/-- The digits after `t` iterations: `[used + b - t, used + b)` moved up by `b`. -/
def fD (a : MpInt) (b t j : Nat) : Nat :=
  if a.used + b - t ≤ j ∧ j < a.used + b then a.digit (j - b) else a.digit j

/-- The result. -/
def res (a : MpInt) (b : Nat) : MpInt := MpInt.ofDigits (a.used + b) a.alloc a.sign (lshdDigits a b)

/-- The memory after the prologue. -/
abbrev m0Of (m : Mem) (ra : BitVec 64) (sp pa u b : Nat) : Mem :=
  writeLog (writeLog m [(sp - 8, 8, ra)]) [(pa, 4, BitVec.ofNat 64 (u + b))]

theorem code_sub : Iv.Sub ⟨mpLshdBase, 200⟩ textIv := ⟨by decide, by decide⟩

theorem res_post {a : MpInt} {b : Nat} (ha : a.Shape) (hroom : a.used + b ≤ a.alloc) : LshdShift a b (res a b) :=
  { alloc := rfl, len := MpInt.ofDigits_len _ _ _ _, used := rfl, sign := rfl
    digit := fun i => by
      simp only [res, MpInt.ofDigits_digit]
      split
      · rfl
      · simp only [show ¬ i < b by omega, show ¬ i < a.used + b by omega, ite_false]
        exact (ha.high_zero i (by omega)).symm }

/-- **`mp_lshd` on the machine.** -/
theorem correct : Api.MpLshd.Statement := by
  intro m v outp sp pa adp a b ra s0 hP
  have hS := hP.lay
  have hua := hP.sa.used_le; have := hP.sa.alloc_lt; have := hP.sp_ge; have hroom := hP.room
  have hra : Ram pa 24 := by simpa [Layout.sizeofMpInt] using hP.ga.st
  have hrd : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have hsf : SFacts m pa adp a.used a.alloc :=
    { ra_ := hra, pa_al := hP.ga.st_al
      u_v := by simpa [Layout.offUsed] using hP.ra_.used
      al_v := by simpa [Layout.offAlloc] using hP.ra_.alloc
      dp_v := by simpa [Layout.offDp] using hP.ra_.dpv
      u_lt := by omega, al_lt := by omega }
  have hnoop : LshdPost a b a → ∀ cf, At ra (retL ra s0 sp) (writeLog m []) v.keepR outp cf →
      MpLshd.Ret m v outp sp pa adp a b ra s0 cf := fun hl cf h => ⟨a, m, h, hP.ra_, hl, Frm.refl _ _⟩
  rcases Nat.eq_zero_or_pos b with hb0 | hb
  · subst hb0
    exact Triple.rmap (hnoop ⟨fun _ => rfl, fun h => absurd h (Nat.lt_irrefl 0)⟩)
      (n_step ra s0 v outp sp pa m hP.img.mpLshd hP.ra_al)
  rcases Nat.eq_zero_or_pos a.used with hu0 | hu
  · rw [hu0] at hsf
    exact Triple.rmap (hnoop ⟨fun _ => rfl, fun _ h => absurd h (by omega)⟩)
      (z_step ra s0 v outp sp pa adp a.alloc b m hP.img.mpLshd hP.ra_al hsf hb hP.b_lt)
  have h1 := hS.disj (r := R.stk) (s := R.aS)
  have h2 := hS.sub (r := R.stk) (s := R.code) (Iv.sub_self _) code_sub
  have h3 := hS.sub (r := R.aS) (s := R.code) (Iv.sub_self _) code_sub
  simp only [Iv.Disj, Disj, Un.lay] at h1 h2 h3
  have hff : FFacts sp pa :=
    { rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
      s_a := by omega
      code_s := by omega
      code_a := by omega }
  -- the prologue
  have hF1 : Frm (Un.lay 32 sp pa adp a) [R.stk] m (writeLog m [(sp - 8, 8, ra)]) :=
    Frm.store (by simp only [LogIn, Iv.Sub, Un.lay, and_true]; omega)
  have hF2 : Frm (Un.lay 32 sp pa adp a) [R.aS] (writeLog m [(sp - 8, 8, ra)]) (m0Of m ra sp pa a.used b) :=
    Frm.sw (by simp only [Iv.Sub, Un.lay]; omega)
  have hF12 := hF1.trans hF2
  have hA1 := hF1.keep hS (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_
  have hdp : bytesT8 (writeLog m [(sp - 8, 8, ra)]) (pa + 16) = BitVec.ofNat 64 adp := by
    simpa [Layout.offDp] using hA1.dpv
  have hhdr : MpAt (m0Of m ra sp pa a.used b) pa adp { a with used := a.used + b } :=
    hA1.set_used hP.ga _ (by omega)
  have himg : ∀ {M : Mem} {ws' : List R}, Frm (Un.lay 32 sp pa adp a) ws' m M →
      Misses isW [R.code] ws' = true → Img M := fun hF hm =>
    hF.keep hS (Img.reads (r := R.code) (Iv.sub_self _)) hP.img hm
  have hI0 : ArrFrm (Un.lay 32 sp pa adp a) R.aD (m0Of m ra sp pa a.used b) (m0Of m ra sp pa a.used b) adp
      a.alloc (fD a b 0) :=
    ArrFrm.init (Iv.sub_self _) (hhdr.arr.congr fun j _ => by simp only [fD, Nat.sub_zero]; rw [if_neg (by omega)]; rfl)
  refine Triple.seq (e1_step ra s0 v outp sp pa adp a.used a.alloc b m hP.img.mpLshd hsf hff hb hP.b_lt hu hroom)
    (Triple.seq (Triple.rmap (fun cf h => (⟨_, hI0, h⟩ : ASt (Un.lay 32 sp pa adp a) R.aD (m0Of m ra sp pa a.used b)
        adp a.alloc v.keepR outp 0x800015ec#64 (e2L' s0 sp adp a.used b) (fD a b 0) cf))
      (e2_step s0 v outp sp pa adp a.used a.alloc b _ (himg hF1 (by decide)).mpLshd hra hP.ga.st_al (by omega) hdp
        hu hroom (by omega))) ?_)
  have hI3 : ∀ {M f}, ArrFrm (Un.lay 32 sp pa adp a) R.aD (m0Of m ra sp pa a.used b) M adp a.alloc f →
      CodeAt M mpLshdBase mpLshdCode := fun hI =>
    ((hF12.trans hI.fr).keep hS (Img.reads (r := R.code) (Iv.sub_self _)) hP.img).mpLshd
  refine Triple.seq (ASt.seg fun M hI => e2b_step s0 v outp sp adp a.used b M (hI3 hI) hb hu (by omega))
    (Triple.seq (ASt.seg fun M hI => e3_step s0 v outp sp adp a.used b M (hI3 hI) hb hu (by omega)
      (by have := hrd.hi_le; omega))
    (Triple.seq (ASt.seg fun M hI => e4_step s0 v outp sp adp a.used b M (hI3 hI) hb hu (by omega)
      (by have := hrd.hi_le; omega)) ?_))
  -- the loop
  have hseg : ∀ t, t < a.used → ∀ {pc' : BitVec 64} {L' : GRegs},
      (∀ M, CodeAt M mpLshdBase mpLshdCode → LFacts M adp a.used b t (a.digit (a.used - 1 - t)) →
        Triple (At 0x80001624#64 (kL s0 sp adp a.used b t) M v.keepR outp)
          (At pc' L' (writeLog M [(adp + 4 * (a.used + b - 1 - t), 4,
            BitVec.ofNat 64 (a.digit (a.used - 1 - t)))]) v.keepR outp)) →
      Triple (ASt (Un.lay 32 sp pa adp a) R.aD (m0Of m ra sp pa a.used b) adp a.alloc v.keepR outp
          0x80001624#64 (kL s0 sp adp a.used b t) (fD a b t))
        (ASt (Un.lay 32 sp pa adp a) R.aD (m0Of m ra sp pa a.used b) adp a.alloc v.keepR outp pc' L'
          (fD a b (t + 1))) := by
    intro t ht pc' L' h
    have hdl := hP.sa.digit_lt (a.used - 1 - t)
    simp only [radix, Layout.digitBits] at hdl
    refine ASt.set (fun M hI => h M ((hF12.trans hI.fr).keep hS (Img.reads (r := R.code) (Iv.sub_self _))
        hP.img).mpLshd ?_) (by omega) (by omega) fun j hj => ?_
    · have hc := hS.sub (r := R.aD) (s := R.code) (I := ⟨adp + 4 * (a.used + b - 1 - t), 4⟩)
        (Iv.sub_elem (by omega)) code_sub
      simp only [Iv.Disj, Disj] at hc
      exact { ry := ⟨by have := hrd.lo_ge; omega, by have := hrd.hi_le; omega, by have := hrd.off; omega⟩
              y_v := by
                have h := hI.arr (a.used - 1 - t) (by omega)
                simpa [fD, show ¬ (a.used + b - t ≤ a.used - 1 - t) by omega] using h
              y_lt := by omega
              rd := ⟨by have := hrd.lo_ge; omega, by have := hrd.hi_le; omega, by have := hrd.off; omega⟩
              dp_al := hP.ga.ds_al
              code_off := by omega }
    · simp only [fD]
      by_cases hjT : j = a.used + b - 1 - t
      · subst hjT; simp only [ite_true]; rw [if_pos (by omega)]; congr 1; omega
      · rw [if_neg hjT]
        by_cases hin : a.used + b - t ≤ j ∧ j < a.used + b
        · rw [if_pos hin, if_pos (by omega)]
        · rw [if_neg hin, if_neg (by omega)]
  refine Triple.seq (Triple.countup (Q := ASt (Un.lay 32 sp pa adp a) R.aD (m0Of m ra sp pa a.used b) adp a.alloc
        v.keepR outp 0x80001640#64 (msL s0 sp adp b) (fD a b a.used))
      (P := fun t => ASt (Un.lay 32 sp pa adp a) R.aD (m0Of m ra sp pa a.used b) adp a.alloc v.keepR outp
        0x80001624#64 (kL s0 sp adp a.used b t) (fD a b t))
      (fun t ht => hseg t (by omega) fun M hc hf => l_step s0 v outp sp adp a.used b t _ M hc hf hb ht) ?_ 0 hu) ?_
  · have h := hseg (a.used - 1) (by omega) fun M hc hf =>
      le_step s0 v outp sp adp a.used b (a.used - 1) _ M hc hf hb hP.b_lt (by omega)
    rwa [show a.used - 1 + 1 = a.used by omega] at h
  -- `memset(dp, 0, 4 b)` and the epilogue
  intro cf ⟨M, hI, hat⟩
  have hFm := hF12.trans hI.fr
  have hms : Memset.Pre M adp 0 (4 * b) :=
    memset_pre hS (r := R.aD) (c := R.code) (himg hFm (by decide)) (Iv.sub_self _)
      (by simp only [Iv.Sub, Un.lay]; omega)
      ⟨hrd.lo_ge, by have := hrd.hi_le; omega, by have := hrd.off; omega⟩
  refine Triple.seq (memset_jal (ret := 0x80001644#64) (Lr := [(2, BitVec.ofNat 64 (sp - 32)), (8, s0)])
      { v with sp := BitVec.ofNat 64 (sp - 32), s0 := s0 }
      (jal_step 0x80001640#64 0x565070ef#32 0x07d64#21
        [(2, BitVec.ofNat 64 (sp - 32)), (8, s0), (10, BitVec.ofNat 64 adp), (11, 0#64), (12, BitVec.ofNat 64 (4 * b))]
        (himg hFm (by decide)).mpLshd [msL] [Abi.keepR])
      (by decide) (by decide) (by simp [Memset.entryL]) (by simp [Abi.keep, Abi.keepR, sKeepL])
      (by decide) hms (by simp [Abi.keep]) (by simp [Abi.keep, Abi.keepR, sKeepL])) ?_ cf hat
  intro cf ⟨M2, hat2, hpost⟩
  have hJ0 : ArrFrm (Un.lay 32 sp pa adp a) R.aD (m0Of m ra sp pa a.used b) M adp a.alloc
      (ovl (lshdDigits a b) (fD a b a.used) 0) := hI.congr fun j _ => by rw [ovl_zero]
  have hJ := hJ0.fill (k := b) (Nat.zero_le _) (by omega) (fun t ht => by simpa using hpost.fill t (by omega))
    (fun x hx => hpost.frame x (by omega)) (fun j _ h2 => by simp [lshdDigits, h2])
  have hF := hF12.trans hJ.fr
  have hrv : bytesT8 M2 (sp - 8) = ra :=
    (hF2.trans hJ.fr).keep hS (Reads.w8 (r := R.stk) (by simp only [Iv.Sub, Un.lay]; omega))
      (bytesT8_sd_self _ _ _)
  refine Triple.rmap (fun cf h => ⟨res a b, _, h, ?_⟩)
    (r_step ra s0 v outp sp M2 (himg hF (by decide)).mpLshd hP.rs (by omega) hP.ra_al hrv) cf hat2
  exact { repr := hhdr.of_hdr (fun x h1 h2 => (Frm.on (r := R.aS) hS hJ.fr) x ⟨h1, h2⟩)
            (hJ.arr.congr fun j hj => by
              simp only [ovl, res, MpInt.ofDigits_digit, if_pos hj]
              split
              · rfl
              · simp only [fD, lshdDigits]; rename_i hjb
                by_cases h3 : j < a.used + b
                · simp [hjb, h3]
                · simp [hjb, h3]) rfl rfl rfl
          lshd := ⟨fun h => absurd h (by omega), fun _ _ => res_post hP.sa hroom⟩
          frame := hF.mono }

end Tom.Machine.Fn.MpLshd
