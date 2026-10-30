import Tom.Machine.Fn.Div2Main
import Tom.Machine.Kit.UnTail

/-!
# `mp_div_2(a, a)` on the machine: in place

The segments of `Tom.Machine.Fn.Div2` (stated for any `a`, `b` pointers)
chained into `Api.Div2.StatementInPlace`, over `Un`'s regions (`a`
written). The loop invariant is `Fn/Div2Main.lean`'s over the one array: at
index `x`, digits above `x` are the shifted ones, digits up to `x` are still
`a`'s, so the loop reads `a[x]` from the overlay itself (`ovlD … (x + 1)` at
`x`). `oldused = a->used`, so the `memset` branch is never taken.
-/

namespace Tom.Machine.Fn.Div2.InPlace

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api
open Tom.Machine.Api.Un (R isW ws Saved Tail Snap)

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt}
  {ra s0 s1 : BitVec 64}

local notation "ρ" => Un.lay 32 sp pa adp a

theorem img_of (hP : Api.Div2.PreI m sp pa adp a ra) {M : Mem} {ws' : List R} (hF : Frm ρ ws' m M)
    (hm : Misses isW [R.code] ws' = true := by decide) : Img M :=
  hF.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img hm

theorem snap (hP : Api.Div2.PreI m sp pa adp a ra) :
    Snap ρ m (m2Of m ra s0 s1 sp pa a.used) ra s0 s1 sp pa adp a.used a.alloc a.sign a.digit := by
  have := hP.sp_ge; have := hP.va.used_le; have := hP.va.alloc_lt
  have hF1 : Frm ρ [R.stk] m (writeLog m (frameLog ra s0 s1 sp)) :=
    Frm.store (by simp only [LogIn, frameLog, Iv.Sub, Un.lay, and_true]; omega)
  have hF2 : Frm ρ [R.aS] (writeLog m (frameLog ra s0 s1 sp)) (m2Of m ra s0 s1 sp pa a.used) :=
    Frm.sw (Iv.sub_pre (by decide))
  have hsv : Saved (writeLog m (frameLog ra s0 s1 sp)) ra s0 s1 sp :=
    { ra_v := bytesT8_log _ _ 2 _ _ rfl (by simp [frameLog, OutLRange])
      s0_v := bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog, OutLRange]; omega)
      s1_v := bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog, OutLRange]; omega) }
  have hb := hF1.keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_
  exact { fr := hF1.trans hF2
          sv := hsv.keep hP.lay (by decide) hP.sp_ge hF2
          hdr := hb.hdr.set_used _ (by omega)
          arr := hF2.keep hP.lay (ArrAt.reads (r := R.aD) (Iv.sub_self _)) hb.arr }

/-- The loop's join points over `a`'s digits. -/
abbrev St (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (ra s0 s1 : BitVec 64) :=
  ASt (Un.lay 32 sp pa adp a) R.aD (m2Of m ra s0 s1 sp pa a.used) adp a.alloc v.keepR1 outp

theorem tail_of (hP : Api.Div2.PreI m sp pa adp a ra) {M : Mem} {f : Nat → Nat}
    (hI : ArrFrm ρ R.aD (m2Of m ra s0 s1 sp pa a.used) M adp a.alloc f) :
    Tail ρ m M ra s0 s1 sp pa adp a.used a.alloc a.sign f :=
  (snap (s0 := s0) (s1 := s1) hP).tail hP.lay (by decide) hP.sp_ge hI

theorem himg (hP : Api.Div2.PreI m sp pa adp a ra) {M : Mem} {f : Nat → Nat}
    (hI : ArrFrm ρ R.aD (m2Of m ra s0 s1 sp pa a.used) M adp a.alloc f) : Img M :=
  img_of (ws' := ws) hP (((snap (s0 := s0) (s1 := s1) hP).fr.trans hI.fr).mono)

theorem dfacts (hP : Api.Div2.PreI m sp pa adp a ra) : DFacts adp adp a.used :=
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt
  have hra : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  { ra_d := ⟨by have := hra.lo_ge; omega, by have := hra.hi_le; omega, by have := hra.off; omega⟩
    rb_d := ⟨by have := hra.lo_ge; omega, by have := hra.hi_le; omega, by have := hra.off; omega⟩
    ua_lt := by omega }

theorem lfacts (hP : Api.Div2.PreI m sp pa adp a ra) {M : Mem} {x : Nat}
    (hI : ArrFrm ρ R.aD (m2Of m ra s0 s1 sp pa a.used) M adp a.alloc
      (ovlD (div2Digits a) a.digit (x + 1) a.used))
    (hx : x < a.used) : LFacts adp adp a.used x (a.digit x) M :=
  have hs := hP.va.toShape
  have hua := hs.used_le
  { rd := dfacts hP, x_lt := hx
    d_v := by
      have := hI.arr x (by omega)
      simp only [ovlD] at this
      rwa [if_neg (by omega)] at this
    d_lt := by have := hs.digit_lt x; rwa [radix_eq] at this
    b_al := hP.ga.ds_al
    code_b := disj_or (hP.lay.sub (r := R.aD) (s := R.code) (Iv.sub_elem (by omega)) code_sub) }

theorem ufacts (hP : Api.Div2.PreI m sp pa adp a ra) {M : Mem} {n al sg : Nat}
    (h : HdrAt M pa adp n al sg) (hn : n < 2 ^ 31) (hb0 : 1 ≤ a.alloc) : UFacts M pa adp n :=
  { rb := by simpa [Layout.sizeofMpInt] using hP.ga.st
    u_v := by simpa [Layout.offUsed] using h.used
    u_lt := hn
    bb := by
      have := hP.ga.disj
      simp only [Layout.sizeofMpInt, Layout.sizeofDigit] at this
      omega }

/-- The loop head at `x`, with `x < a->used`. -/
def LP (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt)
    (ra s0 s1 : BitVec 64) (x : Nat) (cf : Vsa.Machine.Config) : Prop :=
  x < a.used ∧ St m v outp sp pa adp a ra s0 s1 0x8000518c#64
    (lL ra sp pa pa adp a.used adp x (rOf a x)) (ovlD (div2Digits a) a.digit (x + 1) a.used) cf

/-- The loop from `x` to `51b4`. -/
theorem loop (hP : Api.Div2.PreI m sp pa adp a ra) :
    ∀ x, Triple (LP m v outp sp pa adp a ra s0 s1 x)
      (St m v outp sp pa adp a ra s0 s1 0x800051b4#64 (Fn.Div2.tL ra sp pa pa adp a.used a.used)
        (ovlD (div2Digits a) a.digit 0 a.used)) := by
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt
  refine Triple.countdown (fun k => ?_) ?_
  · refine Triple.of_pure fun hk => Triple.rmap (fun cf h => Or.inr ⟨by omega, h⟩) ?_
    have : rOf a (k + 1) < 2 := Nat.mod_lt _ (by decide)
    refine ASt.storeD (v := a.digit (k + 1) / 2 + 134217728 * rOf a (k + 1)) (fun M hI => ?_) (by omega) hk
      (div2Digits_eq a (k + 1)) (by have := hs.digit_lt (k + 1); rw [radix_eq] at this; omega)
    exact l_step ra v outp sp pa pa adp a.used adp a.used k _ _ M (himg (s0 := s0) (s1 := s1) hP hI).mpDiv2
      (lfacts hP hI hk) (by simp only [rOf]; omega)
  · refine Triple.of_pure fun hk => ?_
    have : rOf a 0 < 2 := Nat.mod_lt _ (by decide)
    refine ASt.storeD (v := a.digit 0 / 2 + 134217728 * rOf a 0) (fun M hI => ?_) (by omega) hk
      (div2Digits_eq a 0) (by have := hs.digit_lt 0; rw [radix_eq] at this; omega)
    exact le_step ra v outp sp pa pa adp a.used adp a.used a.used _ _ M (himg (s0 := s0) (s1 := s1) hP hI).mpDiv2
      (lfacts hP hI hk) (by simp only [rOf]; omega) (ufacts hP (tail_of hP hI).hdr (by omega) (by omega))

/-- At `pc` with `a->used = n` and digits `f` (from `51b4` on). -/
def TSt (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (ra s0 s1 : BitVec 64)
    (pc : BitVec 64) (L : GRegs) (n sg : Nat) (f : Nat → Nat) (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, Tail (Un.lay 32 sp pa adp a) m M ra s0 s1 sp pa adp n a.alloc sg f ∧ At pc L M v.keepR1 outp cf

/-- From the entry to `51b4`: the prologue and the loop. -/
theorem phase1 (hP : Api.Div2.PreI m sp pa adp a ra) :
    Triple (At 0x80005134#64 (entry1 ra s0 s1 sp pa pa) m v.keepR1 outp)
      (TSt m v outp sp pa adp a ra s0 s1 0x800051b4#64 (tL ra sp pa pa adp a.used a.used) a.used a.sign
        (ovl (div2Digits a) a.digit a.used)) := by
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt; have := hP.sp_ge
  have hF1 : Frm ρ [R.stk] m (writeLog m (frameLog ra s0 s1 sp)) :=
    Frm.store (by simp only [LogIn, frameLog, Iv.Sub, Un.lay, and_true]; omega)
  have hb1 := hF1.keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_
  have hsa := hP.lay.disj (r := R.stk) (s := R.aS)
  have hsc := hP.lay.sub (r := R.stk) (s := R.code) (Iv.sub_self _) code_sub
  have hac := hP.lay.sub (r := R.aS) (s := R.code) (Iv.sub_self _) code_sub
  simp only [Iv.Disj, Disj, Un.lay] at hsa hsc hac
  have hpf : ProFacts m sp pa pa a.used a.alloc :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rb := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
      ua_v := by simpa [Layout.offUsed] using hP.ra_.used
      al_v := by simpa [Layout.offAlloc] using hP.ra_.alloc
      ua_lt := by omega, al_lt := hal, room := hua
      s_a := by omega, s_b := by omega, code_s := by omega }
  have hbf : BFacts (writeLog m (frameLog ra s0 s1 sp)) pa pa a.used adp adp :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rb := by simpa [Layout.sizeofMpInt] using hP.ga.st
      pb_al := hP.ga.st_al
      ou_v := by simpa [Layout.offUsed] using hb1.used
      bdp_v := by simpa [Layout.offDp] using hb1.dpv
      adp_v := by simpa [Layout.offDp] using hb1.dpv
      ou_lt := by omega, ab := by omega, code_b := hac }
  have hsn := snap (s0 := s0) (s1 := s1) hP
  have himg1 := img_of hP hF1
  refine Triple.seq (p_step ra s0 s1 v outp sp pa pa a.used a.alloc m hP.img.mpDiv2 hpf) ?_
  by_cases h0 : a.used = 0
  · rw [show pL ra sp pa pa a.used = pL ra sp pa pa 0 by rw [h0],
      show tL ra sp pa pa adp a.used a.used = tL ra sp pa pa adp 0 0 by rw [h0], h0, ovl_zero]
    refine Triple.rmap (fun cf h => ⟨_, ?_, h⟩)
      (e0_step ra v outp sp pa pa 0 adp adp _ himg1.mpDiv2 (h0 ▸ hbf))
    have hT := tail_of (s0 := s0) (s1 := s1) hP
      (ArrFrm.init (w := R.aD) (Iv.sub_self _) hsn.arr : ArrFrm ρ R.aD _ _ adp a.alloc a.digit)
    rw [h0] at hT
    exact hT
  have h1 : 1 ≤ a.used := by omega
  have hI0 : ArrFrm ρ R.aD (m2Of m ra s0 s1 sp pa a.used) (m2Of m ra s0 s1 sp pa a.used) adp a.alloc
      (ovlD (div2Digits a) a.digit (a.used - 1 + 1) a.used) :=
    ArrFrm.init (Iv.sub_self _) (by rw [Nat.sub_add_cancel h1, ovlD_top]; exact hsn.arr)
  have hr0 : rOf a (a.used - 1) = 0 := by
    simp only [rOf, Nat.sub_add_cancel h1, hs.high_zero a.used (Nat.le_refl _)]
  have hM2 : Frm ρ [R.aS] (writeLog m (frameLog ra s0 s1 sp)) (m2Of m ra s0 s1 sp pa a.used) :=
    Frm.sw (Iv.sub_pre (by decide))
  have hadp : bytesT8 (m2Of m ra s0 s1 sp pa a.used) (pa + 16) = BitVec.ofNat 64 adp :=
    (hsn.hdr.dpv : bytesT8 _ (pa + Layout.offDp) = _)
  refine Triple.seq (e1_step ra v outp sp pa pa a.used a.used adp adp _ himg1.mpDiv2 hbf h1 (by omega)) ?_
  refine Triple.seq (Triple.rmap (fun cf h => by
      rw [writeLog_nil, ← hr0] at h
      exact (⟨by omega, _, hI0, h⟩ : LP m v outp sp pa adp a ra s0 s1 (a.used - 1) cf))
      (e2_step ra v outp sp pa pa a.used a.used adp adp (m2Of m ra s0 s1 sp pa a.used)
        (img_of hP (hF1.trans hM2)).mpDiv2 hpf.ra_ hadp (dfacts hP) h1)) ?_
  refine Triple.rmap (fun cf ⟨M, hI, hat⟩ => ⟨M, ?_, hat⟩) (loop (s0 := s0) (s1 := s1) hP (a.used - 1))
  rw [← ovlD_zero]
  exact tail_of hP hI

/-- From `51b4` to `51d0`: `oldused = a->used`, so no `memset`. -/
theorem phase2 (hP : Api.Div2.PreI m sp pa adp a ra) :
    Triple (TSt m v outp sp pa adp a ra s0 s1 0x800051b4#64 (tL ra sp pa pa adp a.used a.used) a.used
        a.sign (ovl (div2Digits a) a.digit a.used))
      (TSt m v outp sp pa adp a ra s0 s1 0x800051d0#64 (rL sp pa pa) a.used a.sign (div2Digits a)) := by
  intro cf ⟨M, hT, hat⟩
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt
  have hfin : ∀ j, j < a.alloc → ovl (div2Digits a) a.digit a.used j = div2Digits a j := fun j hj => by
    simp only [ovl]
    split
    · rfl
    · rw [hs.high_zero j (by omega), div2Digits_high hs j (by omega)]
  exact Triple.rmap (fun cf h => ⟨_, hT.congr hfin, h⟩)
    (t0_step ra v outp sp pa pa adp a.used a.used M (img_of hP hT.fr).mpDiv2 (by omega) (Nat.le_refl _)) cf hat

/-- From `51d0` to the return: `a->sign := a->sign`, `mp_clamp(a)`, the epilogue. -/
theorem phase3 (hP : Api.Div2.PreI m sp pa adp a ra) :
    Triple (TSt m v outp sp pa adp a ra s0 v.s.s1 0x800051d0#64 (rL sp pa pa) a.used a.sign (div2Digits a))
      (Api.Div2.RetI m v outp sp pa adp a ra s0) := by
  intro cf ⟨M, hT, hat⟩
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt
  have hsg := hP.va.sign_ok
  simp only [Layout.mpZpos, Layout.mpNeg] at hsg
  have := hP.sp_ge
  have hac := hP.lay.sub (r := R.aS) (s := R.code) (Iv.sub_self _) code_sub
  have hal' := hP.lay.sub (r := R.aS) (s := R.code) (Iv.sub_self _) clamp_sub
  simp only [Iv.Disj, Disj, Un.lay] at hac hal'
  have hsf : SFacts M pa pa a.sign :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rb := by simpa [Layout.sizeofMpInt] using hP.ga.st
      pb_al := hP.ga.st_al, code_b := hac
      sa_v := by simpa [Layout.offSign] using hT.hdr.sign
      sa_lt := by omega }
  have hsw : Frm ρ [R.aS] M (writeLog M [(pa + 8, 4, BitVec.ofNat 64 a.sign)]) :=
    Frm.sw (by simp only [Iv.Sub, Un.lay]; omega)
  have hd := div2Mid_digit (b := a) hs hua
  have hcp : Clamp.Pre (writeLog M [(pa + 8, 4, BitVec.ofNat 64 a.sign)]) pa adp (div2Mid a a) :=
    { repr := HdrAt.mpAt (hT.hdr.set_sign _ (by omega))
        ((hsw.keep hP.lay (ArrAt.reads (r := R.aD) (Iv.sub_self _)) hT.arr).congr fun j _ => by rw [hd])
      shape := div2Mid_shape hs hua hal
      geom := hP.ga
      code := (img_of hP (Frm.step hT.fr hsw)).mpClamp
      code_off := hal' }
  refine Triple.seq (s_step v outp sp pa pa a.sign M (img_of hP hT.fr).mpDiv2 hsf)
    (Triple.seq (clamp_call v outp sp pa pa adp _ _ (img_of hP (Frm.step hT.fr hsw)).mpDiv2 hcp) ?_) cf hat
  intro cf ⟨b', M', hat', hpost⟩
  have hcl : Frm ρ [R.aS] (writeLog M [(pa + 8, 4, BitVec.ofNat 64 a.sign)]) M' :=
    Frm.call (w := R.aS) hpost.frame (Iv.sub_pre (by decide))
  have hF := Frm.step (Frm.step hT.fr hsw) hcl
  have hsv := (hT.sv.keep hP.lay (by decide) hP.sp_ge hsw).keep hP.lay (by decide) hP.sp_ge hcl
  have hrf : RFacts M' ra s0 v.s.s1 sp :=
    { rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
      ra_v := hsv.ra_v, s0_v := hsv.s0_v, s1_v := hsv.s1_v, ra_al := hP.ra_al }
  refine Triple.rmap (fun cf h => ⟨b', _, h.reshape (by simp) (by simp [Abi.keepR, Abi.keepR1, sKeepL]), ?_⟩)
    (r_step ra s0 v.s.s1 v outp sp pa pa M' (img_of hP hF).mpDiv2 hrf) cf hat'
  have hc := hpost.clamp
  exact { repr := hpost.repr
          div2 := { alloc := hc.alloc
                    len := by rw [hc.digits]; simp [div2Mid]
                    digit := by rw [hc.digit, hd]
                    used := by rw [hc.used, hd]; rfl
                    sign := by rw [hc.sign]; rfl }
          frame := hF }

end

end InPlace

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic Tom.Machine Tom.Machine.Api

/-- **`mp_div_2(a, a)` on the machine.** -/
theorem correct_inplace : Api.Div2.StatementInPlace := by
  intro m v outp sp pa adp a ra s0 hP
  refine Triple.lmap (fun cf h => h.reshape (L' := entry1 ra s0 v.s.s1 sp pa pa) (K' := v.keepR1)
    (by simp [Api.Div2.entryL, entry1, Abi.keepR, sKeepL])
    (by simp [Api.Div2.entryL, Abi.keepR1, Abi.keepR, sKeepL])) ?_
  exact Triple.seq (InPlace.phase1 hP) (Triple.seq (InPlace.phase2 hP) (InPlace.phase3 hP))

end Tom.Machine.Fn.Div2
