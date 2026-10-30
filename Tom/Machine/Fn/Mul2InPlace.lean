import Tom.Machine.Fn.Mul2Main
import Tom.Machine.Kit.UnTail

/-!
# `mp_mul_2(a, a)` on the machine: in place

The segments of `Tom.Machine.Fn.Mul2` (stated for any `a`, `b` pointers, so
they hold for `b = a`) chained into `Api.Mul2.StatementInPlace`, over `Un`'s
regions (`a` written). The loop invariant is `Fn/Mul2Main.lean`'s over the
one array: at index `i`, digits below `i` are `a + a`'s, digits from `i` on
are still `a`'s, so the loop reads `a[i]` from the overlay itself
(`ovl … i` at `i`) and `a->used` from the struct, where the prologue stored
`b->used := a->used`. `oldused = a->used`, so the `memset` branch is never
taken.
-/

namespace Tom.Machine.Fn.Mul2.InPlace

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api
open Tom.Machine.Api.Un (R isW ws Saved Tail Snap)

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp : Nat} {a : MpInt}
  {ra s0 s1 : BitVec 64}

local notation "ρ" => Un.lay 32 sp pa adp a

theorem img_of (hP : Api.Mul2.PreI m sp pa adp a ra) {M : Mem} {ws' : List R} (hF : Frm ρ ws' m M)
    (hm : Misses isW [R.code] ws' = true := by decide) : Img M :=
  hF.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img hm

theorem snap (hP : Api.Mul2.PreI m sp pa adp a ra) :
    Snap ρ m (m2Of m ra s0 s1 sp pa a.used) ra s0 s1 sp pa adp a.used a.alloc a.sign a.digit := by
  have := hP.sp_ge; have := hP.va.used_le; have := hP.va.alloc_lt
  have hF1 : Frm ρ [R.stk] m (writeLog m (frameLog ra s0 s1 sp)) :=
    Frm.store (by simp only [LogIn, frameLog, Iv.Sub, Un.lay, and_true]; omega)
  have hF2 : Frm ρ [R.aS] (writeLog m (frameLog ra s0 s1 sp)) (m2Of m ra s0 s1 sp pa a.used) :=
    Frm.sw (Iv.sub_pre (by decide))
  have hsv : Saved (writeLog m (frameLog ra s0 s1 sp)) ra s0 s1 sp :=
    { ra_v := bytesT8_log _ _ 2 _ _ rfl (by simp [frameLog, OutLRange])
      s0_v := bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog, OutLRange]; omega)
      s1_v := bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog, OutLRange]; omega) }
  have hb := hF1.keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_
  exact { fr := hF1.trans hF2
          sv := hsv.keep hP.lay (by decide) hP.sp_ge hF2
          hdr := hb.hdr.set_used _ (by omega)
          arr := hF2.keep hP.lay (ArrAt.reads (r := R.aD) (Iv.sub_self _)) hb.arr }

/-- The loop's join points over `a`'s digits. -/
abbrev St (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (ra s0 s1 : BitVec 64) :=
  ASt (Un.lay 32 sp pa adp a) R.aD (m2Of m ra s0 s1 sp pa a.used) adp a.alloc v.keepR1 outp

theorem tail_of (hP : Api.Mul2.PreI m sp pa adp a ra) {M : Mem} {f : Nat → Nat}
    (hI : ArrFrm ρ R.aD (m2Of m ra s0 s1 sp pa a.used) M adp a.alloc f) :
    Tail ρ m M ra s0 s1 sp pa adp a.used a.alloc a.sign f :=
  (snap (s0 := s0) (s1 := s1) hP).tail hP.lay (by decide) hP.sp_ge hI

theorem lfacts (hP : Api.Mul2.PreI m sp pa adp a ra) {M : Mem} {i : Nat}
    (hI : ArrFrm ρ R.aD (m2Of m ra s0 s1 sp pa a.used) M adp a.alloc (ovl (addDigits a a) a.digit i))
    (hi : i < a.used) : LFacts M pa adp adp a.used i (a.digit i) :=
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt
  have hra : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have hd := hP.ga.disj
  { rx := ⟨by have := hra.lo_ge; omega, by have := hra.hi_le; omega, by have := hra.off; omega⟩
    x_v := by have := hI.arr i (by omega); simpa [ovl] using this
    x_lt := by have := hs.digit_lt i; rwa [radix_eq] at this
    ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    ua_v := by simpa [Layout.offUsed] using (tail_of (s0 := s0) (s1 := s1) hP hI).hdr.used
    ua_lt := by omega
    rb := ⟨by have := hra.lo_ge; omega, by have := hra.hi_le; omega, by have := hra.off; omega⟩
    b_al := hP.ga.ds_al
    ab := by simp only [Layout.sizeofMpInt, Layout.sizeofDigit] at hd; omega
    code_b := hP.lay.sub (r := R.aD) (s := R.code) (Iv.sub_elem (by omega)) code_sub }

/-- One loop segment (back edge to `5cec`, or the exit at `5d1c`). -/
theorem l_seg (hP : Api.Mul2.PreI m sp pa adp a ra) (i : Nat) (hi : i < a.used) (pc' : BitVec 64)
    (hseg : ∀ M, CodeAt M mpMul2Base mpMul2Code → LFacts M pa adp adp a.used i (a.digit i) →
      Triple (At 0x80005cec#64 (lL ra sp pa pa adp a.used adp i (addCarryAt a a i)) M v.keepR1 outp)
      (At pc' (lL ra sp pa pa adp a.used adp (i + 1) (a.digit i / 134217728))
        (writeLog M [(adp + 4 * i, 4, BitVec.ofNat 64 ((2 * a.digit i + addCarryAt a a i) % 268435456))])
        v.keepR1 outp)) :
    Triple (St m v outp sp pa adp a ra s0 s1 0x80005cec#64
        (lL ra sp pa pa adp a.used adp i (addCarryAt a a i)) (ovl (addDigits a a) a.digit i))
      (St m v outp sp pa adp a ra s0 s1 pc'
        (lL ra sp pa pa adp a.used adp (i + 1) (addCarryAt a a (i + 1))) (ovl (addDigits a a) a.digit (i + 1))) := by
  have hs := hP.va.toShape
  have hua := hs.used_le; have hroom := hP.room
  have hc := addCarryAt_le_one hs hs i
  refine ASt.store (v := (2 * a.digit i + addCarryAt a a i) % 268435456) (fun M hI => ?_) (by omega)
    (by rw [addDigits_self_lt hs hi, radix_eq, Nat.two_mul]) (by omega)
  have h := hseg M (img_of (ws' := ws) hP (((snap (s0 := s0) (s1 := s1) hP).fr.trans hI.fr).mono)).mpMul2
    (lfacts hP hI hi)
  rwa [show a.digit i / 134217728 = addCarryAt a a (i + 1) by rw [addCarryAt_self_succ hs]] at h

theorem loop (hP : Api.Mul2.PreI m sp pa adp a ra) (h1 : 1 ≤ a.used) :
    ∀ i, i < a.used → Triple (St m v outp sp pa adp a ra s0 s1 0x80005cec#64
        (lL ra sp pa pa adp a.used adp i (addCarryAt a a i)) (ovl (addDigits a a) a.digit i))
      (St m v outp sp pa adp a ra s0 s1 0x80005d1c#64
        (lL ra sp pa pa adp a.used adp a.used (addCarryAt a a a.used)) (ovl (addDigits a a) a.digit a.used)) := by
  have hs := hP.va.toShape
  refine Triple.countup (fun i hi => l_seg hP i (by omega) _ fun M hc hf =>
    l_step ra v outp sp pa pa adp a.used adp a.used i _ _ M hc hf (addCarryAt_le_one hs hs i) hi) ?_
  have h := l_seg (s0 := s0) (s1 := s1) (v := v) (outp := outp) hP (a.used - 1) (by omega) _ fun M hc hf =>
    le_step ra v outp sp pa pa adp a.used adp a.used (a.used - 1) _ _ M hc hf (addCarryAt_le_one hs hs _)
      (by omega)
  rw [show a.used - 1 + 1 = a.used by omega] at h
  exact h

/-- At `pc` with `a->used = n` and digits `f` (from `5d34` on). -/
def TSt (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (ra s0 s1 : BitVec 64)
    (pc : BitVec 64) (L : GRegs) (n : Nat) (f : Nat → Nat) (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, Tail (Un.lay 32 sp pa adp a) m M ra s0 s1 sp pa adp n a.alloc a.sign f ∧ At pc L M v.keepR1 outp cf

theorem ufacts (hP : Api.Mul2.PreI m sp pa adp a ra) {M : Mem} {n al sg : Nat}
    (h : HdrAt M pa adp n al sg) (hn : n + 1 < 2 ^ 31) : UFacts M pa n :=
  { rb := by simpa [Layout.sizeofMpInt] using hP.ga.st
    u_v := by simpa [Layout.offUsed] using h.used
    u_lt := hn }

theorem sfacts (hP : Api.Mul2.PreI m sp pa adp a ra) : SFacts pa :=
  { rb := by simpa [Layout.sizeofMpInt] using hP.ga.st
    pb_al := hP.ga.st_al
    code_b := disj_or (hP.lay.sub (r := R.aS) (s := R.code) (Iv.sub_self _) code_sub) }

/-- From the entry to `5d34`: the prologue, the loop, the final carry. -/
theorem phase1 (hP : Api.Mul2.PreI m sp pa adp a ra) :
    Triple (At 0x80005ca0#64 (entry1 ra s0 s1 sp pa pa) m v.keepR1 outp)
      (TSt m v outp sp pa adp a ra s0 s1 0x80005d34#64 (tL ra sp pa pa adp (nOf a) a.used) (nOf a)
        (ovl (addDigits a a) a.digit (nOf a))) := by
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt; have hroom := hP.room; have := hP.sp_ge
  have hF1 : Frm ρ [R.stk] m (writeLog m (frameLog ra s0 s1 sp)) :=
    Frm.store (by simp only [LogIn, frameLog, Iv.Sub, Un.lay, and_true]; omega)
  have hb1 := hF1.keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_
  have hsa := hP.lay.disj (r := R.stk) (s := R.aS)
  have hsc := hP.lay.sub (r := R.stk) (s := R.code) (Iv.sub_self _) code_sub
  simp only [Iv.Disj, Disj, Un.lay] at hsa hsc
  have hpf : ProFacts m sp pa pa a.used a.alloc :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rb := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
      ua_v := by simpa [Layout.offUsed] using hP.ra_.used
      al_v := by simpa [Layout.offAlloc] using hP.ra_.alloc
      ua_lt := by omega, al_lt := hal, room := by omega
      s_a := by omega, s_b := by omega, code_s := by omega }
  have hbf : BFacts (writeLog m (frameLog ra s0 s1 sp)) pa pa a.used adp adp :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rb := by simpa [Layout.sizeofMpInt] using hP.ga.st
      pb_al := hP.ga.st_al
      ou_v := by simpa [Layout.offUsed] using hb1.used
      bdp_v := by simpa [Layout.offDp] using hb1.dpv
      adp_v := by simpa [Layout.offDp] using hb1.dpv
      ou_lt := by omega, ab := by omega, code_b := (sfacts hP).code_b }
  have hsn := snap (s0 := s0) (s1 := s1) hP
  refine Triple.seq (p_step ra s0 s1 v outp sp pa pa a.used a.alloc m hP.img.mpMul2 hpf) ?_
  have himg1 := img_of hP hF1
  by_cases h0 : a.used = 0
  · have hn : nOf a = 0 := by simp only [nOf, h0]; rfl
    rw [hn, ovl_zero, show pL ra sp pa pa a.used = pL ra sp pa pa 0 by rw [h0],
      show tL ra sp pa pa adp 0 a.used = tL ra sp pa pa adp 0 0 by rw [h0]]
    refine Triple.rmap (fun cf h => ⟨_, ?_, h⟩)
      (e0_step ra v outp sp pa pa 0 adp adp _ himg1.mpMul2 (h0 ▸ hbf))
    have hT := tail_of (s0 := s0) (s1 := s1) hP
      (ArrFrm.init (w := R.aD) (Iv.sub_self _) hsn.arr : ArrFrm ρ R.aD _ _ adp a.alloc a.digit)
    rw [h0] at hT
    exact hT
  have h1 : 1 ≤ a.used := by omega
  have hI0 : ArrFrm ρ R.aD (m2Of m ra s0 s1 sp pa a.used) (m2Of m ra s0 s1 sp pa a.used) adp a.alloc
      (ovl (addDigits a a) a.digit 0) := ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; exact hsn.arr)
  refine Triple.seq (Triple.rmap (fun cf h => ⟨_, hI0, h⟩)
      (e1_step ra v outp sp pa pa a.used a.used adp adp _ himg1.mpMul2 hbf h1 (by omega)))
    (Triple.seq (loop (s0 := s0) (s1 := s1) hP h1 0 (by omega)) ?_)
  have hpost : ∀ {M : Mem} {f : Nat → Nat}, ArrFrm ρ R.aD (m2Of m ra s0 s1 sp pa a.used) M adp a.alloc f →
      Img M := fun hI => img_of (ws' := ws) hP (((snap (s0 := s0) (s1 := s1) hP).fr.trans hI.fr).mono)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (addCarryAt_le_one hs hs a.used) with hc | hc
  · have hn : nOf a = a.used := by simp only [nOf, hc, Nat.add_zero]
    rw [hn, hc]
    exact Triple.rmap (fun cf ⟨M, hI, hat⟩ => ⟨M, tail_of hP hI, hat⟩)
      (ASt.seg fun M hI => n_step ra v outp sp pa pa adp a.used adp a.used M
        (hpost hI).mpMul2 (ufacts hP (tail_of hP hI).hdr (by omega)))
  · have hn : nOf a = a.used + 1 := by simp only [nOf, hc]
    rw [hn, hc]
    have hra : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
    have hcf : CFacts adp a.used :=
      { rb := ⟨by have := hra.lo_ge; omega, by have := hra.hi_le; omega, by have := hra.off; omega⟩
        b_al := hP.ga.ds_al
        code_b := disj_or (hP.lay.sub (r := R.aD) (s := R.code) (Iv.sub_elem (by omega)) code_sub) }
    refine Triple.seq (ASt.store (v := 1) (i := a.used) (fun M hI => c1_step ra v outp sp pa pa adp a.used adp
      a.used M (hpost hI).mpMul2 hcf) (by omega) (by rw [addDigits_self_used hs, hc]) (by decide)) ?_
    intro cf ⟨M, hI, hat⟩
    have hT := tail_of hP hI
    have hsw : Frm ρ [R.aS] M (writeLog M [(pa, 4, BitVec.ofNat 64 (a.used + 1))]) := Frm.sw (Iv.sub_pre (by decide))
    refine Triple.rmap (fun cf h => ⟨_, ?_, h⟩)
      (c2_step ra v outp sp pa pa adp a.used a.used M (hpost hI).mpMul2 (ufacts hP hT.hdr (by omega))
        (sfacts hP)) cf hat
    exact { fr := Frm.step hT.fr hsw
            sv := hT.sv.keep hP.lay (by decide) hP.sp_ge hsw
            hdr := hT.hdr.set_used _ (by omega)
            arr := hsw.keep hP.lay (ArrAt.reads (r := R.aD) (Iv.sub_self _)) hT.arr }

/-- From `5d34` to `5d50`: `oldused = a->used ≤ n`, so no `memset`. -/
theorem phase2 (hP : Api.Mul2.PreI m sp pa adp a ra) :
    Triple (TSt m v outp sp pa adp a ra s0 s1 0x80005d34#64 (tL ra sp pa pa adp (nOf a) a.used) (nOf a)
        (ovl (addDigits a a) a.digit (nOf a)))
      (TSt m v outp sp pa adp a ra s0 s1 0x80005d50#64 (rL sp pa pa) (nOf a) (addDigits a a)) := by
  intro cf ⟨M, hT, hat⟩
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt; have hroom := hP.room
  have hc := addCarryAt_le_one hs hs a.used
  have hfin : ∀ j, j < a.alloc → ovl (addDigits a a) a.digit (nOf a) j = addDigits a a j := fun j hj => by
    simp only [ovl]
    split
    · rfl
    · rw [hs.high_zero j (by simp only [nOf] at *; omega), addDigits_self_high hs j (by simp only [nOf] at *; omega)]
  exact Triple.rmap (fun cf h => ⟨_, hT.congr hfin, h⟩)
    (t0_step ra v outp sp pa pa adp (nOf a) a.used M (img_of hP hT.fr).mpMul2 (by simp only [nOf]; omega)
      (by simp only [nOf]; omega)) cf hat

/-- From `5d50` to the return: `a->sign := a->sign`, the epilogue. -/
theorem phase3 (hP : Api.Mul2.PreI m sp pa adp a ra) :
    Triple (TSt m v outp sp pa adp a ra s0 v.s.s1 0x80005d50#64 (rL sp pa pa) (nOf a) (addDigits a a))
      (Api.Mul2.RetI m v outp sp pa adp a ra s0) := by
  intro cf ⟨M, hT, hat⟩
  have hs := hP.va.toShape
  have hsg := hP.va.sign_ok
  simp only [Layout.mpZpos, Layout.mpNeg] at hsg
  have hsa := hP.lay.disj (r := R.stk) (s := R.aS)
  simp only [Iv.Disj, Disj, Un.lay] at hsa
  have := hP.sp_ge
  have hrf : RFacts M ra s0 v.s.s1 sp pa pa a.sign :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
      sa_v := by simpa [Layout.offSign] using hT.hdr.sign
      sa_lt := by omega
      ra_v := hT.sv.ra_v, s0_v := hT.sv.s0_v, s1_v := hT.sv.s1_v
      ra_al := hP.ra_al, s := sfacts hP, s_b := by omega }
  have hsw : Frm ρ [R.aS] M (writeLog M [(pa + 8, 4, BitVec.ofNat 64 a.sign)]) :=
    Frm.sw (by simp only [Iv.Sub, Un.lay]; omega)
  refine Triple.rmap (fun cf h => ⟨bRes a a, _, h.reshape (by simp) (by simp [Abi.keepR, Abi.keepR1, sKeepL]), ?_⟩)
    (r_step ra s0 v.s.s1 v outp sp pa pa a.sign M (img_of hP hT.fr).mpMul2 hrf) cf hat
  have hd := bRes_digit (b := a) hs hP.room
  exact { repr := HdrAt.mpAt (hT.hdr.set_sign _ (by omega))
            ((hsw.keep hP.lay (ArrAt.reads (r := R.aD) (Iv.sub_self _)) hT.arr).congr fun j _ => by rw [hd])
          mul2 := { alloc := rfl, len := by simp [bRes], digit := hd, used := rfl, sign := rfl }
          frame := Frm.step hT.fr hsw }

end

end InPlace

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic Tom.Machine Tom.Machine.Api

/-- **`mp_mul_2(a, a)` on the machine.** -/
theorem correct_inplace : Api.Mul2.StatementInPlace := by
  intro m v outp sp pa adp a ra s0 hP
  refine Triple.lmap (fun cf h => h.reshape (L' := entry1 ra s0 v.s.s1 sp pa pa) (K' := v.keepR1)
    (by simp [Api.Mul2.entryL, entry1, Abi.keepR, sKeepL])
    (by simp [Api.Mul2.entryL, Abi.keepR1, Abi.keepR, sKeepL])) ?_
  exact Triple.seq (InPlace.phase1 hP) (Triple.seq (InPlace.phase2 hP) (InPlace.phase3 hP))

end Tom.Machine.Fn.Mul2
