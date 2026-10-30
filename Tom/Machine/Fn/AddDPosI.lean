import Tom.Machine.Api.AddD
import Tom.Machine.Kit.UnDTail
import Tom.Machine.Fn.AddDPos

/-!
# `mp_add_d(a, b, a)` on the machine for `a ≥ 0`

`Fn/AddDPos.lean` with `c = a` (same struct, same digits), over `Un`'s regions:
the loop reads `a[i]` from the overlay before storing `c[i]` there, `a->used`
from the struct (not stored until after the loop), and `oldused = a->used`,
so the zeroing never calls `memset`. The segments are `Fn/AddD.lean`'s.
-/

namespace Tom.Machine.Fn.AddD.InPlace

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api
open Tom.Machine.Api.Un (R isW ws Saved2 Tail2 Snap2)

/-- What stays as at the entry. -/
structure RO (M : Mem) : Prop where
  img : Img M

/-- At `pc0` with `c->used = n`, sign `s`, digits `f`. -/
def TSt (F : Nat) (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt)
    (ra s0 : BitVec 64) (pc0 : BitVec 64) (L : GRegs) (n s : Nat) (f : Nat → Nat)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, Tail2 (Un.lay F sp pa adp a) m M ra s0 sp pa adp n a.alloc s f ∧ At pc0 L M v.keepR outp cf

/-- What a branch leaves: `c'` at `c`, its `DRes`, memory changed only in `ws`. -/
structure DOut (ρ : R → Iv) (m M : Mem) (pa adp : Nat) (c c' : MpInt) (dig : Nat → Nat) (n s : Nat) : Prop where
  repr : MpAt M pa adp c'
  res : DRes c c' dig n s
  frame : Frm ρ ws m M

/-- The return of a branch. -/
def RetD (F : Nat) (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt)
    (ra s0 : BitVec 64) (dig : Nat → Nat) (n s : Nat) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    DOut (Un.lay F sp pa adp a) m M pa adp a c' dig n s

section
variable {F : Nat} {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pa adp : Nat} {a : MpInt} {b : Nat}
   {ra s0 : BitVec 64}

local notation "ρ" => Un.lay F sp pa adp a

theorem RO.of (hP : Api.AddD.PreI F m sp pa adp a b ra) {M : Mem} (hF : Frm ρ ws m M) : RO M :=
  { img := hF.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img }

theorem f1 (hP : Api.AddD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) :
    Frm ρ [R.stk] m (m1Of m ra s0 sp) := by
  have := hP.sp_ge
  exact Frm.store (by simp only [LogIn, frameLog, Iv.Sub, Un.lay, and_true]; omega)

theorem sv1 (hP : Api.AddD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) :
    Saved2 (m1Of m ra s0 sp) ra s0 sp :=
  have := hP.sp_ge
  { ra_v := bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog, OutLRange])
    s0_v := bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog, OutLRange]; omega) }

theorem rc1 (hP : Api.AddD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) :
    MpAt (m1Of m ra s0 sp) pa adp a :=
  (f1 hP hF).keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_

theorem ro1 (hP : Api.AddD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) :
    RO (m1Of m ra s0 sp) := RO.of hP (f1 hP hF).mono

/-- The snapshot of the loop: the memory after the prologue. -/
theorem snap1 (hP : Api.AddD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) :
    Snap2 ρ m (m1Of m ra s0 sp) ra s0 sp pa adp a.used a.alloc a.sign a.digit :=
  { fr := (f1 hP hF).mono, sv := sv1 hP hF, hdr := (rc1 hP hF).hdr, arr := (rc1 hP hF).arr }

theorem pfacts (hP : Api.AddD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) :
    PFacts m sp pa pa a.used a.alloc :=
  have := hP.sp_ge; have := hP.va.used_le; have := hP.va.alloc_lt; have := hP.va.toShape.alloc_lt
  have := hP.room
  have hrs := hP.rs
  { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    rc := by simpa [Layout.sizeofMpInt] using hP.ga.st
    rs := ⟨by have := hrs.lo_ge; omega, by have := hrs.hi_le; omega, by have := hrs.off; omega⟩
    sp_al := hP.sp_al, sp_ge := by omega
    ua_v := by simpa [Layout.offUsed] using hP.ra_.used
    al_v := by simpa [Layout.offAlloc] using hP.ra_.alloc
    ua_lt := by omega, al_lt := by omega, room := by omega
    code_s := disj_or (hP.lay.sub (r := R.stk) (s := R.code) (I := ⟨sp - 64, 64⟩)
      (by simp only [Iv.Sub, Un.lay]; omega) code_sub) |>.elim (fun h => Or.inl (by omega)) Or.inr }

theorem hfacts (hP : Api.AddD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) :
    HFacts (m1Of m ra s0 sp) pa pa a.sign a.used a.used adp adp :=
  have hro := ro1 (s0 := s0) hP hF
  have hc := rc1 (s0 := s0) hP hF
  have := hP.va.used_le; have := hP.va.alloc_lt; have := hP.va.toShape.alloc_lt; have := hP.va.toShape.used_le
  have hsg := hP.va.sign_ok
  { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    rc := by simpa [Layout.sizeofMpInt] using hP.ga.st
    sa_v := by simpa [Layout.offSign] using hc.sign
    ua_v := by simpa [Layout.offUsed] using hc.used
    ou_v := by simpa [Layout.offUsed] using hc.used
    adp_v := by simpa [Layout.offDp] using hc.dpv
    cdp_v := by simpa [Layout.offDp] using hc.dpv
    sa_lt := by simp only [Layout.mpZpos, Layout.mpNeg] at hsg; omega
    ua_lt := by omega, ou_lt := by omega }

theorem code_c (hP : Api.AddD.PreI F m sp pa adp a b ra) :
    pa + 24 ≤ mpAddDBase ∨ mpAddDBase + 424 ≤ pa :=
  disj_or (hP.lay.sub (r := R.aS) (s := R.code) (Iv.sub_self _) code_sub)

/-! ## The tail -/

theorem fin_eq {n : Nat} {dig : Nat → Nat} (hc : a.Shape) (hhi : ∀ i, n ≤ i → dig i = 0) {k : Nat}
    (hk : n ≤ k) (hk' : a.used ≤ k) : ∀ j, j < a.alloc → ovl dig a.digit k j = dig j := fun j _ => by
  simp only [ovl]
  split
  · rfl
  · rw [hc.high_zero j (by omega), hhi j (by omega)]

/-- From `4ec4`: `c->sign := MP_ZPOS`, zero the excess digits, `mp_clamp(c)`, return. -/
theorem tail (hP : Api.AddD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) {n : Nat} {dig : Nat → Nat}
    (hlt : ∀ i, dig i < radix) (hhi : ∀ i, n ≤ i → dig i = 0) (hn : n ≤ a.alloc) :
    Triple (TSt F m v outp sp pa adp a ra s0 0x80004ec4#64 (tL ra sp pa a.used adp n) n a.sign
        (ovl dig a.digit n))
      (RetD F m v outp sp pa adp a ra s0 dig n 0) := by
  have := hP.sp_ge; have hal := hP.va.toShape.alloc_lt; have hbu := hP.va.toShape.used_le
  have hrc : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have hrs : Ram pa 24 := by simpa [Layout.sizeofMpInt] using hP.ga.st
  -- after the sign store and the zeroing, at `4edc`
  have hfin : Triple (TSt F m v outp sp pa adp a ra s0 0x80004edc#64 (mL sp pa) n 0 dig)
      (RetD F m v outp sp pa adp a ra s0 dig n 0) := by
    intro cf ⟨M, hT, hat⟩
    have hro := RO.of hP hT.fr
    have hd := dMid_digit (c := a) (s := 0) hhi hn
    have hcp : Clamp.Pre M pa adp (dMid a dig n 0) :=
      { repr := HdrAt.mpAt hT.hdr (hT.arr.congr fun j _ => by rw [hd])
        shape := dMid_shape hlt hhi hn hal
        geom := hP.ga, code := hro.img.mpClamp
        code_off := disj_or (hP.lay.sub (r := R.aS) (s := R.code) (Iv.sub_self _) clamp_sub) }
    refine Triple.seq (d_step v outp sp pa M hro.img.mpAddD)
      (Triple.seq (clamp_call1 v outp sp pa adp _ M hro.img.mpAddD hcp) ?_) cf hat
    intro cf ⟨c', M', hat', hpost⟩
    have hcl : Frm ρ [R.aS] M M' := Frm.call (w := R.aS) hpost.frame (Iv.sub_pre (by decide))
    have hF' := Frm.step hT.fr hcl
    have hsv := hT.sv.keep hP.lay (by omega) hP.sp_ge hcl
    have hrs := hP.rs
    have hrf : RFacts M' ra s0 sp :=
      { rs := ⟨by have := hrs.lo_ge; omega, by have := hrs.hi_le; omega, by have := hrs.off; omega⟩
        sp_al := hP.sp_al, sp_ge := by omega
        ra_v := hsv.ra_v, s0_v := hsv.s0_v, ra_al := hP.ra_al }
    exact Triple.rmap (fun cf h => ⟨c', _, h, hpost.repr, DRes.of_clamp hhi hn hpost.clamp, hF'⟩)
      (r_step ra s0 v outp sp M' (RO.of hP hF').img.mpAddD hrf) cf hat'
  intro cf ⟨M, hT, hat⟩
  have hro := RO.of hP hT.fr
  have hsw : Frm ρ [R.aS] M (writeLog M [(pa + 8, 4, 0#64)]) := Frm.sw (by simp only [Iv.Sub, Un.lay]; omega)
  have hT' : Tail2 ρ m (writeLog M [(pa + 8, 4, 0#64)]) ra s0 sp pa adp n a.alloc 0 (ovl dig a.digit n) :=
    { fr := Frm.step hT.fr hsw
      sv := hT.sv.keep hP.lay (by omega) hP.sp_ge hsw
      hdr := hT.hdr.set_sign 0 (by decide)
      arr := hsw.keep hP.lay (ArrAt.reads (r := R.aD) (Iv.sub_self _)) hT.arr }
  by_cases hou : a.used ≤ n
  · exact Triple.seq (Triple.rmap (fun cf h => ⟨_, hT'.congr (fin_eq hP.va.toShape hhi (Nat.le_refl _) hou), h⟩)
      (t0_step ra v outp sp pa a.used adp n M hro.img.mpAddD hrs hP.ga.st_al (code_c hP) (by omega) hou)) hfin cf hat
  · have hro' := RO.of hP hT'.fr
    refine Triple.seq (t1_step ra v outp sp pa a.used adp n M hro.img.mpAddD hrs hP.ga.st_al (code_c hP)
        (by omega) (by omega) (by have := hrc.hi_le; omega))
      (Triple.seq (Triple.rmap (fun cf ⟨M', hat', hpost⟩ => ⟨M', (hT'.fill hP.lay (by omega) hP.sp_ge
          (by omega) hbu hpost fun j h1 _ => hhi j h1).congr (fin_eq hP.va.toShape hhi (by omega) (Nat.le_refl _)), hat'⟩)
        (memset_call ra v outp sp pa adp n a.used _ hro'.img.mpAddD
          (Un.memset_pre hP.lay hP.ga hro'.img (by omega) hbu))) hfin) cf hat

/-! ## `a ≥ 0` -/

/-- The loop's join points: `c`'s digits hold `f`, nothing else changed since `m1Of`. -/
abbrev St (F : Nat) (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt)
    (ra s0 : BitVec 64) :=
  ASt (Un.lay F sp pa adp a) R.aD (m1Of m ra s0 sp) adp a.alloc v.keepR outp

theorem ro2 (hP : Api.AddD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) {M : Mem} {f : Nat → Nat}
    (hI : ArrFrm ρ R.aD (m1Of m ra s0 sp) M adp a.alloc f) : RO M :=
  RO.of hP (((snap1 (s0 := s0) hP hF).fr.trans hI.fr).mono)

theorem lfacts (hP : Api.AddD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) {M : Mem} {i : Nat}
    (hI : ArrFrm ρ R.aD (m1Of m ra s0 sp) M adp a.alloc (ovl (addDDigits a b) a.digit i))
    (hi : i < a.used) : LFacts M pa adp adp a.used i (a.digit i) :=
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt; have hroom := hP.room
  have hra : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have hT := (snap1 (s0 := s0) hP hF).tail hP.lay (by omega) hP.sp_ge hI
  { rx := ⟨by have := hra.lo_ge; omega, by have := hra.hi_le; omega, by have := hra.off; omega⟩
    x_v := by have := hI.arr i (by omega); simpa [ovl] using this
    x_lt := by have := hs.digit_lt i; rwa [radix_eq] at this
    ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    ua_v := by simpa [Layout.offUsed] using hT.hdr.used
    ua_lt := by omega
    rd := ⟨by have := hra.lo_ge; omega, by have := hra.hi_le; omega, by have := hra.off; omega⟩
    d_al := hP.ga.ds_al
    ac := disj_or (hP.lay.sub (r := R.aS) (s := R.aD) (I := ⟨pa, 4⟩) (J := ⟨adp + 4 * i, 4⟩)
      (Iv.sub_pre (by decide)) (Iv.sub_elem (by omega)))
    code_d := disj_or (hP.lay.sub (r := R.aD) (s := R.code) (Iv.sub_elem (by omega)) code_sub) }

/-- One loop segment (back edge to `4e80`, or the exit at `4eb0`). -/
theorem l_seg (hP : Api.AddD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) (i : Nat) (hi : i < a.used)
    (pa' : BitVec 64) (Lf : Nat → GRegs)
    (hseg : ∀ M, CodeAt M mpAddDBase mpAddDCode → LFacts M pa adp adp a.used i (a.digit i) →
      Triple (At 0x80004e80#64 (lL ra sp pa pa a.used adp adp i (addDCarry a b i)) M v.keepR outp)
      (At pa' (Lf ((a.digit i + addDCarry a b i) / 268435456))
        (writeLog M [(adp + 4 * i, 4, BitVec.ofNat 64 ((a.digit i + addDCarry a b i) % 268435456))])
        v.keepR outp)) :
    Triple (St F m v outp sp pa adp a ra s0 0x80004e80#64
        (lL ra sp pa pa a.used adp adp i (addDCarry a b i)) (ovl (addDDigits a b) a.digit i))
      (St F m v outp sp pa adp a ra s0 pa' (Lf (addDCarry a b (i + 1)))
        (ovl (addDDigits a b) a.digit (i + 1))) := by
  have hs := hP.va.toShape
  have hua := hs.used_le; have hroom := hP.room
  refine ASt.store (v := (a.digit i + addDCarry a b i) % 268435456) (fun M hI => ?_) (by omega)
    (by simp only [addDDigits, if_pos hi, radix_eq]) (by omega)
  have hro := ro2 (s0 := s0) hP hF hI
  have h := hseg M hro.img.mpAddD (lfacts hP hF hI hi)
  rwa [show (a.digit i + addDCarry a b i) / 268435456 = addDCarry a b (i + 1) by
    rw [addDCarry_succ, radix_eq]] at h

theorem loop (hP : Api.AddD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) (h1 : 1 ≤ a.used) :
    ∀ i, i < a.used → Triple (St F m v outp sp pa adp a ra s0 0x80004e80#64
        (lL ra sp pa pa a.used adp adp i (addDCarry a b i)) (ovl (addDDigits a b) a.digit i))
      (St F m v outp sp pa adp a ra s0 0x80004eb0#64
        (jL ra sp pa pa a.used adp a.used (addDCarry a b a.used)) (ovl (addDDigits a b) a.digit a.used)) := by
  have hs := hP.va.toShape
  have hc : ∀ i, addDCarry a b i < 268435456 := fun i => by
    have := addDCarry_lt hs hP.hb i; rwa [radix_eq] at this
  refine Triple.countup (fun i hi => l_seg hP hF i (by omega) _ (fun u => lL ra sp pa pa a.used adp adp (i + 1) u)
    fun M hcd hf => l_step ra v outp sp pa pa a.used adp adp a.used i _ _ M hcd hf (hc i) hi) ?_
  have h := l_seg (s0 := s0) (v := v) (outp := outp) hP hF (a.used - 1) (by omega) _
    (fun u => jL ra sp pa pa a.used adp a.used u)
    fun M hcd hf => le_step ra v outp sp pa pa a.used adp adp a.used (a.used - 1) _ _ M hcd hf (hc _) (by omega)
  rw [show a.used - 1 + 1 = a.used by omega] at h
  exact h

theorem cfacts (hP : Api.AddD.PreI F m sp pa adp a b ra) {M : Mem}
    (hu : bytesT4 M pa = BitVec.ofNat 32 a.used) : CFacts M pa pa adp a.used :=
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt; have hroom := hP.room
  have hra : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    rc := by simpa [Layout.sizeofMpInt] using hP.ga.st
    pc_al := hP.ga.st_al
    ua_v := hu
    ua_lt := by omega
    rd := ⟨by have := hra.lo_ge; omega, by have := hra.hi_le; omega, by have := hra.off; omega⟩
    d_al := hP.ga.ds_al
    ac := disj_or (hP.lay.sub (r := R.aS) (s := R.aD) (I := ⟨pa, 4⟩) (J := ⟨adp + 4 * a.used, 4⟩)
      (Iv.sub_pre (by decide)) (Iv.sub_elem (by omega)))
    code_c := code_c hP
    code_d := disj_or (hP.lay.sub (r := R.aD) (s := R.code) (Iv.sub_elem (by omega)) code_sub) }

/-- At `4eb0`, then the carry digit and `c->used := a->used + 1`: a `Tail2` at `4ec4`. -/
theorem carry (hP : Api.AddD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) :
    Triple (St F m v outp sp pa adp a ra s0 0x80004eb0#64
        (jL ra sp pa pa a.used adp a.used (addDCarry a b a.used)) (ovl (addDDigits a b) a.digit a.used))
      (TSt F m v outp sp pa adp a ra s0 0x80004ec4#64 (tL ra sp pa a.used adp (a.used + 1))
        (a.used + 1) a.sign (ovl (addDDigits a b) a.digit (a.used + 1))) := by
  intro cf ⟨M, hI, hat⟩
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt; have hroom := hP.room
  have hcl := addDCarry_lt hs hP.hb a.used
  rw [radix_eq] at hcl
  have hro := ro2 (s0 := s0) hP hF hI
  have hI' := hI.step (i := a.used) (v := addDCarry a b a.used) (by omega) (by omega)
    (by simp [addDDigits])
  have hsw : Frm ρ [R.aS] (writeLog M [(adp + 4 * a.used, 4, BitVec.ofNat 64 (addDCarry a b a.used))])
      (writeLog (writeLog M [(adp + 4 * a.used, 4, BitVec.ofNat 64 (addDCarry a b a.used))])
        [(pa, 4, BitVec.ofNat 64 (a.used + 1))]) := Frm.sw (Iv.sub_pre (by decide))
  have hT := (snap1 (s0 := s0) hP hF).tail hP.lay (by omega) hP.sp_ge hI'
  have e : writeLog M [(adp + 4 * a.used, 4, BitVec.ofNat 64 (addDCarry a b a.used)),
      (pa, 4, BitVec.ofNat 64 (a.used + 1))] = writeLog (writeLog M [(adp + 4 * a.used, 4,
        BitVec.ofNat 64 (addDCarry a b a.used))]) [(pa, 4, BitVec.ofNat 64 (a.used + 1))] :=
    writeLog_append M [(adp + 4 * a.used, 4, BitVec.ofNat 64 (addDCarry a b a.used))] _
  have h := c_step ra v outp sp pa pa a.used adp a.used _ M hro.img.mpAddD (cfacts hP (by simpa [Layout.offUsed] using ((snap1 (s0 := s0) hP hF).tail hP.lay (by omega) hP.sp_ge hI).hdr.used)) (by omega) cf hat
  rw [e] at h
  obtain ⟨cf', hst, hat'⟩ := h
  refine ⟨cf', hst, _, ?_, hat'⟩
  exact { fr := Frm.step hT.fr hsw
          sv := hT.sv.keep hP.lay (by omega) hP.sp_ge hsw
          hdr := hT.hdr.set_used _ (by omega)
          arr := hsw.keep hP.lay (ArrAt.reads (r := R.aD) (Iv.sub_self _)) hT.arr }

/-- **`mp_add_d(a, b, a)` for `a ≥ 0`**, any stack depth `F ≥ 64`. -/
theorem pos_correct (hF : 64 ≤ F) (hP : Api.AddD.PreI F m sp pa adp a b ra) (hs : a.sign = Layout.mpZpos) :
    Triple (At 0x80004e30#64 (entryL ra s0 sp pa b pa) m v.keepR outp)
      (Api.AddD.RetI F m v outp sp pa adp a b ra s0) := by
  have hsh := hP.va.toShape
  have hua := hsh.used_le; have hroom := hP.room
  have hH := hfacts (s0 := s0) hP hF
  rw [show a.sign = 0 from hs] at hH
  have hsn := snap1 (s0 := s0) hP hF
  have hI0 : ArrFrm ρ R.aD (m1Of m ra s0 sp) (m1Of m ra s0 sp) adp a.alloc (ovl (addDDigits a b) a.digit 0) :=
    ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; exact hsn.arr)
  have hneg : a.sign ≠ Layout.mpNeg := by rw [hs]; decide
  suffices hmain : Triple (At 0x80004e54#64 (pL ra sp pa b pa a.used) (m1Of m ra s0 sp) v.keepR outp)
      (RetD F m v outp sp pa adp a ra s0 (addDDigits a b) (a.used + 1) 0) from
    Triple.seq (p_step ra s0 v outp sp pa b pa a.used a.alloc m hP.img.mpAddD (pfacts hP hF))
      (Triple.rmap (fun cf ⟨c', M, hat, ho⟩ => ⟨c', M, hat, ho.repr,
        ⟨fun _ => ho.res, fun h => absurd h hneg, fun h => absurd h hneg⟩, ho.frame⟩) hmain)
  refine Triple.seq ?_ (Triple.seq (carry hP hF) (tail hP hF (addDDigits_lt hsh hP.hb) (addDDigits_high a b)
    (by omega)))
  by_cases h0 : a.used = 0
  · rw [show pL ra sp pa b pa a.used = pL ra sp pa b pa 0 by rw [h0]]
    have h := z_step ra v outp sp pa b pa a.used adp adp (m1Of m ra s0 sp) (ro1 hP hF).img.mpAddD (h0 ▸ hH)
    rw [writeLog_nil] at h
    exact Triple.rmap (fun cf h' => (⟨_, by rw [h0]; exact hI0, by rw [h0] at h' ⊢; exact h'⟩ : St F m v outp sp pa adp a ra s0
      0x80004eb0#64 (jL ra sp pa pa a.used adp a.used (addDCarry a b a.used))
      (ovl (addDDigits a b) a.digit a.used) cf)) h
  · have h1 : 1 ≤ a.used := by omega
    have h := e_step ra v outp sp pa b pa a.used a.used adp adp (m1Of m ra s0 sp) (ro1 hP hF).img.mpAddD hH h1
    rw [writeLog_nil] at h
    exact Triple.seq (Triple.rmap (fun cf h' => (⟨_, hI0, h'⟩ : St F m v outp sp pa adp a ra s0
      0x80004e80#64 (lL ra sp pa pa a.used adp adp 0 (addDCarry a b 0)) (ovl (addDDigits a b) a.digit 0) cf)) h)
      (loop hP hF h1 0 (by omega))

end

end InPlace

/-- **`mp_add_d(a, b, a)` on the machine for `a ≥ 0`.** -/
theorem correct_inplace_pos : Api.AddD.StatementInPlacePos :=
  fun hF hP hs => InPlace.pos_correct hF hP hs

end Tom.Machine.Fn.AddD
