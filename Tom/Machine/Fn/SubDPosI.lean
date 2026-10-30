import Tom.Machine.Api.SubD
import Tom.Machine.Kit.UnDTail
import Tom.Machine.Fn.SubDPos

/-!
# `mp_sub_d(a, b, a)` on the machine for `a ≥ 0`

`Fn/SubDPos.lean` with `c = a` (same struct, same digits), over `Un`'s regions:
the loop reads `a[i]` from the overlay before storing `c[i]` there; the big
branch stores `c->used := a->used` and reads `a->used` back from the same
word, so its struct stores are two segments (`bb1_step`, `bb2_step`) and the
snapshot `m2Of` writes them one at a time. `oldused = a->used`, so the
zeroing never calls `memset`.
-/

namespace Tom.Machine.Fn.SubD.InPlace

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api
open Tom.Machine.Api.Un (R isW ws Saved2 Tail2 Snap2)

/-- What stays as at the entry. -/
structure RO (M : Mem) : Prop where
  img : Img M

/-- The memory after the big branch's struct stores (one at a time: the code reads the first back). -/
def m2Of (m : Mem) (ra s0 : BitVec 64) (sp pa ua : Nat) : Mem :=
  writeLog (writeLog (m1Of m ra s0 sp) [(pa, 4, BitVec.ofNat 64 ua)]) [(pa + 8, 4, 0#64)]

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

theorem RO.of (hP : Api.SubD.PreI F m sp pa adp a b ra) {M : Mem} (hF : Frm ρ ws m M) : RO M :=
  { img := hF.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img }

theorem f1 (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) :
    Frm ρ [R.stk] m (m1Of m ra s0 sp) := by
  have := hP.sp_ge
  exact Frm.store (by simp only [LogIn, frameLog, Iv.Sub, Un.lay, and_true]; omega)

theorem sv1 (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) :
    Saved2 (m1Of m ra s0 sp) ra s0 sp :=
  have := hP.sp_ge
  { ra_v := bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog, OutLRange])
    s0_v := bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog, OutLRange]; omega) }

theorem rc1 (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) :
    MpAt (m1Of m ra s0 sp) pa adp a :=
  (f1 hP hF).keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_

theorem ro1 (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) :
    RO (m1Of m ra s0 sp) := RO.of hP (f1 hP hF).mono

theorem pfacts (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) :
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

theorem hfacts (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) {sa ua : Nat} (hs : a.sign = sa)
    (hu : a.used = ua) : HFacts (m1Of m ra s0 sp) pa pa sa ua a.used adp adp :=
  have hro := ro1 (s0 := s0) hP hF
  have hc := rc1 (s0 := s0) hP hF
  have := hP.va.used_le; have := hP.va.alloc_lt; have := hP.va.toShape.alloc_lt; have := hP.va.toShape.used_le
  have hsg := hP.va.sign_ok
  { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    rc := by simpa [Layout.sizeofMpInt] using hP.ga.st
    pc_al := hP.ga.st_al
    sa_v := by rw [← hs]; simpa [Layout.offSign] using hc.sign
    ua_v := by rw [← hu]; simpa [Layout.offUsed] using hc.used
    ou_v := by simpa [Layout.offUsed] using hc.used
    adp_v := by simpa [Layout.offDp] using hc.dpv
    cdp_v := by simpa [Layout.offDp] using hc.dpv
    sa_lt := by rw [← hs]; simp only [Layout.mpZpos, Layout.mpNeg] at hsg; omega
    ua_lt := by rw [← hu]; omega, ou_lt := by omega
    code_c := disj_or (hP.lay.sub (r := R.aS) (s := R.code) (Iv.sub_self _) code_sub) }

theorem cfacts (hP : Api.SubD.PreI F m sp pa adp a b ra) : CFacts pa :=
  { rc := by simpa [Layout.sizeofMpInt] using hP.ga.st
    pc_al := hP.ga.st_al
    code_c := disj_or (hP.lay.sub (r := R.aS) (s := R.code) (Iv.sub_self _) code_sub) }

theorem dfacts (hP : Api.SubD.PreI F m sp pa adp a b ra) : DFacts adp :=
  have hrc : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have := hP.room
  { rd := ⟨by have := hrc.lo_ge; omega, by have := hrc.hi_le; omega, by have := hrc.off; omega⟩
    d_al := hP.ga.ds_al
    code_d := disj_or (hP.lay.sub (r := R.aD) (s := R.code) (I := ⟨adp, 4⟩)
      ⟨by simp [Un.lay], by simp only [Un.lay]; omega⟩ code_sub) }

theorem xfacts (hP : Api.SubD.PreI F m sp pa adp a b ra) {M : Mem} (hc : MpAt M pa adp a)
    (h1 : 1 ≤ a.used) : XFacts M adp (a.digit 0) :=
  have hra : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have := hP.va.used_le
  { rx := ⟨by have := hra.lo_ge; omega, by have := hra.hi_le; omega, by have := hra.off; omega⟩
    x_v := by simpa [Layout.sizeofDigit] using hc.digits 0 (by omega)
    x_lt := by have := hP.va.digit_lt 0; rwa [radix_eq] at this }

/-! ## The tail -/

/-- `mp_clamp(c)` and the epilogue: the branch's result. -/
theorem finish (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) {n s : Nat} {dig : Nat → Nat}
    (hlt : ∀ i, dig i < radix) (hhi : ∀ i, n ≤ i → dig i = 0) (hn : n ≤ a.alloc) :
    Triple (TSt F m v outp sp pa adp a ra s0 0x80006514#64 (mL sp pa) n s dig)
      (RetD F m v outp sp pa adp a ra s0 dig n s) := by
  intro cf ⟨M, hT, hat⟩
  have := hP.sp_ge; have hal := hP.va.toShape.alloc_lt
  have hro := RO.of hP hT.fr
  have hd := dMid_digit (c := a) (s := s) hhi hn
  have hcp : Clamp.Pre M pa adp (dMid a dig n s) :=
    { repr := HdrAt.mpAt hT.hdr (hT.arr.congr fun j _ => by rw [hd])
      shape := dMid_shape hlt hhi hn hal
      geom := hP.ga, code := hro.img.mpClamp
      code_off := disj_or (hP.lay.sub (r := R.aS) (s := R.code) (Iv.sub_self _) clamp_sub) }
  refine Triple.seq (d_step v outp sp pa M hro.img.mpSubD)
    (Triple.seq (clamp_call v outp sp pa adp _ M hro.img.mpSubD hcp) ?_) cf hat
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
    (r_step ra s0 v outp sp M' (RO.of hP hF').img.mpSubD hrf) cf hat'

theorem fin_eq {n : Nat} {dig : Nat → Nat} (hc : a.Shape) (hhi : ∀ i, n ≤ i → dig i = 0) {k : Nat}
    (hk : n ≤ k) (hk' : a.used ≤ k) : ∀ j, j < a.alloc → ovl dig a.digit k j = dig j := fun j _ => by
  simp only [ovl]
  split
  · rfl
  · rw [hc.high_zero j (by omega), hhi j (by omega)]

/-- `oldused ≤ n`: the digits from `n` on are zero already. -/
theorem zero0 (hP : Api.SubD.PreI F m sp pa adp a b ra) {n s : Nat} {dig : Nat → Nat}
    (hhi : ∀ i, n ≤ i → dig i = 0) (hou : a.used ≤ n) :
    Triple (TSt F m v outp sp pa adp a ra s0 0x80006514#64 (jL ra sp pa) n s (ovl dig a.digit n))
      (TSt F m v outp sp pa adp a ra s0 0x80006514#64 (mL sp pa) n s dig) :=
  Triple.rmap (fun _ ⟨M, hT, hat⟩ => ⟨M, hT.congr (fin_eq hP.va.toShape hhi (Nat.le_refl _) hou),
    hat.weaken (by simp [jL, mL])⟩) Triple.rfl

/-- `oldused > n`: `memset` the digits `[n, oldused)`. -/
theorem zero1 (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) {n s : Nat} {dig : Nat → Nat}
    (hhi : ∀ i, n ≤ i → dig i = 0) (hou : n < a.used) :
    Triple (TSt F m v outp sp pa adp a ra s0 0x80006510#64 (msL ra sp pa adp n a.used) n s
        (ovl dig a.digit n))
      (TSt F m v outp sp pa adp a ra s0 0x80006514#64 (mL sp pa) n s dig) := by
  intro cf ⟨M, hT, hat⟩
  have hbu := hP.va.toShape.used_le
  have hro := RO.of hP hT.fr
  refine Triple.rmap (fun cf ⟨M', hat', hpost⟩ => ⟨M', ?_, hat'⟩)
    (memset_call ra v outp sp pa adp n a.used M hro.img.mpSubD
      (Un.memset_pre hP.lay hP.ga hro.img (by omega) hbu)) cf hat
  exact (hT.fill hP.lay (by omega) hP.sp_ge (by omega) hbu hpost fun j h1 _ => hhi j h1).congr
    (fin_eq hP.va.toShape hhi (by omega) (Nat.le_refl _))

/-! ## The small branches -/

theorem small_tail (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) (d : Nat)
    (hd : d < 2 ^ 32) (hdd : d = smallDigits a b 0) :
    Tail2 ρ m (writeLog (m1Of m ra s0 sp) (smallLog pa adp d)) ra s0 sp pa adp 1 a.alloc 1
      (ovl (smallDigits a b) a.digit 1) := by
  have := hP.sp_ge; have := hP.room
  have hc1 := rc1 (s0 := s0) hP hF
  have hA0 : ArrFrm ρ R.aD (m1Of m ra s0 sp) (m1Of m ra s0 sp) adp a.alloc (ovl (smallDigits a b) a.digit 0) :=
    ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; exact hc1.arr)
  have hA := hA0.step (i := 0) (v := d) (by omega) hd hdd
  rw [show adp + 4 * 0 = adp by omega] at hA
  have hS2 : Frm ρ [R.aS] (writeLog (m1Of m ra s0 sp) [(adp, 4, BitVec.ofNat 64 d)])
      (writeLog (writeLog (m1Of m ra s0 sp) [(adp, 4, BitVec.ofNat 64 d)])
        [(pa + 8, 4, BitVec.ofNat 64 1), (pa, 4, BitVec.ofNat 64 1)]) :=
    Frm.store (by simp only [LogIn, Iv.Sub, Un.lay, and_true]; omega)
  have e : writeLog (m1Of m ra s0 sp) (smallLog pa adp d) = writeLog (writeLog (m1Of m ra s0 sp)
      [(adp, 4, BitVec.ofNat 64 d)]) [(pa + 8, 4, BitVec.ofNat 64 1), (pa, 4, BitVec.ofNat 64 1)] :=
    writeLog_append _ [(adp, 4, BitVec.ofNat 64 d)] _
  have e2 : ∀ X : Mem, writeLog X [(pa + 8, 4, BitVec.ofNat 64 1), (pa, 4, BitVec.ofNat 64 1)] =
      writeLog (writeLog X [(pa + 8, 4, BitVec.ofNat 64 1)]) [(pa, 4, BitVec.ofNat 64 1)] := fun X =>
    writeLog_append X [(pa + 8, 4, BitVec.ofNat 64 1)] [(pa, 4, BitVec.ofNat 64 1)]
  have hal := hP.va.toShape.alloc_lt
  rw [e]
  exact { fr := ((f1 hP hF).trans (hA.fr.trans hS2)).mono
          sv := ((sv1 hP hF).keep hP.lay (by omega) hP.sp_ge hA.fr).keep hP.lay (by omega) hP.sp_ge hS2
          hdr := by
            rw [e2]
            exact ((hA.fr.keep hP.lay (HdrAt.reads (r := R.aS) (Iv.sub_self _)) hc1.hdr).set_sign 1
              (by decide)).set_used 1 (by decide)
          arr := hS2.keep hP.lay (ArrAt.reads (r := R.aD) (Iv.sub_self _)) hA.arr }

theorem smallDigits_high' (b : Nat) : ∀ i, 1 ≤ i → smallDigits a b i = 0 := smallDigits_high a b

/-- The small branches (`0 ≤ a ≤ b`): `c := -(b - a)`. -/
theorem small (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) (hs : a.sign = 0)
    (hsm : SubDSmall a b) :
    Triple (At 0x800064c8#64 (pL ra sp pa b pa a.used) (m1Of m ra s0 sp) v.keepR outp)
      (RetD F m v outp sp pa adp a ra s0 (smallDigits a b) 1 1) := by
  have hb := hP.hb; rw [radix_eq] at hb
  have hcu := hP.va.toShape.used_le; have hcl := hP.va.toShape.alloc_lt; have := hP.room
  have hrc : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have hfin := finish (v := v) (outp := outp) (s0 := s0) hP hF (n := 1) (s := 1) (smallDigits_lt hP.hb)
    (smallDigits_high a b) (by omega)
  rcases hsm with ⟨h1, hxb⟩ | h0
  · have hH := hfacts (s0 := s0) hP hF hs h1
    rw [show pL ra sp pa b pa a.used = pL ra sp pa b pa 1 by rw [h1]]
    have hx := xfacts hP (rc1 (s0 := s0) hP hF) (by omega)
    have hd : b - a.digit 0 = smallDigits a b 0 := by simp [smallDigits]
    refine Triple.seq (nil_post (s1_step ra v outp sp pa b pa a.used adp adp _ _ (ro1 hP hF).img.mpSubD hH hx hb hxb)) ?_
    by_cases hou : a.used ≤ 1
    · exact Triple.seq (Triple.rmap (fun cf h => ⟨_, small_tail hP hF _ (by omega) hd, h⟩)
        (s1a_step ra v outp sp b pa a.used adp _ (m1Of m ra s0 sp) (ro1 hP hF).img.mpSubD (cfacts hP) (dfacts hP) hb hxb hou))
        (Triple.seq (zero0 hP (smallDigits_high a b) hou) hfin)
    · exact Triple.seq (Triple.rmap (fun cf h => ⟨_, small_tail hP hF _ (by omega) hd, h⟩)
        (s1b_step ra v outp sp b pa a.used adp _ (m1Of m ra s0 sp) (ro1 hP hF).img.mpSubD (cfacts hP) (dfacts hP) hb hxb
          (by omega) (by omega) (by have := hrc.hi_le; omega)))
        (Triple.seq (zero1 hP hF (smallDigits_high a b) (by omega)) hfin)
  · have hH := hfacts (s0 := s0) hP hF hs h0
    rw [show pL ra sp pa b pa a.used = pL ra sp pa b pa 0 by rw [h0]]
    have hd : b = smallDigits a b 0 := by simp [smallDigits, hP.va.high_zero 0 (by omega)]
    refine Triple.seq (nil_post (s0_step ra v outp sp pa b pa a.used adp adp _ (ro1 hP hF).img.mpSubD hH
      (by have := hrc.hi_le; omega))) ?_
    by_cases hou : a.used ≤ 1
    · exact Triple.seq (Triple.rmap (fun cf h => ⟨_, small_tail hP hF _ (by omega) hd, h⟩)
        (s0a_step ra v outp sp b pa a.used adp (m1Of m ra s0 sp) (ro1 hP hF).img.mpSubD (cfacts hP) (dfacts hP) (by omega) hou))
        (Triple.seq (zero0 hP (smallDigits_high a b) hou) hfin)
    · exact Triple.seq (Triple.rmap (fun cf h => ⟨_, small_tail hP hF _ (by omega) hd, h⟩)
        (s0b_step ra v outp sp b pa a.used adp (m1Of m ra s0 sp) (ro1 hP hF).img.mpSubD (cfacts hP) (dfacts hP) (by omega)
          (by omega) (by omega) (by have := hrc.hi_le; omega)))
        (Triple.seq (zero1 hP hF (smallDigits_high a b) (by omega)) hfin)

/-! ## The big branch -/

theorem snap2 (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) :
    Snap2 ρ m (m2Of m ra s0 sp pa a.used) ra s0 sp pa adp a.used a.alloc 0 a.digit := by
  have := hP.sp_ge; have := hP.va.used_le; have := hP.va.alloc_lt
  have hc1 := rc1 (s0 := s0) hP hF
  have hS1 : Frm ρ [R.aS] (m1Of m ra s0 sp) (writeLog (m1Of m ra s0 sp) [(pa, 4, BitVec.ofNat 64 a.used)]) :=
    Frm.sw (Iv.sub_pre (by decide))
  have hS2 : Frm ρ [R.aS] (writeLog (m1Of m ra s0 sp) [(pa, 4, BitVec.ofNat 64 a.used)])
      (m2Of m ra s0 sp pa a.used) := Frm.sw (by simp only [Iv.Sub, Un.lay]; omega)
  have hS := (hS1.trans hS2).mono (ws' := [R.aS])
  exact { fr := ((f1 hP hF).trans hS).mono
          sv := (sv1 hP hF).keep hP.lay (by omega) hP.sp_ge hS
          hdr := (hc1.hdr.set_used _ (by omega)).set_sign 0 (by decide)
          arr := hS.keep hP.lay (ArrAt.reads (r := R.aD) (Iv.sub_self _)) hc1.arr }

/-- The big branch's join points: `c`'s digits hold `f`, nothing else changed since `m2Of`. -/
abbrev St (F : Nat) (m : Mem) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt)
    (ra s0 : BitVec 64) :=
  ASt (Un.lay F sp pa adp a) R.aD (m2Of m ra s0 sp pa a.used) adp a.alloc v.keepR outp

theorem ro2 (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) {M : Mem} {f : Nat → Nat}
    (hI : ArrFrm ρ R.aD (m2Of m ra s0 sp pa a.used) M adp a.alloc f) : RO M :=
  RO.of hP (((snap2 (s0 := s0) hP hF).fr.trans hI.fr).mono)

theorem lfacts (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) {M : Mem} {i : Nat}
    (hI : ArrFrm ρ R.aD (m2Of m ra s0 sp pa a.used) M adp a.alloc (ovl (subDDigits a b) a.digit i))
    (hi : i < a.used) : LFacts M pa adp adp a.used i (a.digit i) :=
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt
  have hra : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have hT := (snap2 (s0 := s0) hP hF).tail hP.lay (by omega) hP.sp_ge hI
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

theorem borrowD_eq {x u : Nat} (hx : x < 268435456) (hu : u < 268435456) :
    (x + 4294967296 - u) % 4294967296 / 2147483648 = if x < u then 1 else 0 := by
  split <;> omega

/-- One loop segment (back edge to `6558`, or an exit). -/
theorem l_seg (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) (i : Nat) (hi : i < a.used)
    (pa' : BitVec 64) (Lf : Nat → GRegs)
    (hseg : ∀ M, CodeAt M mpSubDBase mpSubDCode → LFacts M pa adp adp a.used i (a.digit i) →
      Triple (At 0x80006558#64 (lL ra sp pa pa a.used adp adp i (subDBorrow a b i)) M v.keepR outp)
      (At pa' (Lf ((a.digit i + 4294967296 - subDBorrow a b i) % 4294967296 / 2147483648))
        (writeLog M [(adp + 4 * i, 4, BitVec.ofNat 64
          ((a.digit i + 268435456 - subDBorrow a b i) % 268435456))]) v.keepR outp)) :
    Triple (St F m v outp sp pa adp a ra s0 0x80006558#64
        (lL ra sp pa pa a.used adp adp i (subDBorrow a b i)) (ovl (subDDigits a b) a.digit i))
      (St F m v outp sp pa adp a ra s0 pa' (Lf (subDBorrow a b (i + 1)))
        (ovl (subDDigits a b) a.digit (i + 1))) := by
  have hs := hP.va.toShape
  have hua := hs.used_le; have hroom := hP.room
  refine ASt.store (v := (a.digit i + 268435456 - subDBorrow a b i) % 268435456) (fun M hI => ?_) (by omega)
    (by simp only [subDDigits, if_pos hi, radix_eq]) (by omega)
  have hro := ro2 (s0 := s0) hP hF hI
  have hl := lfacts hP hF hI hi
  have h := hseg M hro.img.mpSubD hl
  rwa [borrowD_eq hl.x_lt (by have := subDBorrow_le (a := a) hP.hb i; rwa [radix_eq] at this),
    ← subDBorrow_succ] at h

theorem loop (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) (h1 : 1 ≤ a.used)
    (pcE : BitVec 64) (LE : GRegs)
    (hlast : ∀ M, CodeAt M mpSubDBase mpSubDCode → LFacts M pa adp adp a.used (a.used - 1) (a.digit (a.used - 1)) →
      Triple (At 0x80006558#64 (lL ra sp pa pa a.used adp adp (a.used - 1) (subDBorrow a b (a.used - 1))) M v.keepR outp)
      (At pcE LE (writeLog M [(adp + 4 * (a.used - 1), 4, BitVec.ofNat 64
          ((a.digit (a.used - 1) + 268435456 - subDBorrow a b (a.used - 1)) % 268435456))]) v.keepR outp)) :
    ∀ i, i < a.used → Triple (St F m v outp sp pa adp a ra s0 0x80006558#64
        (lL ra sp pa pa a.used adp adp i (subDBorrow a b i)) (ovl (subDDigits a b) a.digit i))
      (St F m v outp sp pa adp a ra s0 pcE LE (ovl (subDDigits a b) a.digit a.used)) := by
  have hb := hP.hb
  refine Triple.countup (fun i hi => l_seg hP hF i (by omega) _ (fun u => lL ra sp pa pa a.used adp adp (i + 1) u)
    fun M hc hf => l_step ra v outp sp pa pa a.used adp adp a.used i _ _ M hc hf
      (by have := subDBorrow_le (a := a) hb i; rwa [radix_eq] at this) hi) ?_
  have h := l_seg (s0 := s0) (v := v) (outp := outp) hP hF (a.used - 1) (by omega) pcE (fun _ => LE) hlast
  rw [show a.used - 1 + 1 = a.used by omega] at h
  exact h

/-- The big branch (`a > b ≥ 0`): `c := a - b`. -/
theorem big (hP : Api.SubD.PreI F m sp pa adp a b ra) (hF : 64 ≤ F) (hs : a.sign = 0)
    (hnsm : ¬ SubDSmall a b) :
    Triple (At 0x800064c8#64 (pL ra sp pa b pa a.used) (m1Of m ra s0 sp) v.keepR outp)
      (RetD F m v outp sp pa adp a ra s0 (subDDigits a b) a.used 0) := by
  have hb := hP.hb; rw [radix_eq] at hb
  have hcu := hP.va.toShape.used_le; have hcl := hP.va.toShape.alloc_lt; have hroom := hP.room
  have hua := hP.va.used_le; have hal := hP.va.alloc_lt
  have hrc : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have hH := hfacts (s0 := s0) hP hF hs rfl
  have h1 : 1 ≤ a.used := by
    rcases Nat.eq_zero_or_pos a.used with h | h
    · exact absurd (Or.inr h) hnsm
    · exact h
  have hfin := finish (v := v) (outp := outp) (s0 := s0) hP hF (n := a.used) (s := 0) (subDDigits_lt a b)
    (subDDigits_high a b) (by omega)
  -- to `653c`
  have hpre : Triple (At 0x800064c8#64 (pL ra sp pa b pa a.used) (m1Of m ra s0 sp) v.keepR outp)
      (At 0x8000653c#64 (bL ra sp pa b pa a.used a.used adp adp) (m1Of m ra s0 sp) v.keepR outp) := by
    by_cases h2 : 2 ≤ a.used
    · exact nil_post (b2_step ra v outp sp pa b pa a.used a.used adp adp _ (ro1 hP hF).img.mpSubD hH h2)
    · have hu1 : a.used = 1 := by omega
      have hx := xfacts hP (rc1 (s0 := s0) hP hF) h1
      have hxb : b < a.digit 0 := Nat.lt_of_not_le fun h => hnsm (Or.inl ⟨hu1, h⟩)
      rw [show pL ra sp pa b pa a.used = pL ra sp pa b pa 1 by rw [hu1],
        show bL ra sp pa b pa a.used a.used adp adp = bL ra sp pa b pa 1 a.used adp adp by rw [hu1]]
      exact nil_post (b1_step ra v outp sp pa b pa a.used adp adp _ _ (ro1 hP hF).img.mpSubD
        (hfacts (s0 := s0) hP hF hs hu1) hx hb hxb)
  have hsn := snap2 (s0 := s0) hP hF
  have hI0 : ArrFrm ρ R.aD (m2Of m ra s0 sp pa a.used) (m2Of m ra s0 sp pa a.used) adp a.alloc
      (ovl (subDDigits a b) a.digit 0) := ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; exact hsn.arr)
  have hS1 : Frm ρ [R.aS] (m1Of m ra s0 sp) (writeLog (m1Of m ra s0 sp) [(pa, 4, BitVec.ofNat 64 a.used)]) :=
    Frm.sw (Iv.sub_pre (by decide))
  have hu1 : bytesT4 (writeLog (m1Of m ra s0 sp) [(pa, 4, BitVec.ofNat 64 a.used)]) pa = BitVec.ofNat 32 a.used := by
    simpa [Layout.offUsed] using ((rc1 (s0 := s0) hP hF).hdr.set_used a.used (by omega)).used
  refine Triple.seq hpre (Triple.seq (bb1_step ra v outp sp pa b pa a.used a.used adp adp _ (ro1 hP hF).img.mpSubD
    (cfacts hP)) (Triple.seq (Triple.rmap (fun cf h => (⟨_, hI0, h⟩ : St F m v outp sp pa adp a
      ra s0 0x80006558#64 (lL ra sp pa pa a.used adp adp 0 (subDBorrow a b 0)) (ovl (subDDigits a b) a.digit 0) cf))
    (bb2_step ra v outp sp pa b pa a.used a.used adp adp _ (RO.of hP ((f1 hP hF).trans hS1).mono).img.mpSubD
      (cfacts hP) (by simpa [Layout.sizeofMpInt] using hP.ga.st) hu1 (by omega) h1)) ?_))
  by_cases hou : a.used ≤ a.used
  · refine Triple.seq (Triple.rmap (fun cf ⟨M, hI, hat⟩ => ⟨M, hsn.tail hP.lay (by omega) hP.sp_ge hI, hat⟩)
      (loop hP hF h1 _ _ (fun M hc hf => la_step ra v outp sp pa pa a.used adp adp a.used (a.used - 1) _ _ M hc hf
        (by have := subDBorrow_le (a := a) hP.hb (a.used - 1); rwa [radix_eq] at this) (by omega) hou
        (by omega)) 0 (by omega)))
      (Triple.seq (zero0 hP (subDDigits_high a b) hou) hfin)
  · refine Triple.seq (Triple.rmap (fun cf ⟨M, hI, hat⟩ => ⟨M, hsn.tail hP.lay (by omega) hP.sp_ge hI, hat⟩)
      (loop hP hF h1 _ _ (fun M hc hf => lb_step ra v outp sp pa pa a.used adp adp a.used (a.used - 1) _ _ M hc hf
        (by have := subDBorrow_le (a := a) hP.hb (a.used - 1); rwa [radix_eq] at this) (by omega) (by omega)
        (by omega) (by have := hrc.hi_le; omega)) 0 (by omega)))
      (Triple.seq (zero1 hP hF (subDDigits_high a b) (by omega)) hfin)

/-- **`mp_sub_d(a, b, a)` for `a ≥ 0`**, any stack depth `F ≥ 64`. -/
theorem pos_correct (hF : 64 ≤ F) (hP : Api.SubD.PreI F m sp pa adp a b ra) (hs : a.sign = Layout.mpZpos) :
    Triple (At 0x800064a4#64 (entryL ra s0 sp pa b pa) m v.keepR outp)
      (Api.SubD.RetI F m v outp sp pa adp a b ra s0) := by
  refine Triple.seq (p_step ra s0 v outp sp pa b pa a.used a.alloc m hP.img.mpSubD (pfacts hP hF)) ?_
  have hneg : a.sign ≠ Layout.mpNeg := by rw [hs]; decide
  by_cases hsm : SubDSmall a b
  · exact Triple.rmap (fun cf ⟨c', M, hat, ho⟩ => ⟨c', M, hat, ho.repr,
      ⟨fun h => absurd h hneg, fun _ _ => ho.res, fun _ h => absurd hsm h⟩, ho.frame⟩) (small hP hF hs hsm)
  · exact Triple.rmap (fun cf ⟨c', M, hat, ho⟩ => ⟨c', M, hat, ho.repr,
      ⟨fun h => absurd h hneg, fun _ h => absurd h hsm, fun _ _ => ho.res⟩, ho.frame⟩) (big hP hF hs hsm)

end

end InPlace

/-- **`mp_sub_d(a, b, a)` on the machine for `a ≥ 0`.** -/
theorem correct_inplace_pos : Api.SubD.StatementInPlacePos :=
  fun hF hP hs => InPlace.pos_correct hF hP hs

end Tom.Machine.Fn.SubD
