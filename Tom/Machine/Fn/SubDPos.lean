import Tom.Machine.Fn.SubD
import Tom.Machine.Api.SubD
import Tom.Machine.Kit.DTail

/-!
# `mp_sub_d` on the machine: the branches for `a ≥ 0`

`pos_correct`: from the entry with `a->sign = MP_ZPOS`, any stack depth
`F ≥ 64` (its own frame; `memset` and `mp_clamp` use none), `mp_sub_d`
meets `Api.SubD.Post` (its `small` and `big` fields; `neg` is vacuous). It
does not call `mp_add_d`, so `mp_add_d`'s negative branch can use it
(`Fn/AddDMain.lean`).

States, over `Two`'s regions with `c` the written operand (`bS`, `bD`):
after the prologue the memory `m1Of` (the saved registers); the small
branches store `c[0]`, `c->sign`, `c->used` at once (`small_tail`); the big
branch stores `c->used`, `c->sign` (the snapshot `m2Of`, a `Two.Snap2`),
then its loop changes only `c`'s digits (`ASt … .bD`). Both reach a
`Two.Tail2` at `6510` (the `memset` call) or `6514`; `zero0`/`zero1` zero
the excess digits, `finish` is `mp_clamp` and the epilogue, whose
`ClampPost` of `dMid` is the branch's `DRes` (`DRes.of_clamp`).
-/

namespace Tom.Machine.Fn.SubD

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api
open Tom.Machine.Api.Two (R isW ws Saved2 Tail2 Snap2)

theorem code_sub : Iv.Sub ⟨mpSubDBase, 412⟩ textIv := ⟨by decide, by decide⟩

theorem clamp_sub : Iv.Sub ⟨mpClampBase, 64⟩ textIv := ⟨by decide, by decide⟩

theorem disj_or {x n y k : Nat} (h : Iv.Disj ⟨x, n⟩ ⟨y, k⟩) : x + n ≤ y ∨ y + k ≤ x := h

/-- What stays as at the entry. -/
structure RO (M : Mem) (pa adp : Nat) (a : MpInt) : Prop where
  img : Img M
  ra_ : MpAt M pa adp a

/-- The memory after the prologue. -/
def m1Of (m : Mem) (ra s0 : BitVec 64) (sp : Nat) : Mem := writeLog m (frameLog ra s0 sp)

/-- The memory after the big branch's struct stores. -/
def m2Of (m : Mem) (ra s0 : BitVec 64) (sp pc ua : Nat) : Mem :=
  writeLog (m1Of m ra s0 sp) [(pc, 4, BitVec.ofNat 64 ua), (pc + 8, 4, 0#64)]

/-- At `pc0` with `c->used = n`, sign `s`, digits `f`. -/
def TSt (F : Nat) (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a c : MpInt)
    (ra s0 : BitVec 64) (pc0 : BitVec 64) (L : GRegs) (n s : Nat) (f : Nat → Nat)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, Tail2 (Two.lay F sp pa adp pc cdp a c) m M ra s0 sp pc cdp n c.alloc s f ∧ At pc0 L M v.keepR outp cf

/-- What a branch leaves: `c'` at `c`, its `DRes`, memory changed only in `ws`. -/
structure DOut (ρ : R → Iv) (m M : Mem) (pc cdp : Nat) (c c' : MpInt) (dig : Nat → Nat) (n s : Nat) : Prop where
  repr : MpAt M pc cdp c'
  res : DRes c c' dig n s
  frame : Frm ρ ws m M

/-- The return of a branch. -/
def RetD (F : Nat) (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a c : MpInt)
    (ra s0 : BitVec 64) (dig : Nat → Nat) (n s : Nat) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    DOut (Two.lay F sp pa adp pc cdp a c) m M pc cdp c c' dig n s

section
variable {F : Nat} {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat}
  {c : MpInt} {ra s0 : BitVec 64}

local notation "ρ" => Two.lay F sp pa adp pc cdp a c

theorem RO.of (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) {M : Mem} (hF : Frm ρ ws m M) : RO M pa adp a :=
  { img := hF.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
    ra_ := hF.keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_ }

theorem f1 (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    Frm ρ [R.stk] m (m1Of m ra s0 sp) := by
  have := hP.sp_ge
  exact Frm.store (by simp only [LogIn, frameLog, Iv.Sub, Two.lay, and_true]; omega)

theorem sv1 (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    Saved2 (m1Of m ra s0 sp) ra s0 sp :=
  have := hP.sp_ge
  { ra_v := bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog, OutLRange])
    s0_v := bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog, OutLRange]; omega) }

theorem rc1 (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    MpAt (m1Of m ra s0 sp) pc cdp c :=
  (f1 hP hF).keep hP.lay (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hP.rc

theorem ro1 (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    RO (m1Of m ra s0 sp) pa adp a := RO.of hP (f1 hP hF).mono

theorem pfacts (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    PFacts m sp pa pc a.used c.alloc :=
  have := hP.sp_ge; have := hP.va.used_le; have := hP.va.alloc_lt; have := hP.sc.alloc_lt
  have := hP.room
  have hrs := hP.rs
  { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    rc := by simpa [Layout.sizeofMpInt] using hP.gc.st
    rs := ⟨by have := hrs.lo_ge; omega, by have := hrs.hi_le; omega, by have := hrs.off; omega⟩
    sp_al := hP.sp_al, sp_ge := by omega
    ua_v := by simpa [Layout.offUsed] using hP.ra_.used
    al_v := by simpa [Layout.offAlloc] using hP.rc.alloc
    ua_lt := by omega, al_lt := by omega, room := by omega
    code_s := disj_or (hP.lay.sub (r := R.stk) (s := R.code) (I := ⟨sp - 64, 64⟩)
      (by simp only [Iv.Sub, Two.lay]; omega) code_sub) |>.elim (fun h => Or.inl (by omega)) Or.inr }

theorem hfacts (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    HFacts (m1Of m ra s0 sp) pa pc a.sign a.used c.used adp cdp :=
  have hro := ro1 (s0 := s0) hP hF
  have hc := rc1 (s0 := s0) hP hF
  have := hP.va.used_le; have := hP.va.alloc_lt; have := hP.sc.alloc_lt; have := hP.sc.used_le
  have hsg := hP.va.sign_ok
  { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    rc := by simpa [Layout.sizeofMpInt] using hP.gc.st
    pc_al := hP.gc.st_al
    sa_v := by simpa [Layout.offSign] using hro.ra_.sign
    ua_v := by simpa [Layout.offUsed] using hro.ra_.used
    ou_v := by simpa [Layout.offUsed] using hc.used
    adp_v := by simpa [Layout.offDp] using hro.ra_.dpv
    cdp_v := by simpa [Layout.offDp] using hc.dpv
    sa_lt := by simp only [Layout.mpZpos, Layout.mpNeg] at hsg; omega
    ua_lt := by omega, ou_lt := by omega
    code_c := disj_or (hP.lay.sub (r := R.bS) (s := R.code) (Iv.sub_self _) code_sub) }

theorem cfacts (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) : CFacts pc :=
  { rc := by simpa [Layout.sizeofMpInt] using hP.gc.st
    pc_al := hP.gc.st_al
    code_c := disj_or (hP.lay.sub (r := R.bS) (s := R.code) (Iv.sub_self _) code_sub) }

theorem dfacts (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) : DFacts cdp :=
  have hrc : Ram cdp (4 * c.alloc) := by simpa [Layout.sizeofDigit] using hP.gc.ds
  have := hP.room
  { rd := ⟨by have := hrc.lo_ge; omega, by have := hrc.hi_le; omega, by have := hrc.off; omega⟩
    d_al := hP.gc.ds_al
    code_d := disj_or (hP.lay.sub (r := R.bD) (s := R.code) (I := ⟨cdp, 4⟩)
      ⟨by simp [Two.lay], by simp only [Two.lay]; omega⟩ code_sub) }

theorem xfacts (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) {M : Mem} (hro : RO M pa adp a)
    (h1 : 1 ≤ a.used) : XFacts M adp (a.digit 0) :=
  have hra : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have := hP.va.used_le
  { rx := ⟨by have := hra.lo_ge; omega, by have := hra.hi_le; omega, by have := hra.off; omega⟩
    x_v := by simpa [Layout.sizeofDigit] using hro.ra_.digits 0 (by omega)
    x_lt := by have := hP.va.digit_lt 0; rwa [radix_eq] at this }

/-! ## The tail -/

/-- `mp_clamp(c)` and the epilogue: the branch's result. -/
theorem finish (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) {n s : Nat} {dig : Nat → Nat}
    (hlt : ∀ i, dig i < radix) (hhi : ∀ i, n ≤ i → dig i = 0) (hn : n ≤ c.alloc) :
    Triple (TSt F m v outp sp pa adp pc cdp a c ra s0 0x80006514#64 (mL sp pc) n s dig)
      (RetD F m v outp sp pa adp pc cdp a c ra s0 dig n s) := by
  intro cf ⟨M, hT, hat⟩
  have := hP.sp_ge; have hal := hP.sc.alloc_lt
  have hro := RO.of hP hT.fr
  have hd := dMid_digit (c := c) (s := s) hhi hn
  have hcp : Clamp.Pre M pc cdp (dMid c dig n s) :=
    { repr := HdrAt.mpAt hT.hdr (hT.arr.congr fun j _ => by rw [hd])
      shape := dMid_shape hlt hhi hn hal
      geom := hP.gc, code := hro.img.mpClamp
      code_off := disj_or (hP.lay.sub (r := R.bS) (s := R.code) (Iv.sub_self _) clamp_sub) }
  refine Triple.seq (d_step v outp sp pc M hro.img.mpSubD)
    (Triple.seq (clamp_call v outp sp pc cdp _ M hro.img.mpSubD hcp) ?_) cf hat
  intro cf ⟨c', M', hat', hpost⟩
  have hcl : Frm ρ [R.bS] M M' := Frm.call (w := R.bS) hpost.frame (Iv.sub_pre (by decide))
  have hF' := Frm.step hT.fr hcl
  have hsv := hT.sv.keep hP.lay (by omega) hP.sp_ge hcl
  have hrs := hP.rs
  have hrf : RFacts M' ra s0 sp :=
    { rs := ⟨by have := hrs.lo_ge; omega, by have := hrs.hi_le; omega, by have := hrs.off; omega⟩
      sp_al := hP.sp_al, sp_ge := by omega
      ra_v := hsv.ra_v, s0_v := hsv.s0_v, ra_al := hP.ra_al }
  exact Triple.rmap (fun cf h => ⟨c', _, h, hpost.repr, DRes.of_clamp hhi hn hpost.clamp, hF'⟩)
    (r_step ra s0 v outp sp M' (RO.of hP hF').img.mpSubD hrf) cf hat'

theorem fin_eq {n : Nat} {dig : Nat → Nat} (hc : c.Shape) (hhi : ∀ i, n ≤ i → dig i = 0) {k : Nat}
    (hk : n ≤ k) (hk' : c.used ≤ k) : ∀ j, j < c.alloc → ovl dig c.digit k j = dig j := fun j _ => by
  simp only [ovl]
  split
  · rfl
  · rw [hc.high_zero j (by omega), hhi j (by omega)]

/-- `oldused ≤ n`: the digits from `n` on are zero already. -/
theorem zero0 (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) {n s : Nat} {dig : Nat → Nat}
    (hhi : ∀ i, n ≤ i → dig i = 0) (hou : c.used ≤ n) :
    Triple (TSt F m v outp sp pa adp pc cdp a c ra s0 0x80006514#64 (jL ra sp pc) n s (ovl dig c.digit n))
      (TSt F m v outp sp pa adp pc cdp a c ra s0 0x80006514#64 (mL sp pc) n s dig) :=
  Triple.rmap (fun _ ⟨M, hT, hat⟩ => ⟨M, hT.congr (fin_eq hP.sc hhi (Nat.le_refl _) hou),
    hat.weaken (by simp [jL, mL])⟩) Triple.rfl

/-- `oldused > n`: `memset` the digits `[n, oldused)`. -/
theorem zero1 (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) {n s : Nat} {dig : Nat → Nat}
    (hhi : ∀ i, n ≤ i → dig i = 0) (hou : n < c.used) :
    Triple (TSt F m v outp sp pa adp pc cdp a c ra s0 0x80006510#64 (msL ra sp pc cdp n c.used) n s
        (ovl dig c.digit n))
      (TSt F m v outp sp pa adp pc cdp a c ra s0 0x80006514#64 (mL sp pc) n s dig) := by
  intro cf ⟨M, hT, hat⟩
  have hbu := hP.sc.used_le
  have hro := RO.of hP hT.fr
  refine Triple.rmap (fun cf ⟨M', hat', hpost⟩ => ⟨M', ?_, hat'⟩)
    (memset_call ra v outp sp pc cdp n c.used M hro.img.mpSubD
      (Two.memset_pre hP.lay hP.gc hro.img (by omega) hbu)) cf hat
  exact (hT.fill hP.lay (by omega) hP.sp_ge (by omega) hbu hpost fun j h1 _ => hhi j h1).congr
    (fin_eq hP.sc hhi (by omega) (Nat.le_refl _))

/-! ## The small branches -/

/-- Drop an empty write log from a segment's post. -/
theorem nil_post {P : Vsa.Machine.Config → Prop} {pc0 : BitVec 64} {L K : GRegs} {M : Mem} {o : Array String}
    (h : Triple P (At pc0 L (writeLog M []) K o)) : Triple P (At pc0 L M K o) :=
  Triple.rmap (fun _ h => by rwa [writeLog_nil] at h) h

theorem small_tail (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) (d : Nat)
    (hd : d < 2 ^ 32) (hdd : d = smallDigits a b 0) :
    Tail2 ρ m (writeLog (m1Of m ra s0 sp) (smallLog pc cdp d)) ra s0 sp pc cdp 1 c.alloc 1
      (ovl (smallDigits a b) c.digit 1) := by
  have := hP.sp_ge; have := hP.room
  have hc1 := rc1 (s0 := s0) hP hF
  have hA0 : ArrFrm ρ R.bD (m1Of m ra s0 sp) (m1Of m ra s0 sp) cdp c.alloc (ovl (smallDigits a b) c.digit 0) :=
    ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; exact hc1.arr)
  have hA := hA0.step (i := 0) (v := d) (by omega) hd hdd
  rw [show cdp + 4 * 0 = cdp by omega] at hA
  have hS2 : Frm ρ [R.bS] (writeLog (m1Of m ra s0 sp) [(cdp, 4, BitVec.ofNat 64 d)])
      (writeLog (writeLog (m1Of m ra s0 sp) [(cdp, 4, BitVec.ofNat 64 d)])
        [(pc + 8, 4, BitVec.ofNat 64 1), (pc, 4, BitVec.ofNat 64 1)]) :=
    Frm.store (by simp only [LogIn, Iv.Sub, Two.lay, and_true]; omega)
  have e : writeLog (m1Of m ra s0 sp) (smallLog pc cdp d) = writeLog (writeLog (m1Of m ra s0 sp)
      [(cdp, 4, BitVec.ofNat 64 d)]) [(pc + 8, 4, BitVec.ofNat 64 1), (pc, 4, BitVec.ofNat 64 1)] :=
    writeLog_append _ [(cdp, 4, BitVec.ofNat 64 d)] _
  have e2 : ∀ X : Mem, writeLog X [(pc + 8, 4, BitVec.ofNat 64 1), (pc, 4, BitVec.ofNat 64 1)] =
      writeLog (writeLog X [(pc + 8, 4, BitVec.ofNat 64 1)]) [(pc, 4, BitVec.ofNat 64 1)] := fun X =>
    writeLog_append X [(pc + 8, 4, BitVec.ofNat 64 1)] [(pc, 4, BitVec.ofNat 64 1)]
  have hal := hP.sc.alloc_lt
  rw [e]
  exact { fr := ((f1 hP hF).trans (hA.fr.trans hS2)).mono
          sv := ((sv1 hP hF).keep hP.lay (by omega) hP.sp_ge hA.fr).keep hP.lay (by omega) hP.sp_ge hS2
          hdr := by
            rw [e2]
            exact ((hA.fr.keep hP.lay (HdrAt.reads (r := R.bS) (Iv.sub_self _)) hc1.hdr).set_sign 1
              (by decide)).set_used 1 (by decide)
          arr := hS2.keep hP.lay (ArrAt.reads (r := R.bD) (Iv.sub_self _)) hA.arr }

theorem smallDigits_high' (b : Nat) : ∀ i, 1 ≤ i → smallDigits a b i = 0 := smallDigits_high a b

/-- The small branches (`0 ≤ a ≤ b`): `c := -(b - a)`. -/
theorem small (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) (hs : a.sign = 0)
    (hsm : SubDSmall a b) :
    Triple (At 0x800064c8#64 (pL ra sp pa b pc a.used) (m1Of m ra s0 sp) v.keepR outp)
      (RetD F m v outp sp pa adp pc cdp a c ra s0 (smallDigits a b) 1 1) := by
  have hb := hP.hb; rw [radix_eq] at hb
  have hcu := hP.sc.used_le; have hcl := hP.sc.alloc_lt; have := hP.room
  have hrc : Ram cdp (4 * c.alloc) := by simpa [Layout.sizeofDigit] using hP.gc.ds
  have hfin := finish (v := v) (outp := outp) (s0 := s0) hP hF (n := 1) (s := 1) (smallDigits_lt hP.hb)
    (smallDigits_high a b) (by omega)
  have hH := hfacts (s0 := s0) hP hF
  rw [hs] at hH
  rcases hsm with ⟨h1, hxb⟩ | h0
  · rw [h1] at hH ⊢
    have hx := xfacts hP (ro1 (s0 := s0) hP hF) (by omega)
    have hd : b - a.digit 0 = smallDigits a b 0 := by simp [smallDigits]
    refine Triple.seq (nil_post (s1_step ra v outp sp pa b pc c.used adp cdp _ _ (ro1 hP hF).img.mpSubD hH hx hb hxb)) ?_
    by_cases hou : c.used ≤ 1
    · exact Triple.seq (Triple.rmap (fun cf h => ⟨_, small_tail hP hF _ (by omega) hd, h⟩)
        (s1a_step ra v outp sp b pc c.used cdp _ (m1Of m ra s0 sp) (ro1 hP hF).img.mpSubD (cfacts hP) (dfacts hP) hb hxb hou))
        (Triple.seq (zero0 hP (smallDigits_high a b) hou) hfin)
    · exact Triple.seq (Triple.rmap (fun cf h => ⟨_, small_tail hP hF _ (by omega) hd, h⟩)
        (s1b_step ra v outp sp b pc c.used cdp _ (m1Of m ra s0 sp) (ro1 hP hF).img.mpSubD (cfacts hP) (dfacts hP) hb hxb
          (by omega) (by omega) (by have := hrc.hi_le; omega)))
        (Triple.seq (zero1 hP hF (smallDigits_high a b) (by omega)) hfin)
  · rw [h0] at hH ⊢
    have hd : b = smallDigits a b 0 := by simp [smallDigits, hP.va.high_zero 0 (by omega)]
    refine Triple.seq (nil_post (s0_step ra v outp sp pa b pc c.used adp cdp _ (ro1 hP hF).img.mpSubD hH
      (by have := hrc.hi_le; omega))) ?_
    by_cases hou : c.used ≤ 1
    · exact Triple.seq (Triple.rmap (fun cf h => ⟨_, small_tail hP hF _ (by omega) hd, h⟩)
        (s0a_step ra v outp sp b pc c.used cdp (m1Of m ra s0 sp) (ro1 hP hF).img.mpSubD (cfacts hP) (dfacts hP) (by omega) hou))
        (Triple.seq (zero0 hP (smallDigits_high a b) hou) hfin)
    · exact Triple.seq (Triple.rmap (fun cf h => ⟨_, small_tail hP hF _ (by omega) hd, h⟩)
        (s0b_step ra v outp sp b pc c.used cdp (m1Of m ra s0 sp) (ro1 hP hF).img.mpSubD (cfacts hP) (dfacts hP) (by omega)
          (by omega) (by omega) (by have := hrc.hi_le; omega)))
        (Triple.seq (zero1 hP hF (smallDigits_high a b) (by omega)) hfin)

/-! ## The big branch -/

theorem snap2 (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    Snap2 ρ m (m2Of m ra s0 sp pc a.used) ra s0 sp pc cdp a.used c.alloc 0 c.digit := by
  have := hP.sp_ge; have := hP.va.used_le; have := hP.va.alloc_lt
  have hc1 := rc1 (s0 := s0) hP hF
  have hS : Frm ρ [R.bS] (m1Of m ra s0 sp) (m2Of m ra s0 sp pc a.used) :=
    Frm.store (by simp only [LogIn, Iv.Sub, Two.lay, and_true]; omega)
  have e : writeLog (m1Of m ra s0 sp) [(pc, 4, BitVec.ofNat 64 a.used), (pc + 8, 4, 0#64)] =
      writeLog (writeLog (m1Of m ra s0 sp) [(pc, 4, BitVec.ofNat 64 a.used)]) [(pc + 8, 4, 0#64)] :=
    writeLog_append _ [(pc, 4, BitVec.ofNat 64 a.used)] _
  exact { fr := (f1 hP hF).trans hS
          sv := (sv1 hP hF).keep hP.lay (by omega) hP.sp_ge hS
          hdr := by
            unfold m2Of; rw [e]
            exact (hc1.hdr.set_used _ (by omega)).set_sign 0 (by decide)
          arr := hS.keep hP.lay (ArrAt.reads (r := R.bD) (Iv.sub_self _)) hc1.arr }

/-- The big branch's join points: `c`'s digits hold `f`, nothing else changed since `m2Of`. -/
abbrev St (F : Nat) (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a c : MpInt)
    (ra s0 : BitVec 64) :=
  ASt (Two.lay F sp pa adp pc cdp a c) R.bD (m2Of m ra s0 sp pc a.used) cdp c.alloc v.keepR outp

theorem ro2 (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) {M : Mem} {f : Nat → Nat}
    (hI : ArrFrm ρ R.bD (m2Of m ra s0 sp pc a.used) M cdp c.alloc f) : RO M pa adp a :=
  RO.of hP (((snap2 (s0 := s0) hP hF).fr.trans hI.fr).mono)

theorem lfacts (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) {M : Mem} (hro : RO M pa adp a) {i : Nat}
    (hi : i < a.used) : LFacts M pa adp cdp a.used i (a.digit i) :=
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt; have hroom := hP.room
  have hra : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have hrc : Ram cdp (4 * c.alloc) := by simpa [Layout.sizeofDigit] using hP.gc.ds
  { rx := ⟨by have := hra.lo_ge; omega, by have := hra.hi_le; omega, by have := hra.off; omega⟩
    x_v := by simpa [Layout.sizeofDigit] using hro.ra_.digits i (by omega)
    x_lt := by have := hs.digit_lt i; rwa [radix_eq] at this
    ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    ua_v := by simpa [Layout.offUsed] using hro.ra_.used
    ua_lt := by omega
    rd := ⟨by have := hrc.lo_ge; omega, by have := hrc.hi_le; omega, by have := hrc.off; omega⟩
    d_al := hP.gc.ds_al
    ac := disj_or (hP.lay.sub (r := R.aS) (s := R.bD) (I := ⟨pa, 4⟩) (J := ⟨cdp + 4 * i, 4⟩)
      (Iv.sub_pre (by decide)) (Iv.sub_elem (by omega)))
    code_d := disj_or (hP.lay.sub (r := R.bD) (s := R.code) (Iv.sub_elem (by omega)) code_sub) }

theorem borrowD_eq {x u : Nat} (hx : x < 268435456) (hu : u < 268435456) :
    (x + 4294967296 - u) % 4294967296 / 2147483648 = if x < u then 1 else 0 := by
  split <;> omega

/-- One loop segment (back edge to `6558`, or an exit). -/
theorem l_seg (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) (i : Nat) (hi : i < a.used)
    (pc' : BitVec 64) (Lf : Nat → GRegs)
    (hseg : ∀ M, CodeAt M mpSubDBase mpSubDCode → LFacts M pa adp cdp a.used i (a.digit i) →
      Triple (At 0x80006558#64 (lL ra sp pa pc c.used adp cdp i (subDBorrow a b i)) M v.keepR outp)
      (At pc' (Lf ((a.digit i + 4294967296 - subDBorrow a b i) % 4294967296 / 2147483648))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64
          ((a.digit i + 268435456 - subDBorrow a b i) % 268435456))]) v.keepR outp)) :
    Triple (St F m v outp sp pa adp pc cdp a c ra s0 0x80006558#64
        (lL ra sp pa pc c.used adp cdp i (subDBorrow a b i)) (ovl (subDDigits a b) c.digit i))
      (St F m v outp sp pa adp pc cdp a c ra s0 pc' (Lf (subDBorrow a b (i + 1)))
        (ovl (subDDigits a b) c.digit (i + 1))) := by
  have hs := hP.va.toShape
  have hua := hs.used_le; have hroom := hP.room
  refine ASt.store (v := (a.digit i + 268435456 - subDBorrow a b i) % 268435456) (fun M hI => ?_) (by omega)
    (by simp only [subDDigits, if_pos hi, radix_eq]) (by omega)
  have hro := ro2 (s0 := s0) hP hF hI
  have hl := lfacts hP hro hi
  have h := hseg M hro.img.mpSubD hl
  rwa [borrowD_eq hl.x_lt (by have := subDBorrow_le (a := a) hP.hb i; rwa [radix_eq] at this),
    ← subDBorrow_succ] at h

theorem loop (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) (h1 : 1 ≤ a.used)
    (pcE : BitVec 64) (LE : GRegs)
    (hlast : ∀ M, CodeAt M mpSubDBase mpSubDCode → LFacts M pa adp cdp a.used (a.used - 1) (a.digit (a.used - 1)) →
      Triple (At 0x80006558#64 (lL ra sp pa pc c.used adp cdp (a.used - 1) (subDBorrow a b (a.used - 1))) M v.keepR outp)
      (At pcE LE (writeLog M [(cdp + 4 * (a.used - 1), 4, BitVec.ofNat 64
          ((a.digit (a.used - 1) + 268435456 - subDBorrow a b (a.used - 1)) % 268435456))]) v.keepR outp)) :
    ∀ i, i < a.used → Triple (St F m v outp sp pa adp pc cdp a c ra s0 0x80006558#64
        (lL ra sp pa pc c.used adp cdp i (subDBorrow a b i)) (ovl (subDDigits a b) c.digit i))
      (St F m v outp sp pa adp pc cdp a c ra s0 pcE LE (ovl (subDDigits a b) c.digit a.used)) := by
  have hb := hP.hb
  refine Triple.countup (fun i hi => l_seg hP hF i (by omega) _ (fun u => lL ra sp pa pc c.used adp cdp (i + 1) u)
    fun M hc hf => l_step ra v outp sp pa pc c.used adp cdp a.used i _ _ M hc hf
      (by have := subDBorrow_le (a := a) hb i; rwa [radix_eq] at this) hi) ?_
  have h := l_seg (s0 := s0) (v := v) (outp := outp) hP hF (a.used - 1) (by omega) pcE (fun _ => LE) hlast
  rw [show a.used - 1 + 1 = a.used by omega] at h
  exact h

/-- The big branch (`a > b ≥ 0`): `c := a - b`. -/
theorem big (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) (hs : a.sign = 0)
    (hnsm : ¬ SubDSmall a b) :
    Triple (At 0x800064c8#64 (pL ra sp pa b pc a.used) (m1Of m ra s0 sp) v.keepR outp)
      (RetD F m v outp sp pa adp pc cdp a c ra s0 (subDDigits a b) a.used 0) := by
  have hb := hP.hb; rw [radix_eq] at hb
  have hcu := hP.sc.used_le; have hcl := hP.sc.alloc_lt; have hroom := hP.room
  have hua := hP.va.used_le; have hal := hP.va.alloc_lt
  have hrc : Ram cdp (4 * c.alloc) := by simpa [Layout.sizeofDigit] using hP.gc.ds
  have hH := hfacts (s0 := s0) hP hF
  rw [hs] at hH
  have h1 : 1 ≤ a.used := by
    rcases Nat.eq_zero_or_pos a.used with h | h
    · exact absurd (Or.inr h) hnsm
    · exact h
  have hfin := finish (v := v) (outp := outp) (s0 := s0) hP hF (n := a.used) (s := 0) (subDDigits_lt a b)
    (subDDigits_high a b) (by omega)
  -- to `653c`
  have hpre : Triple (At 0x800064c8#64 (pL ra sp pa b pc a.used) (m1Of m ra s0 sp) v.keepR outp)
      (At 0x8000653c#64 (bL ra sp pa b pc a.used c.used adp cdp) (m1Of m ra s0 sp) v.keepR outp) := by
    by_cases h2 : 2 ≤ a.used
    · exact nil_post (b2_step ra v outp sp pa b pc a.used c.used adp cdp _ (ro1 hP hF).img.mpSubD hH h2)
    · have hu1 : a.used = 1 := by omega
      have hx := xfacts hP (ro1 (s0 := s0) hP hF) h1
      have hxb : b < a.digit 0 := Nat.lt_of_not_le fun h => hnsm (Or.inl ⟨hu1, h⟩)
      rw [hu1] at hH ⊢
      exact nil_post (b1_step ra v outp sp pa b pc c.used adp cdp _ _ (ro1 hP hF).img.mpSubD hH hx hb hxb)
  have hbf : BFacts (m1Of m ra s0 sp) pa pc a.used :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rc := by simpa [Layout.sizeofMpInt] using hP.gc.st
      pc_al := hP.gc.st_al
      ua_v := by simpa [Layout.offUsed] using (ro1 (s0 := s0) hP hF).ra_.used
      ua_lt := by omega
      ac := disj_or (hP.lay.sub (r := R.aS) (s := R.bS) (I := ⟨pa, 4⟩) (J := ⟨pc, 4⟩)
        (Iv.sub_pre (by decide)) (Iv.sub_pre (by decide)))
      code_c := (cfacts hP).code_c }
  have hsn := snap2 (s0 := s0) hP hF
  have hI0 : ArrFrm ρ R.bD (m2Of m ra s0 sp pc a.used) (m2Of m ra s0 sp pc a.used) cdp c.alloc
      (ovl (subDDigits a b) c.digit 0) := ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; exact hsn.arr)
  refine Triple.seq hpre (Triple.seq (Triple.rmap (fun cf h => (⟨_, hI0, h⟩ : St F m v outp sp pa adp pc cdp a c
      ra s0 0x80006558#64 (lL ra sp pa pc c.used adp cdp 0 (subDBorrow a b 0)) (ovl (subDDigits a b) c.digit 0) cf))
    (bb_step ra v outp sp pa b pc a.used c.used adp cdp _ (ro1 hP hF).img.mpSubD hbf h1)) ?_)
  by_cases hou : c.used ≤ a.used
  · refine Triple.seq (Triple.rmap (fun cf ⟨M, hI, hat⟩ => ⟨M, hsn.tail hP.lay (by omega) hP.sp_ge hI, hat⟩)
      (loop hP hF h1 _ _ (fun M hc hf => la_step ra v outp sp pa pc c.used adp cdp a.used (a.used - 1) _ _ M hc hf
        (by have := subDBorrow_le (a := a) hP.hb (a.used - 1); rwa [radix_eq] at this) (by omega) hou
        (by omega)) 0 (by omega)))
      (Triple.seq (zero0 hP (subDDigits_high a b) hou) hfin)
  · refine Triple.seq (Triple.rmap (fun cf ⟨M, hI, hat⟩ => ⟨M, hsn.tail hP.lay (by omega) hP.sp_ge hI, hat⟩)
      (loop hP hF h1 _ _ (fun M hc hf => lb_step ra v outp sp pa pc c.used adp cdp a.used (a.used - 1) _ _ M hc hf
        (by have := subDBorrow_le (a := a) hP.hb (a.used - 1); rwa [radix_eq] at this) (by omega) (by omega)
        (by omega) (by have := hrc.hi_le; omega)) 0 (by omega)))
      (Triple.seq (zero1 hP hF (subDDigits_high a b) (by omega)) hfin)

/-- **`mp_sub_d` for `a ≥ 0`** (no call of `mp_add_d`), any stack depth `F ≥ 64`. -/
theorem pos_correct (hF : 64 ≤ F) (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hs : a.sign = Layout.mpZpos) :
    Triple (At 0x800064a4#64 (entryL ra s0 sp pa b pc) m v.keepR outp)
      (Api.SubD.Ret F m v outp sp pa adp pc cdp a b c ra s0) := by
  refine Triple.seq (p_step ra s0 v outp sp pa b pc a.used c.alloc m hP.img.mpSubD (pfacts hP hF)) ?_
  have hneg : a.sign ≠ Layout.mpNeg := by rw [hs]; decide
  by_cases hsm : SubDSmall a b
  · exact Triple.rmap (fun cf ⟨c', M, hat, ho⟩ => ⟨c', M, hat, ho.repr,
      ⟨fun h => absurd h hneg, fun _ _ => ho.res, fun _ h => absurd hsm h⟩, ho.frame⟩) (small hP hF hs hsm)
  · exact Triple.rmap (fun cf ⟨c', M, hat, ho⟩ => ⟨c', M, hat, ho.repr,
      ⟨fun h => absurd h hneg, fun _ h => absurd h hsm, fun _ _ => ho.res⟩, ho.frame⟩) (big hP hF hs hsm)

end

end Tom.Machine.Fn.SubD
