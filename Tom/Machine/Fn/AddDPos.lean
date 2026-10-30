import Tom.Machine.Fn.AddD
import Tom.Machine.Api.AddD
import Tom.Machine.Kit.DTail

/-!
# `mp_add_d` on the machine: the non-recursive branches

`pos_correct`: from the entry with `a->sign = MP_ZPOS`, any stack depth
`F ≥ 64`, `mp_add_d` meets `Api.AddD.Post` (its `pos` field; `big` and
`small` are vacuous). It does not call `mp_sub_d`, so `mp_sub_d`'s negative
branch can use it (`Fn/SubDMain.lean`). `small`: the branch for `a < 0`,
`|a| < b` (no call either).

States, over `Two`'s regions with `c` the written operand (`bS`, `bD`):
after the prologue the memory `m1Of`, the snapshot of the loop (a
`Two.Snap2`; the loop changes only `c`'s digits); at `4ec4` a `Two.Tail2`
with `c->used` stored and `c->sign` still the old one. `tail` stores
`c->sign := MP_ZPOS`, zeroes the excess digits, calls `mp_clamp`, returns.
-/

namespace Tom.Machine.Fn.AddD

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api
open Tom.Machine.Api.Two (R isW ws Saved2 Tail2 Snap2)

theorem code_sub : Iv.Sub ⟨mpAddDBase, 424⟩ textIv := ⟨by decide, by decide⟩

theorem clamp_sub : Iv.Sub ⟨mpClampBase, 64⟩ textIv := ⟨by decide, by decide⟩

theorem disj_or {x n y k : Nat} (h : Iv.Disj ⟨x, n⟩ ⟨y, k⟩) : x + n ≤ y ∨ y + k ≤ x := h

/-- What stays as at the entry. -/
structure RO (M : Mem) (pa adp : Nat) (a : MpInt) : Prop where
  img : Img M
  ra_ : MpAt M pa adp a

/-- The memory after the prologue. -/
def m1Of (m : Mem) (ra s0 : BitVec 64) (sp : Nat) : Mem := writeLog m (frameLog ra s0 sp)

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

/-- Drop an empty write log from a segment's post. -/
theorem nil_post {P : Vsa.Machine.Config → Prop} {pc0 : BitVec 64} {L K : GRegs} {M : Mem} {o : Array String}
    (h : Triple P (At pc0 L (writeLog M []) K o)) : Triple P (At pc0 L M K o) :=
  Triple.rmap (fun _ h => by rwa [writeLog_nil] at h) h

section
variable {F : Nat} {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat}
  {c : MpInt} {ra s0 : BitVec 64}

local notation "ρ" => Two.lay F sp pa adp pc cdp a c

theorem RO.of (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) {M : Mem} (hF : Frm ρ ws m M) : RO M pa adp a :=
  { img := hF.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
    ra_ := hF.keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_ }

theorem f1 (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    Frm ρ [R.stk] m (m1Of m ra s0 sp) := by
  have := hP.sp_ge
  exact Frm.store (by simp only [LogIn, frameLog, Iv.Sub, Two.lay, and_true]; omega)

theorem sv1 (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    Saved2 (m1Of m ra s0 sp) ra s0 sp :=
  have := hP.sp_ge
  { ra_v := bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog, OutLRange])
    s0_v := bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog, OutLRange]; omega) }

theorem rc1 (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    MpAt (m1Of m ra s0 sp) pc cdp c :=
  (f1 hP hF).keep hP.lay (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hP.rc

theorem ro1 (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    RO (m1Of m ra s0 sp) pa adp a := RO.of hP (f1 hP hF).mono

/-- The snapshot of the loop: the memory after the prologue. -/
theorem snap1 (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    Snap2 ρ m (m1Of m ra s0 sp) ra s0 sp pc cdp c.used c.alloc c.sign c.digit :=
  { fr := (f1 hP hF).mono, sv := sv1 hP hF, hdr := (rc1 hP hF).hdr, arr := (rc1 hP hF).arr }

theorem pfacts (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
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

theorem hfacts (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    HFacts (m1Of m ra s0 sp) pa pc a.sign a.used c.used adp cdp :=
  have hro := ro1 (s0 := s0) hP hF
  have hc := rc1 (s0 := s0) hP hF
  have := hP.va.used_le; have := hP.va.alloc_lt; have := hP.sc.alloc_lt; have := hP.sc.used_le
  have hsg := hP.va.sign_ok
  { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    rc := by simpa [Layout.sizeofMpInt] using hP.gc.st
    sa_v := by simpa [Layout.offSign] using hro.ra_.sign
    ua_v := by simpa [Layout.offUsed] using hro.ra_.used
    ou_v := by simpa [Layout.offUsed] using hc.used
    adp_v := by simpa [Layout.offDp] using hro.ra_.dpv
    cdp_v := by simpa [Layout.offDp] using hc.dpv
    sa_lt := by simp only [Layout.mpZpos, Layout.mpNeg] at hsg; omega
    ua_lt := by omega, ou_lt := by omega }

theorem xfacts (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) {M : Mem} (hro : RO M pa adp a)
    (h1 : 1 ≤ a.used) : XFacts M adp (a.digit 0) :=
  have hra : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have := hP.va.used_le
  { rx := ⟨by have := hra.lo_ge; omega, by have := hra.hi_le; omega, by have := hra.off; omega⟩
    x_v := by simpa [Layout.sizeofDigit] using hro.ra_.digits 0 (by omega)
    x_lt := by have := hP.va.digit_lt 0; rwa [radix_eq] at this }

theorem code_c (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) :
    pc + 24 ≤ mpAddDBase ∨ mpAddDBase + 424 ≤ pc :=
  disj_or (hP.lay.sub (r := R.bS) (s := R.code) (Iv.sub_self _) code_sub)

/-! ## The tail -/

theorem fin_eq {n : Nat} {dig : Nat → Nat} (hc : c.Shape) (hhi : ∀ i, n ≤ i → dig i = 0) {k : Nat}
    (hk : n ≤ k) (hk' : c.used ≤ k) : ∀ j, j < c.alloc → ovl dig c.digit k j = dig j := fun j _ => by
  simp only [ovl]
  split
  · rfl
  · rw [hc.high_zero j (by omega), hhi j (by omega)]

/-- From `4ec4`: `c->sign := MP_ZPOS`, zero the excess digits, `mp_clamp(c)`, return. -/
theorem tail (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) {n : Nat} {dig : Nat → Nat}
    (hlt : ∀ i, dig i < radix) (hhi : ∀ i, n ≤ i → dig i = 0) (hn : n ≤ c.alloc) :
    Triple (TSt F m v outp sp pa adp pc cdp a c ra s0 0x80004ec4#64 (tL ra sp pc c.used cdp n) n c.sign
        (ovl dig c.digit n))
      (RetD F m v outp sp pa adp pc cdp a c ra s0 dig n 0) := by
  have := hP.sp_ge; have hal := hP.sc.alloc_lt; have hbu := hP.sc.used_le
  have hrc : Ram cdp (4 * c.alloc) := by simpa [Layout.sizeofDigit] using hP.gc.ds
  have hrs : Ram pc 24 := by simpa [Layout.sizeofMpInt] using hP.gc.st
  -- after the sign store and the zeroing, at `4edc`
  have hfin : Triple (TSt F m v outp sp pa adp pc cdp a c ra s0 0x80004edc#64 (mL sp pc) n 0 dig)
      (RetD F m v outp sp pa adp pc cdp a c ra s0 dig n 0) := by
    intro cf ⟨M, hT, hat⟩
    have hro := RO.of hP hT.fr
    have hd := dMid_digit (c := c) (s := 0) hhi hn
    have hcp : Clamp.Pre M pc cdp (dMid c dig n 0) :=
      { repr := HdrAt.mpAt hT.hdr (hT.arr.congr fun j _ => by rw [hd])
        shape := dMid_shape hlt hhi hn hal
        geom := hP.gc, code := hro.img.mpClamp
        code_off := disj_or (hP.lay.sub (r := R.bS) (s := R.code) (Iv.sub_self _) clamp_sub) }
    refine Triple.seq (d_step v outp sp pc M hro.img.mpAddD)
      (Triple.seq (clamp_call1 v outp sp pc cdp _ M hro.img.mpAddD hcp) ?_) cf hat
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
      (r_step ra s0 v outp sp M' (RO.of hP hF').img.mpAddD hrf) cf hat'
  intro cf ⟨M, hT, hat⟩
  have hro := RO.of hP hT.fr
  have hsw : Frm ρ [R.bS] M (writeLog M [(pc + 8, 4, 0#64)]) := Frm.sw (by simp only [Iv.Sub, Two.lay]; omega)
  have hT' : Tail2 ρ m (writeLog M [(pc + 8, 4, 0#64)]) ra s0 sp pc cdp n c.alloc 0 (ovl dig c.digit n) :=
    { fr := Frm.step hT.fr hsw
      sv := hT.sv.keep hP.lay (by omega) hP.sp_ge hsw
      hdr := hT.hdr.set_sign 0 (by decide)
      arr := hsw.keep hP.lay (ArrAt.reads (r := R.bD) (Iv.sub_self _)) hT.arr }
  by_cases hou : c.used ≤ n
  · exact Triple.seq (Triple.rmap (fun cf h => ⟨_, hT'.congr (fin_eq hP.sc hhi (Nat.le_refl _) hou), h⟩)
      (t0_step ra v outp sp pc c.used cdp n M hro.img.mpAddD hrs hP.gc.st_al (code_c hP) (by omega) hou)) hfin cf hat
  · have hro' := RO.of hP hT'.fr
    refine Triple.seq (t1_step ra v outp sp pc c.used cdp n M hro.img.mpAddD hrs hP.gc.st_al (code_c hP)
        (by omega) (by omega) (by have := hrc.hi_le; omega))
      (Triple.seq (Triple.rmap (fun cf ⟨M', hat', hpost⟩ => ⟨M', (hT'.fill hP.lay (by omega) hP.sp_ge
          (by omega) hbu hpost fun j h1 _ => hhi j h1).congr (fin_eq hP.sc hhi (by omega) (Nat.le_refl _)), hat'⟩)
        (memset_call ra v outp sp pc cdp n c.used _ hro'.img.mpAddD
          (Two.memset_pre hP.lay hP.gc hro'.img (by omega) hbu))) hfin) cf hat

/-! ## `a ≥ 0` -/

/-- The loop's join points: `c`'s digits hold `f`, nothing else changed since `m1Of`. -/
abbrev St (F : Nat) (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pc cdp : Nat) (a c : MpInt)
    (ra s0 : BitVec 64) :=
  ASt (Two.lay F sp pa adp pc cdp a c) R.bD (m1Of m ra s0 sp) cdp c.alloc v.keepR outp

theorem ro2 (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) {M : Mem} {f : Nat → Nat}
    (hI : ArrFrm ρ R.bD (m1Of m ra s0 sp) M cdp c.alloc f) : RO M pa adp a :=
  RO.of hP (((snap1 (s0 := s0) hP hF).fr.trans hI.fr).mono)

theorem lfacts (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) {M : Mem} (hro : RO M pa adp a) {i : Nat}
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

/-- One loop segment (back edge to `4e80`, or the exit at `4eb0`). -/
theorem l_seg (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) (i : Nat) (hi : i < a.used)
    (pc' : BitVec 64) (Lf : Nat → GRegs)
    (hseg : ∀ M, CodeAt M mpAddDBase mpAddDCode → LFacts M pa adp cdp a.used i (a.digit i) →
      Triple (At 0x80004e80#64 (lL ra sp pa pc c.used adp cdp i (addDCarry a b i)) M v.keepR outp)
      (At pc' (Lf ((a.digit i + addDCarry a b i) / 268435456))
        (writeLog M [(cdp + 4 * i, 4, BitVec.ofNat 64 ((a.digit i + addDCarry a b i) % 268435456))])
        v.keepR outp)) :
    Triple (St F m v outp sp pa adp pc cdp a c ra s0 0x80004e80#64
        (lL ra sp pa pc c.used adp cdp i (addDCarry a b i)) (ovl (addDDigits a b) c.digit i))
      (St F m v outp sp pa adp pc cdp a c ra s0 pc' (Lf (addDCarry a b (i + 1)))
        (ovl (addDDigits a b) c.digit (i + 1))) := by
  have hs := hP.va.toShape
  have hua := hs.used_le; have hroom := hP.room
  refine ASt.store (v := (a.digit i + addDCarry a b i) % 268435456) (fun M hI => ?_) (by omega)
    (by simp only [addDDigits, if_pos hi, radix_eq]) (by omega)
  have hro := ro2 (s0 := s0) hP hF hI
  have h := hseg M hro.img.mpAddD (lfacts hP hro hi)
  rwa [show (a.digit i + addDCarry a b i) / 268435456 = addDCarry a b (i + 1) by
    rw [addDCarry_succ, radix_eq]] at h

theorem loop (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) (h1 : 1 ≤ a.used) :
    ∀ i, i < a.used → Triple (St F m v outp sp pa adp pc cdp a c ra s0 0x80004e80#64
        (lL ra sp pa pc c.used adp cdp i (addDCarry a b i)) (ovl (addDDigits a b) c.digit i))
      (St F m v outp sp pa adp pc cdp a c ra s0 0x80004eb0#64
        (jL ra sp pa pc c.used cdp a.used (addDCarry a b a.used)) (ovl (addDDigits a b) c.digit a.used)) := by
  have hs := hP.va.toShape
  have hc : ∀ i, addDCarry a b i < 268435456 := fun i => by
    have := addDCarry_lt hs hP.hb i; rwa [radix_eq] at this
  refine Triple.countup (fun i hi => l_seg hP hF i (by omega) _ (fun u => lL ra sp pa pc c.used adp cdp (i + 1) u)
    fun M hcd hf => l_step ra v outp sp pa pc c.used adp cdp a.used i _ _ M hcd hf (hc i) hi) ?_
  have h := l_seg (s0 := s0) (v := v) (outp := outp) hP hF (a.used - 1) (by omega) _
    (fun u => jL ra sp pa pc c.used cdp a.used u)
    fun M hcd hf => le_step ra v outp sp pa pc c.used adp cdp a.used (a.used - 1) _ _ M hcd hf (hc _) (by omega)
  rw [show a.used - 1 + 1 = a.used by omega] at h
  exact h

theorem cfacts (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) {M : Mem} (hro : RO M pa adp a) :
    CFacts M pa pc cdp a.used :=
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt; have hroom := hP.room; have := hP.sc.alloc_lt
  have hrc : Ram cdp (4 * c.alloc) := by simpa [Layout.sizeofDigit] using hP.gc.ds
  { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    rc := by simpa [Layout.sizeofMpInt] using hP.gc.st
    pc_al := hP.gc.st_al
    ua_v := by simpa [Layout.offUsed] using hro.ra_.used
    ua_lt := by omega
    rd := ⟨by have := hrc.lo_ge; omega, by have := hrc.hi_le; omega, by have := hrc.off; omega⟩
    d_al := hP.gc.ds_al
    ac := disj_or (hP.lay.sub (r := R.aS) (s := R.bD) (I := ⟨pa, 4⟩) (J := ⟨cdp + 4 * a.used, 4⟩)
      (Iv.sub_pre (by decide)) (Iv.sub_elem (by omega)))
    code_c := code_c hP
    code_d := disj_or (hP.lay.sub (r := R.bD) (s := R.code) (Iv.sub_elem (by omega)) code_sub) }

/-- At `4eb0`, then the carry digit and `c->used := a->used + 1`: a `Tail2` at `4ec4`. -/
theorem carry (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    Triple (St F m v outp sp pa adp pc cdp a c ra s0 0x80004eb0#64
        (jL ra sp pa pc c.used cdp a.used (addDCarry a b a.used)) (ovl (addDDigits a b) c.digit a.used))
      (TSt F m v outp sp pa adp pc cdp a c ra s0 0x80004ec4#64 (tL ra sp pc c.used cdp (a.used + 1))
        (a.used + 1) c.sign (ovl (addDDigits a b) c.digit (a.used + 1))) := by
  intro cf ⟨M, hI, hat⟩
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt; have hroom := hP.room
  have hcl := addDCarry_lt hs hP.hb a.used
  rw [radix_eq] at hcl
  have hro := ro2 (s0 := s0) hP hF hI
  have hI' := hI.step (i := a.used) (v := addDCarry a b a.used) (by omega) (by omega)
    (by simp [addDDigits])
  have hsw : Frm ρ [R.bS] (writeLog M [(cdp + 4 * a.used, 4, BitVec.ofNat 64 (addDCarry a b a.used))])
      (writeLog (writeLog M [(cdp + 4 * a.used, 4, BitVec.ofNat 64 (addDCarry a b a.used))])
        [(pc, 4, BitVec.ofNat 64 (a.used + 1))]) := Frm.sw (Iv.sub_pre (by decide))
  have hT := (snap1 (s0 := s0) hP hF).tail hP.lay (by omega) hP.sp_ge hI'
  have e : writeLog M [(cdp + 4 * a.used, 4, BitVec.ofNat 64 (addDCarry a b a.used)),
      (pc, 4, BitVec.ofNat 64 (a.used + 1))] = writeLog (writeLog M [(cdp + 4 * a.used, 4,
        BitVec.ofNat 64 (addDCarry a b a.used))]) [(pc, 4, BitVec.ofNat 64 (a.used + 1))] :=
    writeLog_append M [(cdp + 4 * a.used, 4, BitVec.ofNat 64 (addDCarry a b a.used))] _
  have h := c_step ra v outp sp pa pc c.used cdp a.used _ M hro.img.mpAddD (cfacts hP hro) (by omega) cf hat
  rw [e] at h
  obtain ⟨cf', hst, hat'⟩ := h
  refine ⟨cf', hst, _, ?_, hat'⟩
  exact { fr := Frm.step hT.fr hsw
          sv := hT.sv.keep hP.lay (by omega) hP.sp_ge hsw
          hdr := hT.hdr.set_used _ (by omega)
          arr := hsw.keep hP.lay (ArrAt.reads (r := R.bD) (Iv.sub_self _)) hT.arr }

/-- **`mp_add_d` for `a ≥ 0`** (no call of `mp_sub_d`), any stack depth `F ≥ 64`. -/
theorem pos_correct (hF : 64 ≤ F) (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hs : a.sign = Layout.mpZpos) :
    Triple (At 0x80004e30#64 (entryL ra s0 sp pa b pc) m v.keepR outp)
      (Api.AddD.Ret F m v outp sp pa adp pc cdp a b c ra s0) := by
  have hsh := hP.va.toShape
  have hua := hsh.used_le; have hroom := hP.room
  have hH := hfacts (s0 := s0) hP hF
  rw [show a.sign = 0 from hs] at hH
  have hsn := snap1 (s0 := s0) hP hF
  have hI0 : ArrFrm ρ R.bD (m1Of m ra s0 sp) (m1Of m ra s0 sp) cdp c.alloc (ovl (addDDigits a b) c.digit 0) :=
    ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; exact hsn.arr)
  have hneg : a.sign ≠ Layout.mpNeg := by rw [hs]; decide
  suffices hmain : Triple (At 0x80004e54#64 (pL ra sp pa b pc a.used) (m1Of m ra s0 sp) v.keepR outp)
      (RetD F m v outp sp pa adp pc cdp a c ra s0 (addDDigits a b) (a.used + 1) 0) from
    Triple.seq (p_step ra s0 v outp sp pa b pc a.used c.alloc m hP.img.mpAddD (pfacts hP hF))
      (Triple.rmap (fun cf ⟨c', M, hat, ho⟩ => ⟨c', M, hat, ho.repr,
        ⟨fun _ => ho.res, fun h => absurd h hneg, fun h => absurd h hneg⟩, ho.frame⟩) hmain)
  refine Triple.seq ?_ (Triple.seq (carry hP hF) (tail hP hF (addDDigits_lt hsh hP.hb) (addDDigits_high a b)
    (by omega)))
  by_cases h0 : a.used = 0
  · rw [show pL ra sp pa b pc a.used = pL ra sp pa b pc 0 by rw [h0]]
    have h := z_step ra v outp sp pa b pc c.used adp cdp (m1Of m ra s0 sp) (ro1 hP hF).img.mpAddD (h0 ▸ hH)
    rw [writeLog_nil] at h
    exact Triple.rmap (fun cf h' => (⟨_, by rw [h0]; exact hI0, by rw [h0]; exact h'⟩ : St F m v outp sp pa adp pc cdp a c ra s0
      0x80004eb0#64 (jL ra sp pa pc c.used cdp a.used (addDCarry a b a.used))
      (ovl (addDDigits a b) c.digit a.used) cf)) h
  · have h1 : 1 ≤ a.used := by omega
    have h := e_step ra v outp sp pa b pc a.used c.used adp cdp (m1Of m ra s0 sp) (ro1 hP hF).img.mpAddD hH h1
    rw [writeLog_nil] at h
    exact Triple.seq (Triple.rmap (fun cf h' => (⟨_, hI0, h'⟩ : St F m v outp sp pa adp pc cdp a c ra s0
      0x80004e80#64 (lL ra sp pa pc c.used adp cdp 0 (addDCarry a b 0)) (ovl (addDDigits a b) c.digit 0) cf)) h)
      (loop hP hF h1 0 (by omega))

end

end Tom.Machine.Fn.AddD
