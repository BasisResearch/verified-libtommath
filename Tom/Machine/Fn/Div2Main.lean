import Tom.Machine.Fn.Div2
import Tom.Machine.Api.Div2
import Tom.Machine.Kit.TwoTail
import Tom.Machine.Kit.ArrDown
import Tom.Machine.Kit.Loop

/-!
# `mp_div_2` on the machine: the whole function

The segments of `Tom.Machine.Fn.Div2` chained into `Api.Div2.Statement`,
over `Two`'s regions (`Pre.lay`). As `Fn/Mul2Main.lean`: the snapshot after
the prologue (`m2Of`, a `Two.Snap`), the loop's join points `St` over `b`'s
digits, from `51b4` on a `Two.Tail`. The loop runs from the top digit down,
so its overlay is `ovlD` (`Kit/ArrDown.lean`) and it is a `Triple.countdown`.
`mp_clamp` gets `div2Mid a b`, and its `ClampPost` is `Div2Post`.
-/

namespace Tom.Machine.Fn.Div2

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api
open Tom.Machine.Api.Two (R isW ws Saved Tail Snap)

/-- What stays as at the entry. -/
structure RO (M : Mem) (pa adp : Nat) (a : MpInt) : Prop where
  img : Img M
  ra_ : MpAt M pa adp a

/-- The memory after the prologue. -/
def m2Of (m : Mem) (ra s0 s1 : BitVec 64) (sp pb ua : Nat) : Mem :=
  writeLog (writeLog m (frameLog ra s0 s1 sp)) [(pb, 4, BitVec.ofNat 64 ua)]

/-- The carry into digit `x` of the loop: the low bit of `a[x + 1]`. -/
abbrev rOf (a : MpInt) (x : Nat) : Nat := a.digit (x + 1) % 2

theorem code_sub : Iv.Sub ⟨mpDiv2Base, 216⟩ textIv := ⟨by decide, by decide⟩

theorem clamp_sub : Iv.Sub ⟨mpClampBase, 64⟩ textIv := ⟨by decide, by decide⟩

theorem disj_or {x n y k : Nat} (h : Iv.Disj ⟨x, n⟩ ⟨y, k⟩) : x + n ≤ y ∨ y + k ≤ x := h

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt}
  {ra s0 s1 : BitVec 64}

local notation "ρ" => Two.lay 32 sp pa adp pb bdp a b

theorem RO.of (hP : Api.Div2.Pre m sp pa adp pb bdp a b ra) {M : Mem} (hF : Frm ρ ws m M) : RO M pa adp a :=
  { img := hF.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
    ra_ := hF.keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_ }

theorem snap (hP : Api.Div2.Pre m sp pa adp pb bdp a b ra) :
    Snap ρ m (m2Of m ra s0 s1 sp pb a.used) ra s0 s1 sp pb bdp a.used b.alloc b.sign b.digit := by
  have := hP.sp_ge; have := hP.va.used_le; have := hP.va.alloc_lt
  have hF1 : Frm ρ [R.stk] m (writeLog m (frameLog ra s0 s1 sp)) :=
    Frm.store (by simp only [LogIn, frameLog, Iv.Sub, Two.lay, and_true]; omega)
  have hF2 : Frm ρ [R.bS] (writeLog m (frameLog ra s0 s1 sp)) (m2Of m ra s0 s1 sp pb a.used) :=
    Frm.sw (Iv.sub_pre (by decide))
  have hsv : Saved (writeLog m (frameLog ra s0 s1 sp)) ra s0 s1 sp :=
    { ra_v := bytesT8_log _ _ 2 _ _ rfl (by simp [frameLog, OutLRange])
      s0_v := bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog, OutLRange]; omega)
      s1_v := bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog, OutLRange]; omega) }
  have hb := hF1.keep hP.lay (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hP.rb
  exact { fr := hF1.trans hF2
          sv := hsv.keep hP.lay (by decide) hP.sp_ge hF2
          hdr := hb.hdr.set_used _ (by omega)
          arr := hF2.keep hP.lay (ArrAt.reads (r := R.bD) (Iv.sub_self _)) hb.arr }

/-- The loop's join points: `b`'s digits hold `f`, nothing else changed since `m2Of`. -/
abbrev St (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 s1 : BitVec 64) :=
  ASt (Two.lay 32 sp pa adp pb bdp a b) R.bD (m2Of m ra s0 s1 sp pb a.used) bdp b.alloc v.keepR1 outp

theorem ro (hP : Api.Div2.Pre m sp pa adp pb bdp a b ra) {M : Mem} {f : Nat → Nat}
    (hI : ArrFrm ρ R.bD (m2Of m ra s0 s1 sp pb a.used) M bdp b.alloc f) : RO M pa adp a :=
  RO.of hP (((snap (s0 := s0) (s1 := s1) hP).fr.trans hI.fr).mono)

theorem tail_of (hP : Api.Div2.Pre m sp pa adp pb bdp a b ra) {M : Mem} {f : Nat → Nat}
    (hI : ArrFrm ρ R.bD (m2Of m ra s0 s1 sp pb a.used) M bdp b.alloc f) :
    Tail ρ m M ra s0 s1 sp pb bdp a.used b.alloc b.sign f :=
  (snap (s0 := s0) (s1 := s1) hP).tail hP.lay (by decide) hP.sp_ge hI

theorem dfacts (hP : Api.Div2.Pre m sp pa adp pb bdp a b ra) : DFacts adp bdp a.used :=
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt; have hroom := hP.room
  have hra : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have hrb : Ram bdp (4 * b.alloc) := by simpa [Layout.sizeofDigit] using hP.gb.ds
  { ra_d := ⟨by have := hra.lo_ge; omega, by have := hra.hi_le; omega, by have := hra.off; omega⟩
    rb_d := ⟨by have := hrb.lo_ge; omega, by have := hrb.hi_le; omega, by have := hrb.off; omega⟩
    ua_lt := by omega }

theorem lfacts (hP : Api.Div2.Pre m sp pa adp pb bdp a b ra) {M : Mem} (hro : RO M pa adp a) {x : Nat}
    (hx : x < a.used) : LFacts adp bdp a.used x (a.digit x) M :=
  have hs := hP.va.toShape
  have hua := hs.used_le; have hroom := hP.room
  { rd := dfacts hP, x_lt := hx
    d_v := by simpa [Layout.sizeofDigit] using hro.ra_.digits x (by omega)
    d_lt := by have := hs.digit_lt x; rwa [radix_eq] at this
    b_al := hP.gb.ds_al
    code_b := disj_or (hP.lay.sub (r := R.bD) (s := R.code) (Iv.sub_elem (by omega)) code_sub) }

theorem ufacts (hP : Api.Div2.Pre m sp pa adp pb bdp a b ra) {M : Mem} {n al sg : Nat}
    (h : HdrAt M pb bdp n al sg) (hn : n < 2 ^ 31) (hb0 : 1 ≤ b.alloc) : UFacts M pb bdp n :=
  { rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
    u_v := by simpa [Layout.offUsed] using h.used
    u_lt := hn
    bb := by
      have := hP.gb.disj
      simp only [Layout.sizeofMpInt, Layout.sizeofDigit] at this
      have := hP.lay.disj (r := R.bS) (s := R.bD)
      simp only [Iv.Disj, Disj, Two.lay] at this
      omega }

end

/-! ## The loop -/

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt}
  {ra s0 s1 : BitVec 64}

/-- The loop head at `x`, with `x < a->used`. -/
def LP (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 s1 : BitVec 64) (x : Nat) (cf : Vsa.Machine.Config) : Prop :=
  x < a.used ∧ St m v outp sp pa adp pb bdp a b ra s0 s1 0x8000518c#64
    (lL ra sp pa pb bdp b.used adp x (rOf a x)) (ovlD (div2Digits a) b.digit (x + 1) a.used) cf

theorem div2Digits_eq (a : MpInt) (x : Nat) :
    a.digit x / 2 + 134217728 * rOf a x = div2Digits a x := by
  simp only [rOf, div2Digits, Nat.reducePow]

/-- The loop from `x` to `51b4`. -/
theorem loop (hP : Api.Div2.Pre m sp pa adp pb bdp a b ra) :
    ∀ x, Triple (LP m v outp sp pa adp pb bdp a b ra s0 s1 x)
      (St m v outp sp pa adp pb bdp a b ra s0 s1 0x800051b4#64 (Fn.Div2.tL ra sp pa pb bdp a.used b.used)
        (ovlD (div2Digits a) b.digit 0 a.used)) := by
  have hs := hP.va.toShape
  have hua := hs.used_le; have hroom := hP.room; have hal := hs.alloc_lt
  refine Triple.countdown (fun k => ?_) ?_
  · refine Triple.of_pure fun hk => Triple.rmap (fun cf h => Or.inr ⟨by omega, h⟩) ?_
    have : rOf a (k + 1) < 2 := Nat.mod_lt _ (by decide)
    refine ASt.storeD (v := a.digit (k + 1) / 2 + 134217728 * rOf a (k + 1)) (fun M hI => ?_) (by omega) hk
      (div2Digits_eq a (k + 1)) (by have := hs.digit_lt (k + 1); rw [radix_eq] at this; omega)
    have hro := ro (s0 := s0) (s1 := s1) hP hI
    exact l_step ra v outp sp pa pb bdp b.used adp a.used k _ _ M hro.img.mpDiv2 (lfacts hP hro hk)
      (by simp only [rOf]; omega)
  · refine Triple.of_pure fun hk => ?_
    have : rOf a 0 < 2 := Nat.mod_lt _ (by decide)
    refine ASt.storeD (v := a.digit 0 / 2 + 134217728 * rOf a 0) (fun M hI => ?_) (by omega) hk
      (div2Digits_eq a 0) (by have := hs.digit_lt 0; rw [radix_eq] at this; omega)
    have hro := ro (s0 := s0) (s1 := s1) hP hI
    exact le_step ra v outp sp pa pb bdp b.used adp a.used a.used _ _ M hro.img.mpDiv2 (lfacts hP hro hk)
      (by simp only [rOf]; omega) (ufacts hP (tail_of hP hI).hdr (by omega) (by omega))

end

/-! ## The phases -/

/-- At `pc` with `b->used = n` and digits `f` (from `51b4` on). -/
def TSt (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra s0 s1 : BitVec 64)
    (pc : BitVec 64) (L : GRegs) (n sg : Nat) (f : Nat → Nat) (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, Tail (Two.lay 32 sp pa adp pb bdp a b) m M ra s0 s1 sp pb bdp n b.alloc sg f ∧
    At pc L M v.keepR1 outp cf

theorem div2Mid_shape {a b : MpInt} (ha : a.Shape) (hroom : a.used ≤ b.alloc) (hb : b.alloc < 2 ^ 31) :
    (div2Mid a b).Shape :=
  have hd := div2Mid_digit (b := b) ha hroom
  { len := by simp [div2Mid]
    used_le := hroom
    alloc_lt := hb
    digit_lt := fun i => by rw [hd]; exact div2Digits_lt ha i
    high_zero := fun i hi => by rw [hd]; exact div2Digits_high ha i hi }

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt}
  {ra s0 s1 : BitVec 64}

local notation "ρ" => Two.lay 32 sp pa adp pb bdp a b

/-- From the entry to `51b4`: the prologue and the loop. -/
theorem phase1 (hP : Api.Div2.Pre m sp pa adp pb bdp a b ra) :
    Triple (At 0x80005134#64 (entry1 ra s0 s1 sp pa pb) m v.keepR1 outp)
      (TSt m v outp sp pa adp pb bdp a b ra s0 s1 0x800051b4#64 (tL ra sp pa pb bdp a.used b.used) a.used b.sign
        (ovl (div2Digits a) b.digit a.used)) := by
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt; have hroom := hP.room
  have hbu := hP.sb.used_le; have hbl := hP.sb.alloc_lt; have := hP.sp_ge
  have hF1 : Frm ρ [R.stk] m (writeLog m (frameLog ra s0 s1 sp)) :=
    Frm.store (by simp only [LogIn, frameLog, Iv.Sub, Two.lay, and_true]; omega)
  have hro0 := RO.of hP (Frm.refl _ m)
  have hro1 := RO.of hP hF1.mono
  have hb1 := hF1.keep hP.lay (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hP.rb
  have hsa := hP.lay.disj (r := R.stk) (s := R.aS)
  have hsb := hP.lay.disj (r := R.stk) (s := R.bS)
  have hab := hP.lay.disj (r := R.aS) (s := R.bS)
  have hsc := hP.lay.sub (r := R.stk) (s := R.code) (Iv.sub_self _) code_sub
  have hbc := hP.lay.sub (r := R.bS) (s := R.code) (Iv.sub_self _) code_sub
  simp only [Iv.Disj, Disj, Two.lay] at hsa hsb hab hsc hbc
  have hpf : ProFacts m sp pa pb a.used b.alloc :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
      rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
      ua_v := by simpa [Layout.offUsed] using hP.ra_.used
      al_v := by simpa [Layout.offAlloc] using hP.rb.alloc
      ua_lt := by omega, al_lt := hbl, room := hroom
      s_a := by omega, s_b := by omega, code_s := by omega }
  have hbf : BFacts (writeLog m (frameLog ra s0 s1 sp)) pa pb b.used bdp adp :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
      pb_al := hP.gb.st_al
      ou_v := by simpa [Layout.offUsed] using hb1.used
      bdp_v := by simpa [Layout.offDp] using hb1.dpv
      adp_v := by simpa [Layout.offDp] using hro1.ra_.dpv
      ou_lt := by omega, ab := by omega, code_b := hbc }
  have hsn := snap (s0 := s0) (s1 := s1) hP
  refine Triple.seq (p_step ra s0 s1 v outp sp pa pb a.used b.alloc m hro0.img.mpDiv2 hpf) ?_
  by_cases h0 : a.used = 0
  · rw [show pL ra sp pa pb a.used = pL ra sp pa pb 0 by rw [h0],
      show tL ra sp pa pb bdp a.used b.used = tL ra sp pa pb bdp 0 b.used by rw [h0], h0, ovl_zero]
    refine Triple.rmap (fun cf h => ⟨_, ?_, h⟩)
      (e0_step ra v outp sp pa pb b.used bdp adp _ hro1.img.mpDiv2 hbf)
    have hT := tail_of (s0 := s0) (s1 := s1) hP
      (ArrFrm.init (w := R.bD) (Iv.sub_self _) hsn.arr : ArrFrm ρ R.bD _ _ bdp b.alloc b.digit)
    rw [h0] at hT
    exact hT
  have h1 : 1 ≤ a.used := by omega
  have hI0 : ArrFrm ρ R.bD (m2Of m ra s0 s1 sp pb a.used) (m2Of m ra s0 s1 sp pb a.used) bdp b.alloc
      (ovlD (div2Digits a) b.digit (a.used - 1 + 1) a.used) :=
    ArrFrm.init (Iv.sub_self _) (by rw [Nat.sub_add_cancel h1, ovlD_top]; exact hsn.arr)
  have hr0 : rOf a (a.used - 1) = 0 := by
    simp only [rOf, Nat.sub_add_cancel h1, hs.high_zero a.used (Nat.le_refl _)]
  have hM2 : Frm ρ [R.bS] (writeLog m (frameLog ra s0 s1 sp)) (m2Of m ra s0 s1 sp pb a.used) :=
    Frm.sw (Iv.sub_pre (by decide))
  have hadp : bytesT8 (m2Of m ra s0 s1 sp pb a.used) (pa + 16) = BitVec.ofNat 64 adp :=
    hM2.keep hP.lay (Reads.w8 (r := R.aS) (by simp only [Iv.Sub, Two.lay]; omega)) hbf.adp_v
  refine Triple.seq (e1_step ra v outp sp pa pb a.used b.used bdp adp _ hro1.img.mpDiv2 hbf h1 (by omega)) ?_
  refine Triple.seq (Triple.rmap (fun cf h => by
      rw [writeLog_nil, ← hr0] at h
      exact (⟨by omega, _, hI0, h⟩ : LP m v outp sp pa adp pb bdp a b ra s0 s1 (a.used - 1) cf))
      (e2_step ra v outp sp pa pb a.used b.used bdp adp (m2Of m ra s0 s1 sp pb a.used)
        (RO.of hP (hF1.trans hM2).mono).img.mpDiv2
        hpf.ra_ hadp (dfacts hP) h1)) ?_
  refine Triple.rmap (fun cf ⟨M, hI, hat⟩ => ⟨M, ?_, hat⟩) (loop (s0 := s0) (s1 := s1) hP (a.used - 1))
  rw [← ovlD_zero]
  exact tail_of hP hI

/-- From `51b4` to `51d0`: `memset` the digits from `a->used` to `oldused` if there are any. -/
theorem phase2 (hP : Api.Div2.Pre m sp pa adp pb bdp a b ra) :
    Triple (TSt m v outp sp pa adp pb bdp a b ra s0 s1 0x800051b4#64 (tL ra sp pa pb bdp a.used b.used) a.used
        b.sign (ovl (div2Digits a) b.digit a.used))
      (TSt m v outp sp pa adp pb bdp a b ra s0 s1 0x800051d0#64 (rL sp pa pb) a.used b.sign (div2Digits a)) := by
  intro cf ⟨M, hT, hat⟩
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt; have hroom := hP.room
  have hbu := hP.sb.used_le; have hbl := hP.sb.alloc_lt
  have hrb : Ram bdp (4 * b.alloc) := by simpa [Layout.sizeofDigit] using hP.gb.ds
  have hro := RO.of hP hT.fr
  have hfin : ∀ k, b.used ≤ k → a.used ≤ k → ∀ j, j < b.alloc →
      ovl (div2Digits a) b.digit k j = div2Digits a j := fun k hk hk' j hj => by
    simp only [ovl]
    split
    · rfl
    · rw [hP.sb.high_zero j (by omega), div2Digits_high hs j (by omega)]
  by_cases hou : b.used ≤ a.used
  · exact Triple.rmap (fun cf h => ⟨_, hT.congr (hfin _ hou (Nat.le_refl _)), h⟩)
      (t0_step ra v outp sp pa pb bdp a.used b.used M hro.img.mpDiv2 (by omega) hou) cf hat
  have hms : Memset.Pre (writeLog M []) (bdp + 4 * a.used) 0 (4 * (b.used - a.used)) :=
    Two.memset_pre hP.lay hP.gb hro.img (by omega) hbu
  refine Triple.seq (t1_step ra v outp sp pa pb bdp a.used b.used M hro.img.mpDiv2 (by omega) (by omega)
      (by have := hrb.hi_le; omega))
    (Triple.rmap ?_ (memset_call ra v outp sp pa pb bdp a.used b.used _ hro.img.mpDiv2 hms)) cf hat
  intro cf ⟨M', hat', hpost⟩
  rw [writeLog_nil] at hpost
  exact ⟨M', (hT.fill hP.lay (by decide) hP.sp_ge (by omega) hbu hpost
    fun j h1 _ => div2Digits_high hs j h1).congr (hfin _ (Nat.le_refl _) (by omega)), hat'⟩

/-- From `51d0` to the return: `b->sign := a->sign`, `mp_clamp(b)`, the epilogue. -/
theorem phase3 (hP : Api.Div2.Pre m sp pa adp pb bdp a b ra) :
    Triple (TSt m v outp sp pa adp pb bdp a b ra s0 v.s.s1 0x800051d0#64 (rL sp pa pb) a.used b.sign
        (div2Digits a))
      (Api.Div2.Ret m v outp sp pa adp pb bdp a b ra s0) := by
  intro cf ⟨M, hT, hat⟩
  have hs := hP.va.toShape
  have hroom := hP.room; have hbl := hP.sb.alloc_lt
  have hsg := hP.va.sign_ok
  simp only [Layout.mpZpos, Layout.mpNeg] at hsg
  have hro := RO.of hP hT.fr
  have := hP.sp_ge
  have hbc := hP.lay.sub (r := R.bS) (s := R.code) (Iv.sub_self _) code_sub
  have hbl' := hP.lay.sub (r := R.bS) (s := R.code) (Iv.sub_self _) clamp_sub
  simp only [Iv.Disj, Disj, Two.lay] at hbc hbl'
  have hsf : SFacts M pa pb a.sign :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
      pb_al := hP.gb.st_al, code_b := hbc
      sa_v := by simpa [Layout.offSign] using hro.ra_.sign
      sa_lt := by omega }
  have hsw : Frm ρ [R.bS] M (writeLog M [(pb + 8, 4, BitVec.ofNat 64 a.sign)]) :=
    Frm.sw (by simp only [Iv.Sub, Two.lay]; omega)
  have hd := div2Mid_digit (b := b) hs hroom
  have hcp : Clamp.Pre (writeLog M [(pb + 8, 4, BitVec.ofNat 64 a.sign)]) pb bdp (div2Mid a b) :=
    { repr := HdrAt.mpAt (hT.hdr.set_sign _ (by omega))
        ((hsw.keep hP.lay (ArrAt.reads (r := R.bD) (Iv.sub_self _)) hT.arr).congr fun j _ => by rw [hd])
      shape := div2Mid_shape hs hroom hbl
      geom := hP.gb
      code := (RO.of hP (Frm.step hT.fr hsw)).img.mpClamp
      code_off := hbl' }
  refine Triple.seq (s_step v outp sp pa pb a.sign M hro.img.mpDiv2 hsf)
    (Triple.seq (clamp_call v outp sp pa pb bdp _ _ (RO.of hP (Frm.step hT.fr hsw)).img.mpDiv2 hcp) ?_) cf hat
  intro cf ⟨b', M', hat', hpost⟩
  have hcl : Frm ρ [R.bS] (writeLog M [(pb + 8, 4, BitVec.ofNat 64 a.sign)]) M' :=
    Frm.call (w := R.bS) hpost.frame (Iv.sub_pre (by decide))
  have hF := Frm.step (Frm.step hT.fr hsw) hcl
  have hsv := (hT.sv.keep hP.lay (by decide) hP.sp_ge hsw).keep hP.lay (by decide) hP.sp_ge hcl
  have hrf : RFacts M' ra s0 v.s.s1 sp :=
    { rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
      ra_v := hsv.ra_v, s0_v := hsv.s0_v, s1_v := hsv.s1_v, ra_al := hP.ra_al }
  refine Triple.rmap (fun cf h => ⟨b', _, h.reshape (by simp) (by simp [Abi.keepR, Abi.keepR1, sKeepL]), ?_⟩)
    (r_step ra s0 v.s.s1 v outp sp pa pb M' (RO.of hP hF).img.mpDiv2 hrf) cf hat'
  have hc := hpost.clamp
  exact { repr := hpost.repr
          div2 := { alloc := hc.alloc
                    len := by rw [hc.digits]; simp [div2Mid]
                    digit := by rw [hc.digit, hd]
                    used := by rw [hc.used, hd]; rfl
                    sign := by rw [hc.sign]; rfl }
          frame := hF }

end

/-- **`mp_div_2` on the machine.** -/
theorem correct : Api.Div2.Statement := by
  intro m v outp sp pa adp pb bdp a b ra s0 hP
  refine Triple.lmap (fun cf h => h.reshape (L' := entry1 ra s0 v.s.s1 sp pa pb) (K' := v.keepR1)
    (by simp [Api.Div2.entryL, entry1, Abi.keepR, sKeepL])
    (by simp [Api.Div2.entryL, Abi.keepR1, Abi.keepR, sKeepL])) ?_
  exact Triple.seq (phase1 hP) (Triple.seq (phase2 hP) (phase3 hP))

end Tom.Machine.Fn.Div2
