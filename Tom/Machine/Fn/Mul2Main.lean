import Tom.Machine.Fn.Mul2
import Tom.Machine.Api.Mul2
import Tom.Machine.Kit.TwoTail
import Tom.Machine.Kit.Loop

/-!
# `mp_mul_2` on the machine: the whole function

The segments of `Tom.Machine.Fn.Mul2` chained into `Api.Mul2.Statement`,
over `Two`'s regions (`Pre.lay`). Snapshots: the entry memory `m` (code,
`a`) and the memory after the prologue `m2Of` (the saved registers,
`b->used := a->used`, `Snap`). The loop changes only `b`'s digits
(`ArrFrm … .bD` at the join points `St`). After it the struct is written
(`++b->used`, `b->sign`), so from `5d34` on the state is a `Tail`: frame,
saved registers, `b`'s struct as an `HdrAt` and its digits as an `ArrAt`.
-/

namespace Tom.Machine.Fn.Mul2

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

/-- `b->used` after the final carry. -/
abbrev nOf (a : MpInt) : Nat := a.used + addCarryAt a a a.used

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt}
  {ra s0 s1 : BitVec 64}

local notation "ρ" => Two.lay 32 sp pa adp pb bdp a b

theorem RO.of (hP : Api.Mul2.Pre m sp pa adp pb bdp a b ra) {M : Mem} (hF : Frm ρ ws m M) : RO M pa adp a :=
  { img := hF.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
    ra_ := hF.keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_ }

theorem snap (hP : Api.Mul2.Pre m sp pa adp pb bdp a b ra) :
    Snap ρ m (m2Of m ra s0 s1 sp pb a.used) ra s0 s1 sp pb bdp a.used b.alloc b.sign b.digit := by
  have := hP.sp_ge; have := hP.va.used_le; have := hP.va.alloc_lt
  have hF1 : Frm ρ [R.stk] m (writeLog m (frameLog ra s0 s1 sp)) :=
    Frm.store (by simp only [LogIn, frameLog, Iv.Sub, Two.lay, and_true]; omega)
  have hF2 : Frm ρ [R.bS] (writeLog m (frameLog ra s0 s1 sp)) (m2Of m ra s0 s1 sp pb a.used) :=
    Frm.sw (Iv.sub_pre (by decide))
  have hsv : Saved (writeLog m (frameLog ra s0 s1 sp)) ra s0 s1 sp :=
    { ra_v := bytesT8_log _ _ 2 _ _ rfl (by simp [frameLog, OutLRange])
      s0_v := bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog, OutLRange]; omega)
      s1_v := bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog, OutLRange]; omega) }
  have hb := hF1.keep hP.lay (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hP.rb
  exact { fr := hF1.trans hF2
          sv := hsv.keep hP.lay (by decide) hP.sp_ge hF2
          hdr := hb.hdr.set_used _ (by omega)
          arr := hF2.keep hP.lay (ArrAt.reads (r := R.bD) (Iv.sub_self _)) hb.arr }

/-- The loop's join points: `b`'s digits hold `f`, nothing else changed since `m2Of`. -/
abbrev St (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (ra s0 s1 : BitVec 64) :=
  ASt (Two.lay 32 sp pa adp pb bdp a b) R.bD (m2Of m ra s0 s1 sp pb a.used) bdp b.alloc v.keepR1 outp

theorem ro (hP : Api.Mul2.Pre m sp pa adp pb bdp a b ra) {M : Mem} {f : Nat → Nat}
    (hI : ArrFrm ρ R.bD (m2Of m ra s0 s1 sp pb a.used) M bdp b.alloc f) : RO M pa adp a :=
  RO.of hP (((snap (s0 := s0) (s1 := s1) hP).fr.trans hI.fr).mono)

theorem code_sub : Iv.Sub ⟨mpMul2Base, 240⟩ textIv := ⟨by decide, by decide⟩

theorem lfacts (hP : Api.Mul2.Pre m sp pa adp pb bdp a b ra) {M : Mem} (hro : RO M pa adp a) {i : Nat}
    (hi : i < a.used) : LFacts M pa adp bdp a.used i (a.digit i) :=
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt; have hroom := hP.room
  have hra : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  have hrb : Ram bdp (4 * b.alloc) := by simpa [Layout.sizeofDigit] using hP.gb.ds
  { rx := ⟨by have := hra.lo_ge; omega, by have := hra.hi_le; omega, by have := hra.off; omega⟩
    x_v := by simpa [Layout.sizeofDigit] using hro.ra_.digits i (by omega)
    x_lt := by have := hs.digit_lt i; rwa [radix_eq] at this
    ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    ua_v := by simpa [Layout.offUsed] using hro.ra_.used
    ua_lt := by omega
    rb := ⟨by have := hrb.lo_ge; omega, by have := hrb.hi_le; omega, by have := hrb.off; omega⟩
    b_al := hP.gb.ds_al
    ab := hP.lay.sub (r := R.aS) (s := R.bD) (Iv.sub_self _) (Iv.sub_elem (by omega))
    code_b := hP.lay.sub (r := R.bD) (s := R.code) (Iv.sub_elem (by omega)) code_sub }

end

/-! ## The loop -/

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt}
  {ra s0 s1 : BitVec 64}

/-- One loop segment (back edge to `5cec`, or the exit at `5d1c`). -/
theorem l_seg (hP : Api.Mul2.Pre m sp pa adp pb bdp a b ra) (i : Nat) (hi : i < a.used) (pc' : BitVec 64)
    (hseg : ∀ M, CodeAt M mpMul2Base mpMul2Code → LFacts M pa adp bdp a.used i (a.digit i) →
      Triple (At 0x80005cec#64 (lL ra sp pa pb bdp b.used adp i (addCarryAt a a i)) M v.keepR1 outp)
      (At pc' (lL ra sp pa pb bdp b.used adp (i + 1) (a.digit i / 134217728))
        (writeLog M [(bdp + 4 * i, 4, BitVec.ofNat 64 ((2 * a.digit i + addCarryAt a a i) % 268435456))])
        v.keepR1 outp)) :
    Triple (St m v outp sp pa adp pb bdp a b ra s0 s1 0x80005cec#64
        (lL ra sp pa pb bdp b.used adp i (addCarryAt a a i)) (ovl (addDigits a a) b.digit i))
      (St m v outp sp pa adp pb bdp a b ra s0 s1 pc'
        (lL ra sp pa pb bdp b.used adp (i + 1) (addCarryAt a a (i + 1))) (ovl (addDigits a a) b.digit (i + 1))) := by
  have hs := hP.va.toShape
  have hua := hs.used_le; have hroom := hP.room
  have hc := addCarryAt_le_one hs hs i
  refine ASt.store (v := (2 * a.digit i + addCarryAt a a i) % 268435456) (fun M hI => ?_) (by omega)
    (by rw [addDigits_self_lt hs hi, radix_eq, Nat.two_mul]) (by omega)
  have hro := ro (s0 := s0) (s1 := s1) hP hI
  have h := hseg M hro.img.mpMul2 (lfacts hP hro hi)
  rwa [show a.digit i / 134217728 = addCarryAt a a (i + 1) by rw [addCarryAt_self_succ hs]] at h

theorem loop (hP : Api.Mul2.Pre m sp pa adp pb bdp a b ra) (h1 : 1 ≤ a.used) :
    ∀ i, i < a.used → Triple (St m v outp sp pa adp pb bdp a b ra s0 s1 0x80005cec#64
        (lL ra sp pa pb bdp b.used adp i (addCarryAt a a i)) (ovl (addDigits a a) b.digit i))
      (St m v outp sp pa adp pb bdp a b ra s0 s1 0x80005d1c#64
        (lL ra sp pa pb bdp b.used adp a.used (addCarryAt a a a.used)) (ovl (addDigits a a) b.digit a.used)) := by
  have hs := hP.va.toShape
  refine Triple.countup (fun i hi => l_seg hP i (by omega) _ fun M hc hf =>
    l_step ra v outp sp pa pb bdp b.used adp a.used i _ _ M hc hf (addCarryAt_le_one hs hs i) hi) ?_
  have h := l_seg (s0 := s0) (s1 := s1) (v := v) (outp := outp) hP (a.used - 1) (by omega) _ fun M hc hf =>
    le_step ra v outp sp pa pb bdp b.used adp a.used (a.used - 1) _ _ M hc hf (addCarryAt_le_one hs hs _)
      (by omega)
  rw [show a.used - 1 + 1 = a.used by omega] at h
  exact h

end

/-! ## The phases -/

/-- At `pc` with `b->used = n` and digits `f` (from `5d34` on). -/
def TSt (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra s0 s1 : BitVec 64)
    (pc : BitVec 64) (L : GRegs) (n : Nat) (f : Nat → Nat) (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, Tail (Two.lay 32 sp pa adp pb bdp a b) m M ra s0 s1 sp pb bdp n b.alloc b.sign f ∧
    At pc L M v.keepR1 outp cf

/-- The result: `used = n`, `a`'s sign, the digits of `a + a`. -/
def bRes (a b : MpInt) : MpInt :=
  { used := nOf a, alloc := b.alloc, sign := a.sign, digits := (List.range b.alloc).map (addDigits a a) }

theorem bRes_digit {a b : MpInt} (ha : a.Shape) (hroom : a.used + 1 ≤ b.alloc) :
    (bRes a b).digit = addDigits a a := by
  funext i
  unfold MpInt.digit bRes
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < b.alloc
  · rw [List.getElem?_range h, Option.map_some, Option.getD_some]
  · rw [List.getElem?_eq_none (by rw [List.length_range]; omega), Option.map_none, Option.getD_none,
      addDigits_high ha ha i (by rw [Nat.max_self]; omega)]

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt}
  {ra s0 s1 : BitVec 64}

local notation "ρ" => Two.lay 32 sp pa adp pb bdp a b

theorem disj_or {x n y k : Nat} (h : Iv.Disj ⟨x, n⟩ ⟨y, k⟩) : x + n ≤ y ∨ y + k ≤ x := h

/-- A loop join point as a `Tail`. -/
theorem tail_of (hP : Api.Mul2.Pre m sp pa adp pb bdp a b ra) {M : Mem} {f : Nat → Nat}
    (hI : ArrFrm ρ R.bD (m2Of m ra s0 s1 sp pb a.used) M bdp b.alloc f) :
    Tail ρ m M ra s0 s1 sp pb bdp a.used b.alloc b.sign f :=
  (snap (s0 := s0) (s1 := s1) hP).tail hP.lay (by decide) hP.sp_ge hI

theorem ufacts (hP : Api.Mul2.Pre m sp pa adp pb bdp a b ra) {M : Mem} {n al sg : Nat}
    (h : HdrAt M pb bdp n al sg) (hn : n + 1 < 2 ^ 31) : UFacts M pb n :=
  { rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
    u_v := by simpa [Layout.offUsed] using h.used
    u_lt := hn }

theorem sfacts (hP : Api.Mul2.Pre m sp pa adp pb bdp a b ra) : SFacts pb :=
  { rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
    pb_al := hP.gb.st_al
    code_b := disj_or (hP.lay.sub (r := R.bS) (s := R.code) (Iv.sub_self _) code_sub) }

/-- From the entry to `5d34`: the prologue, the loop, the final carry. -/
theorem phase1 (hP : Api.Mul2.Pre m sp pa adp pb bdp a b ra) :
    Triple (At 0x80005ca0#64 (entry1 ra s0 s1 sp pa pb) m v.keepR1 outp)
      (TSt m v outp sp pa adp pb bdp a b ra s0 s1 0x80005d34#64 (tL ra sp pa pb bdp (nOf a) b.used) (nOf a)
        (ovl (addDigits a a) b.digit (nOf a))) := by
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
  simp only [Iv.Disj, Disj, Two.lay] at hsa hsb hab hsc
  have hpf : ProFacts m sp pa pb a.used b.alloc :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
      rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
      ua_v := by simpa [Layout.offUsed] using hP.ra_.used
      al_v := by simpa [Layout.offAlloc] using hP.rb.alloc
      ua_lt := by omega, al_lt := hbl, room := by omega
      s_a := by omega, s_b := by omega, code_s := by omega }
  have hbf : BFacts (writeLog m (frameLog ra s0 s1 sp)) pa pb b.used bdp adp :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
      pb_al := hP.gb.st_al
      ou_v := by simpa [Layout.offUsed] using hb1.used
      bdp_v := by simpa [Layout.offDp] using hb1.dpv
      adp_v := by simpa [Layout.offDp] using hro1.ra_.dpv
      ou_lt := by omega, ab := by omega, code_b := (sfacts hP).code_b }
  have hsn := snap (s0 := s0) (s1 := s1) hP
  refine Triple.seq (p_step ra s0 s1 v outp sp pa pb a.used b.alloc m hro0.img.mpMul2 hpf) ?_
  by_cases h0 : a.used = 0
  · have hn : nOf a = 0 := by simp only [nOf, h0]; rfl
    rw [hn, ovl_zero, show pL ra sp pa pb a.used = pL ra sp pa pb 0 by rw [h0]]
    refine Triple.rmap (fun cf h => ⟨_, ?_, h⟩)
      (e0_step ra v outp sp pa pb b.used bdp adp _ hro1.img.mpMul2 hbf)
    have hT := tail_of (s0 := s0) (s1 := s1) hP
      (ArrFrm.init (w := R.bD) (Iv.sub_self _) hsn.arr : ArrFrm ρ R.bD _ _ bdp b.alloc b.digit)
    rw [h0] at hT
    exact hT
  have h1 : 1 ≤ a.used := by omega
  have hI0 : ArrFrm ρ R.bD (m2Of m ra s0 s1 sp pb a.used) (m2Of m ra s0 s1 sp pb a.used) bdp b.alloc
      (ovl (addDigits a a) b.digit 0) := ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; exact hsn.arr)
  refine Triple.seq (Triple.rmap (fun cf h => ⟨_, hI0, h⟩)
      (e1_step ra v outp sp pa pb a.used b.used bdp adp _ hro1.img.mpMul2 hbf h1 (by omega)))
    (Triple.seq (loop (s0 := s0) (s1 := s1) hP h1 0 (by omega)) ?_)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (addCarryAt_le_one hs hs a.used) with hc | hc
  · have hn : nOf a = a.used := by simp only [nOf, hc, Nat.add_zero]
    rw [hn, hc]
    exact Triple.rmap (fun cf ⟨M, hI, hat⟩ => ⟨M, tail_of hP hI, hat⟩)
      (ASt.seg fun M hI => n_step ra v outp sp pa pb bdp b.used adp a.used M
        (ro hP hI).img.mpMul2 (ufacts hP (tail_of hP hI).hdr (by omega)))
  · have hn : nOf a = a.used + 1 := by simp only [nOf, hc]
    rw [hn, hc]
    have hrb : Ram bdp (4 * b.alloc) := by simpa [Layout.sizeofDigit] using hP.gb.ds
    have hcf : CFacts bdp a.used :=
      { rb := ⟨by have := hrb.lo_ge; omega, by have := hrb.hi_le; omega, by have := hrb.off; omega⟩
        b_al := hP.gb.ds_al
        code_b := disj_or (hP.lay.sub (r := R.bD) (s := R.code) (Iv.sub_elem (by omega)) code_sub) }
    refine Triple.seq (ASt.store (v := 1) (i := a.used) (fun M hI => c1_step ra v outp sp pa pb bdp b.used adp a.used M
      (ro hP hI).img.mpMul2 hcf) (by omega) (by rw [addDigits_self_used hs, hc]) (by decide)) ?_
    intro cf ⟨M, hI, hat⟩
    have hT := tail_of hP hI
    have hsw : Frm ρ [R.bS] M (writeLog M [(pb, 4, BitVec.ofNat 64 (a.used + 1))]) := Frm.sw (Iv.sub_pre (by decide))
    refine Triple.rmap (fun cf h => ⟨_, ?_, h⟩)
      (c2_step ra v outp sp pa pb bdp b.used a.used M (ro hP hI).img.mpMul2 (ufacts hP hT.hdr (by omega))
        (sfacts hP)) cf hat
    exact { fr := Frm.step hT.fr hsw
            sv := hT.sv.keep hP.lay (by decide) hP.sp_ge hsw
            hdr := hT.hdr.set_used _ (by omega)
            arr := hsw.keep hP.lay (ArrAt.reads (r := R.bD) (Iv.sub_self _)) hT.arr }

/-- From `5d34` to `5d50`: `memset` the digits from `n` to `oldused` if there are any. -/
theorem phase2 (hP : Api.Mul2.Pre m sp pa adp pb bdp a b ra) :
    Triple (TSt m v outp sp pa adp pb bdp a b ra s0 s1 0x80005d34#64 (tL ra sp pa pb bdp (nOf a) b.used) (nOf a)
        (ovl (addDigits a a) b.digit (nOf a)))
      (TSt m v outp sp pa adp pb bdp a b ra s0 s1 0x80005d50#64 (rL sp pa pb) (nOf a) (addDigits a a)) := by
  intro cf ⟨M, hT, hat⟩
  have hs := hP.va.toShape
  have hua := hs.used_le; have hal := hs.alloc_lt; have hroom := hP.room
  have hbu := hP.sb.used_le; have hbl := hP.sb.alloc_lt
  have hc := addCarryAt_le_one hs hs a.used
  have hrb : Ram bdp (4 * b.alloc) := by simpa [Layout.sizeofDigit] using hP.gb.ds
  have hro := RO.of hP hT.fr
  have hfin : ∀ k, b.used ≤ k → nOf a ≤ k → ∀ j, j < b.alloc →
      ovl (addDigits a a) b.digit k j = addDigits a a j := fun k hk hk' j hj => by
    simp only [ovl]
    split
    · rfl
    · rw [hP.sb.high_zero j (by omega), addDigits_self_high hs j (by simp only [nOf] at hk'; omega)]
  by_cases hou : b.used ≤ nOf a
  · exact Triple.rmap (fun cf h => ⟨_, hT.congr (hfin _ hou (Nat.le_refl _)), h⟩)
      (t0_step ra v outp sp pa pb bdp (nOf a) b.used M hro.img.mpMul2 (by simp only [nOf]; omega) hou) cf hat
  have hms : Memset.Pre (writeLog M []) (bdp + 4 * nOf a) 0 (4 * (b.used - nOf a)) :=
    Two.memset_pre hP.lay hP.gb hro.img (by omega) hbu
  refine Triple.seq (t1_step ra v outp sp pa pb bdp (nOf a) b.used M hro.img.mpMul2 (by omega) (by omega)
      (by have := hrb.hi_le; omega))
    (Triple.rmap ?_ (memset_call ra v outp sp pa pb bdp (nOf a) b.used _ hro.img.mpMul2 hms)) cf hat
  intro cf ⟨M', hat', hpost⟩
  rw [writeLog_nil] at hpost
  exact ⟨M', (hT.fill hP.lay (by decide) hP.sp_ge (by omega) hbu hpost
    fun j h1 _ => addDigits_self_high hs j h1).congr (hfin _ (Nat.le_refl _) (by omega)), hat'⟩

/-- From `5d50` to the return: `b->sign := a->sign`, the epilogue. -/
theorem phase3 (hP : Api.Mul2.Pre m sp pa adp pb bdp a b ra) :
    Triple (TSt m v outp sp pa adp pb bdp a b ra s0 v.s.s1 0x80005d50#64 (rL sp pa pb) (nOf a) (addDigits a a))
      (Api.Mul2.Ret m v outp sp pa adp pb bdp a b ra s0) := by
  intro cf ⟨M, hT, hat⟩
  have hs := hP.va.toShape
  have hsg := hP.va.sign_ok
  simp only [Layout.mpZpos, Layout.mpNeg] at hsg
  have hro := RO.of hP hT.fr
  have hsb := hP.lay.disj (r := R.stk) (s := R.bS)
  simp only [Iv.Disj, Disj, Two.lay] at hsb
  have := hP.sp_ge
  have hrf : RFacts M ra s0 v.s.s1 sp pa pb a.sign :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
      sa_v := by simpa [Layout.offSign] using hro.ra_.sign
      sa_lt := by omega
      ra_v := hT.sv.ra_v, s0_v := hT.sv.s0_v, s1_v := hT.sv.s1_v
      ra_al := hP.ra_al, s := sfacts hP, s_b := by omega }
  have hsw : Frm ρ [R.bS] M (writeLog M [(pb + 8, 4, BitVec.ofNat 64 a.sign)]) :=
    Frm.sw (by simp only [Iv.Sub, Two.lay]; omega)
  refine Triple.rmap (fun cf h => ⟨bRes a b, _, h.reshape (by simp) (by simp [Abi.keepR, Abi.keepR1, sKeepL]), ?_⟩)
    (r_step ra s0 v.s.s1 v outp sp pa pb a.sign M hro.img.mpMul2 hrf) cf hat
  have hd := bRes_digit (b := b) hs hP.room
  exact { repr := HdrAt.mpAt (hT.hdr.set_sign _ (by omega))
            ((hsw.keep hP.lay (ArrAt.reads (r := R.bD) (Iv.sub_self _)) hT.arr).congr fun j _ => by rw [hd])
          mul2 := { alloc := rfl, len := by simp [bRes], digit := hd, used := rfl, sign := rfl }
          frame := Frm.step hT.fr hsw }

end

/-- **`mp_mul_2` on the machine.** -/
theorem correct : Api.Mul2.Statement := by
  intro m v outp sp pa adp pb bdp a b ra s0 hP
  refine Triple.lmap (fun cf h => h.reshape (L' := entry1 ra s0 v.s.s1 sp pa pb) (K' := v.keepR1)
    (by simp [Api.Mul2.entryL, entry1, Abi.keepR, sKeepL])
    (by simp [Api.Mul2.entryL, Abi.keepR1, Abi.keepR, sKeepL])) ?_
  exact Triple.seq (phase1 hP) (Triple.seq (phase2 hP) (phase3 hP))

end Tom.Machine.Fn.Mul2
