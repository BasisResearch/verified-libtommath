import Tom.Machine.Fn.MpSub
import Tom.Machine.Api.MpSub
import Tom.Machine.Api.SAdd
import Tom.Machine.Api.SSub
import Tom.Machine.Fn.CmpMag


/-!
# `mp_sub` on the machine: the whole function

The segments of `Tom.Machine.Fn.MpSub` and the standard contracts of
`s_mp_add`, `s_mp_sub` (`Api/SAdd.lean`, `Api/SSub.lean`) and `mp_cmp_mag`
chained into `Api.MpSub.Statement`. The regions are `Bin`'s; the layout is
`Pre.lay`. Each callee's layout comes by renaming (`Sound.pull`: the
identity, or `Bin.swap` for `s_mp_sub(b, a, c)`) and its frame back by
`Frm.push`. Read-only facts (`Img`, `a`, `b`) are pulled by `Frm.keep`.
-/


namespace Tom.Machine.Fn.MpSub

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api
open Tom.Machine.Api.Bin (R isW ws)

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat} {a b c : MpInt}
  {ra s0 : BitVec 64}

local notation "ρ" => Bin.lay 64 sp pa adp pb bdp pc cdp a b c

/-- What stays as at the entry. -/
structure RO (M : Mem) (pa adp pb bdp : Nat) (a b : MpInt) : Prop where
  img : Img M
  ra_ : MpAt M pa adp a
  rb : MpAt M pb bdp b

theorem RO.of (hP : MpSub.Pre m sp pa adp pb bdp pc cdp a b c ra) {M : Mem} (hF : Frm ρ ws m M) :
    RO M pa adp pb bdp a b :=
  { img := hF.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
    ra_ := hF.keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_
    rb := hF.keep hP.lay (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hP.rb }

/-- What a tail call leaves: `c'` at `c`, `Q`, memory changed only in `ws`. -/
structure Out (m M : Mem) (sp pa adp pb bdp pc cdp : Nat) (a b c c' : MpInt) (Q : Prop) : Prop where
  repr : MpAt M pc cdp c'
  q : Q
  frame : Frm (Bin.lay 64 sp pa adp pb bdp pc cdp a b c) ws m M

def RetQ (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp pc cdp : Nat) (a b c : MpInt)
    (ra s0 : BitVec 64) (Q : MpInt → Prop) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf ∧
    Out m M sp pa adp pb bdp pc cdp a b c c' (Q c')

theorem RetQ.ret {Q : MpInt → Prop} (h : ∀ c', Q c' → SubPost a b c c') :
    ∀ cf, RetQ m v outp sp pa adp pb bdp pc cdp a b c ra s0 Q cf →
      MpSub.Ret m v outp sp pa adp pb bdp pc cdp a b c ra s0 cf
  | _, ⟨c', M, hat, ho⟩ => ⟨c', M, hat, ⟨ho.repr, h c' ho.q, ho.frame⟩⟩

theorem sub_sign : Iv.Sub ⟨pc + 8, 4⟩ (ρ R.cS) := by simp only [Iv.Sub, Bin.lay]; omega

theorem sfacts (hP : MpSub.Pre m sp pa adp pb bdp pc cdp a b c ra) : SFacts m pa pb a.sign b.sign :=
  have ha := hP.va.sign_ok; have hb := hP.vb.sign_ok
  { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
    rb := by simpa [Layout.sizeofMpInt] using hP.gb.st
    sa_v := by simpa [Layout.offSign] using hP.ra_.sign
    sb_v := by simpa [Layout.offSign] using hP.rb.sign
    sa_lt := by simp only [Layout.mpZpos, Layout.mpNeg] at ha; omega
    sb_lt := by simp only [Layout.mpZpos, Layout.mpNeg] at hb; omega }

theorem csign (hP : MpSub.Pre m sp pa adp pb bdp pc cdp a b c ra) : CSign pc :=
  have h := hP.lay.disj (r := R.cS) (s := R.code)
  { rc := by simpa [Layout.sizeofMpInt] using hP.gc.st, pc_al := hP.gc.st_al
    code_off := by
      simp only [Iv.Disj, Disj, Bin.lay, textIv, textBase, textLen] at h
      simp only [mpSubBase]; omega }

theorem ffacts (hP : MpSub.Pre m sp pa adp pb bdp pc cdp a b c ra) : FFacts sp :=
  have h := hP.lay.disj (r := R.stk) (s := R.code)
  have := hP.sp_ge
  { rs := ⟨by have := hP.rs.lo_ge; omega, by have := hP.rs.hi_le; omega, by have := hP.rs.off; omega⟩
    sp_al := hP.sp_al, sp_ge := by omega
    code_off := by
      simp only [Iv.Disj, Disj, Bin.lay, textIv, textBase, textLen] at h
      simp only [mpSubBase]; omega }

theorem shape_sign (hc : c.Shape) (s : Nat) : (c.withSign s).Shape :=
  ⟨hc.len, hc.used_le, hc.alloc_lt, hc.digit_lt, hc.high_zero⟩

/-- The callee placements, inside ours. -/
theorem sub_id (s : Nat) : ∀ k, (Bin.lay 64 sp pa adp pb bdp pc cdp a b (c.withSign s) k).Sub (ρ (id k)) := by
  intro k; cases k <;> exact Iv.sub_self _

theorem sub_48 (hs : 64 ≤ sp) (s : Nat) :
    ∀ k, (Bin.lay 48 sp pa adp pb bdp pc cdp a b (c.withSign s) k).Sub (ρ (id k)) := by
  intro k; cases k <;> first | exact Iv.sub_self _ | (simp only [Iv.Sub, Bin.lay, id]; omega)

theorem sub_48s (hs : 64 ≤ sp) (s : Nat) :
    ∀ k, (Bin.lay 48 sp pb bdp pa adp pc cdp b a (c.withSign s) k).Sub (ρ (Bin.swap k)) := by
  intro k; cases k <;> first | exact Iv.sub_self _ | (simp only [Iv.Sub, Bin.lay, Bin.swap]; omega)

end

/-! ## The calls -/

/-- The callee-saved registers `mp_cmp_mag` sees: this frame's `sp`, `s0 = a`, `s1 = b`. -/
def cmpAbi (v : Abi) (sp pa pb : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 48), s0 := BitVec.ofNat 64 pa, s := { v.s with s1 := BitVec.ofNat 64 pb } }

/-- `mp_cmp_mag(a, b)` at `1f28`, back at `1f2c`. -/
theorem cmp_call (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt)
    (M : Mem) (hc : CodeAt M mpSubBase mpSubCode) (hP : CmpMag.Pre M pa adp pb bdp a b) :
    Triple (At 0x80001f28#64 (callL ra sp pa pb) M v.keepR1 outp)
      (At 0x80001f2c#64 (retL sp pa pb (BitVec.ofInt 64 (ordCode (compare a.mag b.mag)))) M v.keepR1 outp) := by
  refine Triple.seq (jal_at (pc := 0x80001f28#64) (w := 0x83dfe0ef#32) (imm := 0x1fe83c#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 pb),
        (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 pb)])
      (hc.word (a := (0x80001f28#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [callL]) (by simp [keysG]) (by simp [Abi.keepR1, keysG])) ?_
  refine Triple.dimap (fun c h => ?_) (fun c h => h.reshape ?_ ?_)
    (CmpMag.correct 0x80001f2c#64 (cmpAbi v sp pa pb) outp pa adp pb bdp a b M (by decide) hP)
  · have hpc : (0x80001f28#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x1fe83c#21) = CmpMag.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [CmpMag.entryL, Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR1, cmpAbi, sKeepL]
  · simp [retL, CmpMag.retL, Abi.keep, cmpAbi, sKeepL]
  · simp [Abi.keep, Abi.keepR1, cmpAbi, sKeepL]

/-! ## The branches -/

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp : Nat} {a b c : MpInt}
  {ra s0 : BitVec 64}

local notation "ρ" => Bin.lay 64 sp pa adp pb bdp pc cdp a b c

/-- Different signs: `c->sign := a->sign`, then `s_mp_add(a, b, c)`. -/
theorem diff (hP : MpSub.Pre m sp pa adp pb bdp pc cdp a b c ra) (hne : a.sign ≠ b.sign) :
    Triple (At 0x80001ef4#64 (entry1 ra s0 v.s.s1 sp pa pb pc) m v.keepR1 outp)
      (RetQ m v outp sp pa adp pb bdp pc cdp a b c ra s0 (SAddPost a b (c.withSign a.sign))) := by
  have hsf := sfacts hP; have := hP.sp_ge
  have hF : Frm ρ [R.cS] m (writeLog m [(pc + 8, 4, BitVec.ofNat 64 a.sign)]) := Frm.sw sub_sign
  have hro := RO.of hP hF.mono
  have hpre : Api.SAdd.Pre (writeLog m [(pc + 8, 4, BitVec.ofNat 64 a.sign)]) sp pa adp pb bdp pc cdp a b
      (c.withSign a.sign) ra :=
    { ra_ := hro.ra_, rb := hro.rb, rc := hP.rc.set_sign hP.gc a.sign (Nat.lt_trans hsf.sa_lt (by decide))
      sa := hP.va.toShape, sb := hP.vb.toShape, sc := shape_sign hP.sc _, csign := hP.va.sign_ok
      ga := hP.ga, gb := hP.gb, gc := hP.gc, room := hP.room, rs := hP.rs, sp_al := hP.sp_al
      sp_ge := hP.sp_ge, ra_al := hP.ra_al, img := hro.img
      lay := hP.lay.pull id _ Bin.all (sub_id _) }
  refine Triple.seq (s_step ra s0 v.s.s1 v outp sp pa pb pc _ _ m (RO.of hP (Frm.refl _ m)).img.mpSub hsf
      (csign hP) hne)
    (Triple.dimap (fun cf h => ?_)
      (fun cf ⟨c', M, hat, hpost⟩ => ⟨c', M, hat, hpost.repr, hpost.sadd,
        (hF.trans (Frm.push id (sub_id _) hpost.frame)).mono⟩)
      (Api.SAdd.correct hpre))
  exact h.reshape (by simp [Fn.SAdd.entryL, entry1, Abi.keepR1])
    (by simp [entry1, Abi.keepR1, Abi.keepR, sKeepL])

/-- After the comparison: `c->sign := s`, then `s_mp_sub(a, b, c)` (stack `[sp - 48, sp)`). -/
theorem tail (hP : MpSub.Pre m sp pa adp pb bdp pc cdp a b c ra) {M : Mem} (hF : Frm ρ [R.stk] m M)
    (hge : b.used ≤ a.used) (s : Nat) (hs : s = Layout.mpZpos ∨ s = Layout.mpNeg) :
    Triple (At 0x80004564#64 (entry1 ra s0 v.s.s1 sp pa pb pc) (writeLog M [(pc + 8, 4, BitVec.ofNat 64 s)])
        v.keepR1 outp)
      (RetQ m v outp sp pa adp pb bdp pc cdp a b c ra s0 (SSubPost a b (c.withSign s))) := by
  have := hP.sp_ge; have hroom := hP.room
  have hF3 := hF.trans (Frm.sw (w := R.cS) (v := BitVec.ofNat 64 s) sub_sign)
  have hro := RO.of hP hF3.mono
  have hs2 : s < 2 ^ 32 := by simp only [Layout.mpZpos, Layout.mpNeg] at hs; omega
  have hc := (hF.keep hP.lay (MpAt.reads (rs := R.cS) (rd := R.cD) (Iv.sub_self _) (Iv.sub_self _)) hP.rc).set_sign
    hP.gc s hs2
  have hrs := hP.rs
  have hpre : Api.SSub.Pre (writeLog M [(pc + 8, 4, BitVec.ofNat 64 s)]) sp pa adp pb bdp pc cdp a b
      (c.withSign s) ra :=
    { ra_ := hro.ra_, rb := hro.rb, rc := hc
      sa := hP.va.toShape, sb := hP.vb.toShape, sc := shape_sign hP.sc _, csign := hs
      ga := hP.ga, gb := hP.gb, gc := hP.gc, ge := hge, room := by simp only [MpInt.withSign_alloc]; omega
      rs := ⟨by have := hrs.lo_ge; omega, by have := hrs.hi_le; omega, by have := hrs.off; omega⟩
      sp_al := hP.sp_al, sp_ge := by omega, ra_al := hP.ra_al, img := hro.img
      lay := hP.lay.pull id _ Bin.all (sub_48 (by omega) _) }
  refine Triple.dimap (fun cf h => ?_)
    (fun cf ⟨c', M', hat, hpost⟩ => ⟨c', M', hat, hpost.repr, hpost.ssub,
      (hF3.trans (Frm.push id (sub_48 (by omega) _) hpost.frame)).mono⟩)
    (Api.SSub.correct hpre)
  exact h.reshape (by simp [Fn.SSub.entryL, entry1, Abi.keepR1])
    (by simp [entry1, Abi.keepR1, Abi.keepR, sKeepL])

theorem Pre.swap (hP : MpSub.Pre m sp pa adp pb bdp pc cdp a b c ra) : MpSub.Pre m sp pb bdp pa adp pc cdp b a c ra :=
  { hP with ra_ := hP.rb, rb := hP.ra_, va := hP.vb, vb := hP.va, ga := hP.gb, gb := hP.ga
            room := by rw [Nat.max_comm]; exact hP.room
            lay := Bin.sound_swap hP.lay }

/-- A tail call's result for `(b, a)`, in our names. -/
theorem RetQ.unswap {Q : MpInt → Prop} (h : ∀ c', Q c' → SubPost a b c c') :
    ∀ cf, RetQ m v outp sp pb bdp pa adp pc cdp b a c ra s0 Q cf →
      MpSub.Ret m v outp sp pa adp pb bdp pc cdp a b c ra s0 cf
  | _, ⟨c', M, hat, ho⟩ => ⟨c', M, hat, ⟨ho.repr, h c' ho.q,
      (Frm.push Bin.swap (fun k => by cases k <;> exact Iv.sub_self _) ho.frame).mono⟩⟩

theorem ne_lt : ∀ o : Ordering, o ≠ .lt → (BitVec.ofInt 64 (ordCode o) == 0xffffffffffffffff#64) = false
  | .lt, h => absurd rfl h
  | .eq, _ => by decide
  | .gt, _ => by decide

/-- The new sign of the `MP_LT` branch. -/
theorem flip_sign (h : a.sign = Layout.mpZpos ∨ a.sign = Layout.mpNeg) :
    (if a.sign = 0 then 1 else 0) = (if a.sign = Layout.mpZpos then Layout.mpNeg else Layout.mpZpos) ∧
    ((if a.sign = 0 then 1 else 0) = Layout.mpZpos ∨ (if a.sign = 0 then 1 else 0) = Layout.mpNeg) := by
  simp only [Layout.mpZpos, Layout.mpNeg] at *; rcases h with h | h <;> simp [h]

/-- Same signs: the frame, `mp_cmp_mag(a, b)`, then `s_mp_sub` the right way round. The
`seqz` of the `MP_LT` branch is `hz`. -/
theorem same (hP : MpSub.Pre m sp pa adp pb bdp pc cdp a b c ra) (he : a.sign = b.sign)
    (hz : ∀ M, CodeAt M mpSubBase mpSubCode →
      Triple (At 0x80001f68#64 (l1L ra s0 sp pa pb pc b.sign) M v.keepR1 outp)
        (At 0x80001f6c#64 (l2L ra s0 sp pa pb pc (if b.sign = 0 then 1 else 0)) M v.keepR1 outp)) :
    Triple (At 0x80001ef4#64 (entry1 ra s0 v.s.s1 sp pa pb pc) m v.keepR1 outp)
      (MpSub.Ret m v outp sp pa adp pb bdp pc cdp a b c ra s0) := by
  have hsf := sfacts hP; have hff := ffacts hP; have := hP.sp_ge
  have hF1 : Frm ρ [R.stk] m (writeLog m (frameLog1 s0 v.s.s1 sp b.sign)) :=
    Frm.store (by simp only [LogIn, frameLog1, Iv.Sub, Bin.lay, and_true]; omega)
  have hF2 : Frm ρ [R.stk] m (writeLog (writeLog m (frameLog1 s0 v.s.s1 sp b.sign)) (frameLog2 ra sp pc)) :=
    (hF1.trans (Frm.store (w := R.stk) (by simp only [LogIn, frameLog2, Iv.Sub, Bin.lay, and_true]; omega))).mono
  have hrf : RFacts (writeLog (writeLog m (frameLog1 s0 v.s.s1 sp b.sign)) (frameLog2 ra sp pc))
      ra s0 v.s.s1 sp pc b.sign := by
    rw [← writeLog_append]
    exact { rs := hff.rs, sp_al := hP.sp_al, sp_ge := by omega
            s0_v := bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]; omega)
            s1_v := bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]; omega)
            sb_v := bytesT8_log _ _ 2 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]; omega)
            pc_v := bytesT8_log _ _ 3 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]; omega)
            ra_v := bytesT8_log _ _ 4 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]) }
  refine Triple.seq (d1_step ra s0 v.s.s1 v outp sp pa pb pc _ _ m (RO.of hP (Frm.refl _ m)).img.mpSub hsf hff he)
    (Triple.seq (d2_step ra s0 v.s.s1 v outp sp pa pb pc _ _ _ (RO.of hP hF1.mono).img.mpSub hff) ?_)
  generalize writeLog (writeLog m (frameLog1 s0 v.s.s1 sp b.sign)) (frameLog2 ra sp pc) = M2 at hF2 hrf ⊢
  have hro := RO.of hP hF2.mono
  have hcmp : CmpMag.Pre M2 pa adp pb bdp a b :=
    { ra := hro.ra_, rb := hro.rb, va := hP.va, vb := hP.vb, ga := hP.ga, gb := hP.gb, code := hro.img.mpCmpMag }
  refine Triple.seq (cmp_call ra v outp sp pa adp pb bdp a b M2 hro.img.mpSub hcmp) ?_
  rw [← cmpMag_eq hP.va hP.vb]
  have hfs := flip_sign (a := a) hP.va.sign_ok
  by_cases hlt : cmpMag a b = .lt
  · rw [hlt, show BitVec.ofInt 64 (ordCode .lt) = 0xffffffffffffffff#64 by decide]
    have hle : a.mag ≤ b.mag := by
      rw [cmpMag_eq hP.va hP.vb] at hlt; exact Nat.le_of_lt (Nat.compare_eq_lt.1 hlt)
    have hFs : Frm (Bin.lay 64 sp pb bdp pa adp pc cdp b a c) [R.stk] m M2 := hF2
    rw [← he] at hz hrf
    refine Triple.seq (bl_step ra s0 v.s.s1 v outp sp pa pb pc _ M2 hro.img.mpSub hrf)
      (Triple.seq (l1_step ra s0 v.s.s1 v outp sp pa pb pc _ M2 hro.img.mpSub hrf)
        (Triple.seq (hz _ hro.img.mpSub)
          (Triple.seq (l2_step ra s0 v.s.s1 v outp sp pa pb pc _ _ M2 hro.img.mpSub hrf (csign hP))
            (Triple.rmap (RetQ.unswap fun c' q => ⟨fun h => absurd he h, fun _ h => absurd hlt h,
                fun _ _ => by rw [← hfs.1]; exact q⟩)
              (tail (Pre.swap hP) hFs (MpInt.used_le_of_mag_le hP.vb.toShape hP.va hle) _ hfs.2)))))
  · have hle : b.mag ≤ a.mag := by
      rw [cmpMag_eq hP.va hP.vb] at hlt; exact Nat.le_of_not_lt fun h => hlt (Nat.compare_eq_lt.2 h)
    rw [← he] at hrf
    exact Triple.seq (b_step ra s0 v.s.s1 v outp sp pa pb pc _ _ M2 hro.img.mpSub hrf (ne_lt _ hlt))
      (Triple.seq (g_step ra s0 v.s.s1 v outp sp pa pb pc _ M2 hro.img.mpSub hrf (csign hP))
        (Triple.rmap (RetQ.ret fun c' q => ⟨fun h => absurd he h, fun _ _ => q, fun _ h => absurd h hlt⟩)
          (tail hP hF2 (MpInt.used_le_of_mag_le hP.va.toShape hP.vb hle) _ hP.va.sign_ok)))

end

/-- **`mp_sub` on the machine.** -/
theorem correct : Api.MpSub.Statement := by
  intro m v outp sp pa adp pb bdp pc cdp a b c ra s0 hP
  refine Triple.lmap (fun cf h => h.reshape (L' := entry1 ra s0 v.s.s1 sp pa pb pc) (K' := v.keepR1)
    (by simp [Fn.SSub.entryL, entry1, Abi.keepR, sKeepL])
    (by simp [Fn.SSub.entryL, Abi.keepR1, Abi.keepR, sKeepL])) ?_
  by_cases he : a.sign = b.sign
  · have hb2 : b.sign < 2 := by
      have := hP.vb.sign_ok; simp only [Layout.mpZpos, Layout.mpNeg] at this; omega
    exact same hP he fun M hc => z_step ra s0 v outp sp pa pb pc _ M hc hb2
  · exact Triple.rmap (RetQ.ret fun c' q => ⟨fun _ => q, fun h => absurd h he, fun h => absurd h he⟩)
      (diff hP he)

end Tom.Machine.Fn.MpSub
