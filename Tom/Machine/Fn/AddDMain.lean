import Tom.Machine.Fn.AddDPos
import Tom.Machine.Fn.SubDPos
import Tom.Machine.Kit.Copy
import Tom.Machine.Kit.StackCall

/-!
# `mp_add_d` on the machine: the whole function

`a ≥ 0`: `pos_correct` (`Fn/AddDPos.lean`). `a < 0`, `|a| < b`: `small`,
the same tail. `a < 0`, `|a| ≥ b`: `big`, the recursive branch: a stack copy
`a_ = a` with `MP_ZPOS` at `sp - 40` (`MpAt.copy`), the call
`mp_sub_d(&a_, b, c)` (`SubD.pos_correct` with stack depth 64 below this
frame; its layout from ours by `Sound.refine`: the callee's stack and its
`a_` both lie in our stack, apart), then `c->sign := MP_NEG` and `mp_clamp`
(`DRes.resign`). The stack depth is 128.
-/


namespace Tom.Machine.Fn.AddD

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api
open Tom.Machine.Api.Two (R isW ws Saved2 Tail2 Snap2 calleeR callee_sub calleeK bytesT8_log_out)

section
variable {F : Nat} {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat}
  {c : MpInt} {ra s0 : BitVec 64}

local notation "ρ" => Two.lay F sp pa adp pc cdp a c

/-! ## `a < 0`, `|a| < b` -/

theorem small_tail (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) (d : Nat)
    (hd : d < 2 ^ 32) (hdd : d = smallDigits a b 0) :
    Tail2 ρ m (writeLog (m1Of m ra s0 sp) [(pc, 4, BitVec.ofNat 64 1), (cdp, 4, BitVec.ofNat 64 d)])
      ra s0 sp pc cdp 1 c.alloc c.sign (ovl (smallDigits a b) c.digit 1) := by
  have := hP.sp_ge; have := hP.room; have := hP.sc.alloc_lt
  have hc1 := rc1 (s0 := s0) hP hF
  have hS : Frm ρ [R.bS] (m1Of m ra s0 sp) (writeLog (m1Of m ra s0 sp) [(pc, 4, BitVec.ofNat 64 1)]) :=
    Frm.sw (Iv.sub_pre (by decide))
  have hA0 : ArrFrm ρ R.bD (writeLog (m1Of m ra s0 sp) [(pc, 4, BitVec.ofNat 64 1)])
      (writeLog (m1Of m ra s0 sp) [(pc, 4, BitVec.ofNat 64 1)]) cdp c.alloc (ovl (smallDigits a b) c.digit 0) :=
    ArrFrm.init (Iv.sub_self _)
      (by rw [ovl_zero]; exact hS.keep hP.lay (ArrAt.reads (r := R.bD) (Iv.sub_self _)) hc1.arr)
  have hA := hA0.step (i := 0) (v := d) (by omega) hd hdd
  rw [show cdp + 4 * 0 = cdp by omega] at hA
  have e : writeLog (m1Of m ra s0 sp) [(pc, 4, BitVec.ofNat 64 1), (cdp, 4, BitVec.ofNat 64 d)] =
      writeLog (writeLog (m1Of m ra s0 sp) [(pc, 4, BitVec.ofNat 64 1)]) [(cdp, 4, BitVec.ofNat 64 d)] :=
    writeLog_append _ [(pc, 4, BitVec.ofNat 64 1)] _
  rw [e]
  exact { fr := ((f1 hP hF).trans (hS.trans hA.fr)).mono
          sv := ((sv1 hP hF).keep hP.lay (by omega) hP.sp_ge hS).keep hP.lay (by omega) hP.sp_ge hA.fr
          hdr := hA.fr.keep hP.lay (HdrAt.reads (r := R.bS) (Iv.sub_self _)) (hc1.hdr.set_used 1 (by decide))
          arr := hA.arr }

/-- `a < 0`, `|a| < b`: `c := b - |a|`. -/
theorem small (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) (hs : a.sign = 1)
    (hsm : AddDSmall a b) :
    Triple (At 0x80004e54#64 (pL ra sp pa b pc a.used) (m1Of m ra s0 sp) v.keepR outp)
      (RetD F m v outp sp pa adp pc cdp a c ra s0 (smallDigits a b) 1 0) := by
  have hb := hP.hb; rw [radix_eq] at hb
  have hcu := hP.sc.used_le; have hroom := hP.room
  have hu1 : a.used = 1 := by
    have := hP.va.zero_pos; have := hsm.1
    rcases Nat.lt_or_ge a.used 1 with h | h
    · have h0 := this; rw [hs] at *; simp [Layout.mpZpos] at *; omega
    · omega
  have hH := hfacts (s0 := s0) hP hF
  rw [hs] at hH
  have hro1 := ro1 (s0 := s0) hP hF
  have hx := xfacts hP hro1 (by omega)
  have hrc : Ram cdp (4 * c.alloc) := by simpa [Layout.sizeofDigit] using hP.gc.ds
  have hsf : SFacts (m1Of m ra s0 sp) pa pc adp cdp (a.digit 0) :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rc := by simpa [Layout.sizeofMpInt] using hP.gc.st
      pc_al := hP.gc.st_al
      ua_v := by rw [← hu1]; simpa [Layout.offUsed] using hro1.ra_.used
      xf := hx
      rd := ⟨by have := hrc.lo_ge; omega, by have := hrc.hi_le; omega, by have := hrc.off; omega⟩
      d_al := hP.gc.ds_al
      ac := disj_or (hP.lay.sub (r := R.aS) (s := R.bS) (I := ⟨pa, 4⟩) (J := ⟨pc, 4⟩)
        (Iv.sub_pre (by decide)) (Iv.sub_pre (by decide)))
      dc := disj_or (hP.lay.sub (r := R.aD) (s := R.bS) (I := ⟨adp, 4⟩) (J := ⟨pc, 4⟩)
        (Iv.sub_pre (by have := hP.va.used_le; omega)) (Iv.sub_pre (by decide)))
      code_c := code_c hP
      code_d := disj_or (hP.lay.sub (r := R.bD) (s := R.code) (I := ⟨cdp, 4⟩)
        (Iv.sub_pre (by omega)) code_sub) }
  have hd : b - a.digit 0 = smallDigits a b 0 := by simp [smallDigits]
  refine Triple.seq (nil_post (s1_step ra v outp sp pa b pc a.used c.used adp cdp _ _ hro1.img.mpAddD hH hx
    hsm.1 hb hsm.2)) ?_
  refine Triple.seq (Triple.rmap (fun cf h => (⟨_, small_tail hP hF _ (by omega) hd, h⟩ :
      TSt F m v outp sp pa adp pc cdp a c ra s0 0x80004ec4#64 (tL ra sp pc c.used cdp 1) 1 c.sign
        (ovl (smallDigits a b) c.digit 1) cf))
    (s2_step ra v outp sp pa b pc c.used adp cdp _ (m1Of m ra s0 sp) hro1.img.mpAddD hsf hb hsm.2)) ?_
  exact tail hP hF (smallDigits_lt hP.hb) (smallDigits_high a b) (by omega)

/-! ## `a < 0`, `|a| ≥ b`: the call of `mp_sub_d` -/

/-- The stack copy's memory. -/
abbrev m3Of (m : Mem) (ra s0 : BitVec 64) (sp pa : Nat) : Mem :=
  writeLog (m1Of m ra s0 sp) (cpLog sp (bytesT8 (m1Of m ra s0 sp) pa) (bytesT8 (m1Of m ra s0 sp) (pa + 8))
    (bytesT8 (m1Of m ra s0 sp) (pa + 16)))

theorem f3 (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    Frm ρ [R.stk] (m1Of m ra s0 sp) (m3Of m ra s0 sp pa) := by
  have := hP.sp_ge
  exact Frm.store (by simp only [LogIn, cpLog, Iv.Sub, Two.lay, and_true]; omega)

/-- The copy holds `a` with `MP_ZPOS`. -/
theorem copy_at (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    MpAt (m3Of m ra s0 sp pa) (sp - 40) adp (a.withSign 0) := by
  have := hP.sp_ge
  have hro := ro1 (s0 := s0) hP hF
  have e : ∀ (M : Mem) (w0 w8 w16 : BitVec 64), writeLog M (cpLog sp w0 w8 w16) =
      writeLog (writeLog M [(sp - 32, 8, w8), (sp - 24, 8, w16), (sp - 40, 8, w0)]) [(sp - 32, 4, 0#64)] :=
    fun M w0 w8 w16 => writeLog_append M [(sp - 32, 8, w8), (sp - 24, 8, w16), (sp - 40, 8, w0)] _
  refine hro.ra_.copy 0 ?_ ?_ ?_ ?_
  · exact bytesT8_log _ _ 2 _ _ rfl (by simp [cpLog, OutLRange]; omega)
  · rw [show sp - 40 + 16 = sp - 24 by omega]
    exact bytesT8_log _ _ 1 _ _ rfl (by simp [cpLog, OutLRange]; omega)
  · rw [show sp - 40 + 8 = sp - 32 by omega]
    dsimp only [m3Of]
    rw [e]
    exact bytesT4_sw_self _ _ 0 (by decide)
  · exact (f3 hP hF).keep hP.lay (ArrAt.reads (r := R.aD) (Iv.sub_self _)) hro.ra_.arr

/-- The callee's precondition. -/
theorem callee_pre (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 128 ≤ F) (hs : a.sign = 1) :
    Api.SubD.Pre 64 (m3Of m ra s0 sp pa) (sp - 64) (sp - 40) adp pc cdp (a.withSign 0) b c 0x80004fa4#64 := by
  have := hP.sp_ge; have hsa := hP.lay.disj (r := R.stk) (s := R.aD)
  simp only [Iv.Disj, Disj, Two.lay] at hsa
  have hF3 := (f1 (s0 := s0) hP (by omega)).trans (f3 hP (by omega))
  have hrs := hP.rs
  exact { ra_ := copy_at hP (by omega)
          rc := hF3.keep hP.lay (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hP.rc
          va := { len := hP.va.len, used_le := hP.va.used_le, alloc_lt := hP.va.alloc_lt,
                  digit_lt := hP.va.digit_lt, high_zero := hP.va.high_zero, top := hP.va.top,
                  sign_ok := Or.inl rfl, zero_pos := fun _ => rfl }
          sc := hP.sc, hb := hP.hb
          ga := { st := ⟨by have := hrs.lo_ge; simp [Layout.sizeofMpInt]; omega,
                    by have := hrs.hi_le; simp [Layout.sizeofMpInt]; omega,
                    by have := hrs.off; simp [Layout.sizeofMpInt]; omega⟩
                  st_al := by have := hP.sp_al; omega
                  ds := hP.ga.ds, ds_al := hP.ga.ds_al
                  disj := by simp only [Layout.sizeofMpInt, Layout.sizeofDigit, MpInt.withSign] at *; omega }
          gc := hP.gc, room := hP.room
          rs := ⟨by have := hrs.lo_ge; omega, by have := hrs.hi_le; omega, by have := hrs.off; omega⟩
          sp_al := by have := hP.sp_al; omega
          sp_ge := by omega
          ra_al := by decide
          img := hF3.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
          lay := Two.callee_sound hP.lay hF hP.sp_ge }

/-- The callee-saved registers `mp_sub_d` sees. -/
theorem sub_call (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 128 ≤ F) (hs : a.sign = 1) :
    Triple (At 0x80004fa0#64 (cpL ra sp b pc) (m3Of m ra s0 sp pa) v.keepR outp)
      (fun cf => ∃ c'' M4, At 0x80004fa4#64 (sdL sp pc) M4 v.keepR outp cf ∧
        Api.SubD.Post 64 (m3Of m ra s0 sp pa) (sp - 64) (sp - 40) adp pc cdp (a.withSign 0) b c c'' M4) := by
  have hc := (callee_pre (s0 := s0) hP hF hs).img
  refine Triple.seq (jal_at (pc := 0x80004fa0#64) (w := 0x504010ef#32) (imm := 0x01504#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 (sp - 40)),
        (11, BitVec.ofNat 64 b), (12, BitVec.ofNat 64 pc)])
      (hc.mpAddD.word (a := (0x80004fa0#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [cpL]) (by simp [keysG]) (by simp [Abi.keepR, sKeepL, keysG])) ?_
  refine Triple.dimap (fun cf h => ?_) (fun cf ⟨c'', M4, hat, hpost⟩ => ⟨c'', M4, hat.reshape ?_ ?_, hpost⟩)
    (SubD.pos_correct (v := calleeAbi v sp pc) (outp := outp) (s0 := BitVec.ofNat 64 pc) (by decide)
      (callee_pre hP hF hs) rfl)
  · have hpc : (0x80004fa0#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x01504#21) = 0x800064a4#64 := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [SubD.entryL, Sail.BitVec.addInt]
    · simp [Abi.keepR, calleeAbi, sKeepL]
  · simp [sdL]
  · simp [Abi.keepR, calleeAbi, sKeepL]

/-- The digits of the recursive branch: those of `mp_sub_d(|a|, b)`. -/
theorem big_res {c'' c' : MpInt} (ha : a.Valid) (hs : a.sign = 1) (hnsm : ¬ AddDSmall a b)
    (hsub : SubDPost (a.withSign 0) b c c'') (hcl : ClampPost (c''.withSign 1) c') :
    DRes c c' (subDDigits a b) a.used 1 := by
  have hd0 : (a.withSign 0).digit 0 = a.digit 0 := rfl
  have hu0 : (a.withSign 0).used = a.used := rfl
  by_cases hsm : SubDSmall (a.withSign 0) b
  · have h := (hsub.small rfl hsm).resign 1 hcl
    have hu1 : a.used = 1 ∧ a.digit 0 = b := by
      rcases hsm with ⟨h1, h2⟩ | h0
      · rw [hu0] at h1; rw [hd0] at h2
        have : ¬ (a.used ≤ 1 ∧ a.digit 0 < b) := hnsm
        exact ⟨h1, by omega⟩
      · exfalso; rw [hu0] at h0; have := ha.zero_pos h0; rw [hs] at this; exact absurd this (by decide)
    have he : smallDigits (a.withSign 0) b = subDDigits a b := by
      funext i
      by_cases hi : i = 0
      · subst hi
        simp only [smallDigits, subDDigits, if_pos (show (0 : Nat) < a.used by omega), if_true,
          subDBorrow_zero]
        rw [hd0, hu1.2, radix_eq]; omega
      · simp only [smallDigits, subDDigits, if_neg hi]
        rw [if_neg (by omega)]
    rw [hu1.1]
    exact h.congr he
  · exact (hsub.big rfl hsm).resign 1 hcl

/-- `a < 0`, `|a| ≥ b`: `c := -(|a| - b)` by `mp_sub_d` on a copy. -/
theorem big (hP : Api.AddD.Pre F m sp pa adp pc cdp a b c ra) (hF : 128 ≤ F) (hs : a.sign = 1)
    (hnsm : ¬ AddDSmall a b) :
    Triple (At 0x80004e54#64 (pL ra sp pa b pc a.used) (m1Of m ra s0 sp) v.keepR outp)
      (RetD F m v outp sp pa adp pc cdp a c ra s0 (subDDigits a b) a.used 1) := by
  have hb := hP.hb; rw [radix_eq] at hb
  have := hP.sp_ge; have hroom := hP.room; have hal := hP.sc.alloc_lt
  have hH := hfacts (s0 := s0) hP (by omega)
  rw [hs] at hH
  have hro1 := ro1 (s0 := s0) hP (by omega)
  have hsa := hP.lay.disj (r := R.stk) (s := R.aS)
  have hsc := hP.lay.disj (r := R.stk) (s := R.bS)
  have hsd := hP.lay.disj (r := R.stk) (s := R.bD)
  have hstc := hP.lay.sub (r := R.stk) (s := R.code) (Iv.sub_self _) code_sub
  simp only [Iv.Disj, Disj, Two.lay] at hsa hsc hsd hstc
  have hrs := hP.rs
  have hrs64 : Ram (sp - 64) 64 := ⟨by have := hrs.lo_ge; omega, by have := hrs.hi_le; omega, by have := hrs.off; omega⟩
  -- to `4f78`
  have hpre : Triple (At 0x80004e54#64 (pL ra sp pa b pc a.used) (m1Of m ra s0 sp) v.keepR outp)
      (At 0x80004f78#64 (gL ra sp pa b pc) (m1Of m ra s0 sp) v.keepR outp) := by
    by_cases h2 : 1 < a.used
    · exact nil_post (g1_step ra v outp sp pa b pc a.used c.used adp cdp _ hro1.img.mpAddD hH h2)
    · have hx := xfacts hP hro1 (by
        have := hP.va.zero_pos
        rcases Nat.eq_zero_or_pos a.used with h | h
        · have h0 := this h; rw [hs] at h0; exact absurd h0 (by decide)
        · exact h)
      exact nil_post (g2_step ra v outp sp pa b pc a.used c.used adp cdp _ _ hro1.img.mpAddD hH hx (by omega) hb
        (Nat.le_of_not_lt fun h => hnsm ⟨by omega, h⟩))
  have hcp : CpFacts sp pa :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rs := hrs64, sp_al := hP.sp_al, sp_ge := by omega
      s_a := by omega, code_s := by omega }
  refine Triple.seq hpre (Triple.seq (cp_step ra v outp sp pa b pc (m1Of m ra s0 sp) hro1.img.mpAddD hcp)
    (Triple.seq (sub_call hP hF hs) ?_))
  intro cf ⟨c'', M4, hat, hpost⟩
  have hF13 := (f1 (s0 := s0) hP (by omega)).trans (f3 hP (by omega))
  have hF4 : Frm ρ ws (m3Of m ra s0 sp pa) M4 := (Frm.push calleeR (callee_sub hF this) hpost.frame).mono
  have hspec := hpost.subd
  have hcsh : c''.Valid := (SubDPost.spec (a := a.withSign 0)
    { len := hP.va.len, used_le := hP.va.used_le, alloc_lt := hP.va.alloc_lt, digit_lt := hP.va.digit_lt,
      high_zero := hP.va.high_zero, top := hP.va.top, sign_ok := Or.inl rfl, zero_pos := fun _ => rfl }
    hP.hb hroom hal hspec).1
  have hcal : c''.alloc = c.alloc := by
    by_cases hsm : SubDSmall (a.withSign 0) b
    · exact (hspec.small rfl hsm).alloc
    · exact (hspec.big rfl hsm).alloc
  -- saved registers survive the callee (its frame is below ours)
  have hK := Two.ksound hP.lay (by omega) this
  have hF4k := Frm.push calleeK (Two.callee_subK (pa := pa) hF this) hpost.frame
  have hsv1 := sv1 (s0 := s0) hP (by omega)
  have hra3 : bytesT8 (m3Of m ra s0 sp pa) (sp - 8) = ra := by
    rw [bytesT8_log_out _ _ _ (by simp [cpLog, OutLRange]; omega)]; exact hsv1.ra_v
  have hs03 : bytesT8 (m3Of m ra s0 sp pa) (sp - 16) = s0 := by
    rw [bytesT8_log_out _ _ _ (by simp [cpLog, OutLRange]; omega)]; exact hsv1.s0_v
  have hra4 : bytesT8 M4 (sp - 8) = ra :=
    hF4k.keep hK (Reads.w8 (r := Two.K.sv) (by simp only [Iv.Sub, Two.klay]; omega)) hra3
  have hs04 : bytesT8 M4 (sp - 16) = s0 :=
    hF4k.keep hK (Reads.w8 (r := Two.K.sv) (by simp only [Iv.Sub, Two.klay]; omega)) hs03
  have himg4 : Img M4 := ((hF13.trans hF4).mono (ws' := ws)).keep hP.lay
    (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
  -- `MP_OKAY` spilled, `c->sign := MP_NEG`
  have hb3 := b3_step v outp sp pc M4 himg4.mpAddD hrs64 hP.sp_al (by omega) (by omega)
    (by simpa [Layout.sizeofMpInt] using hP.gc.st) hP.gc.st_al (code_c hP)
  rw [show writeLog M4 [(sp - 64, 8, 0#64), (pc + 8, 4, BitVec.ofNat 64 1)] =
      writeLog (writeLog M4 [(sp - 64, 8, 0#64)]) [(pc + 8, 4, BitVec.ofNat 64 1)] from
    writeLog_append M4 [(sp - 64, 8, 0#64)] _] at hb3
  have hF5a : Frm ρ [R.stk] M4 (writeLog M4 [(sp - 64, 8, 0#64)]) :=
    Frm.store (by simp only [LogIn, Iv.Sub, Two.lay, and_true]; omega)
  have hF5b : Frm ρ [R.bS] (writeLog M4 [(sp - 64, 8, 0#64)])
      (writeLog (writeLog M4 [(sp - 64, 8, 0#64)]) [(pc + 8, 4, BitVec.ofNat 64 1)]) :=
    Frm.sw (by simp only [Iv.Sub, Two.lay]; omega)
  have hgc : MpGeom pc cdp c''.alloc := by rw [hcal]; exact hP.gc
  have hrc5 : MpAt (writeLog (writeLog M4 [(sp - 64, 8, 0#64)]) [(pc + 8, 4, BitVec.ofNat 64 1)]) pc cdp
      (c''.withSign 1) :=
    (hF5a.keep hP.lay (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (by rw [hcal]; exact Iv.sub_self _))
      hpost.repr).set_sign hgc 1 (by decide)
  have hF15 := ((hF13.trans hF4).trans (hF5a.trans hF5b)).mono (ws' := ws)
  have himg5 := hF15.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
  have hcp : Clamp.Pre (writeLog (writeLog M4 [(sp - 64, 8, 0#64)]) [(pc + 8, 4, BitVec.ofNat 64 1)]) pc cdp
      (c''.withSign 1) :=
    { repr := hrc5
      shape := ⟨hcsh.len, hcsh.used_le, hcsh.alloc_lt, hcsh.digit_lt, hcsh.high_zero⟩
      geom := hgc, code := himg5.mpClamp
      code_off := disj_or (hP.lay.sub (r := R.bS) (s := R.code) (Iv.sub_self _) clamp_sub) }
  refine Triple.seq hb3 (Triple.seq (clamp_call2 v outp sp pc cdp _ _ himg5.mpAddD hcp) ?_) cf hat
  intro cf ⟨c', M6, hat6, hpost6⟩
  have hF5ak : Frm (Two.klay F sp pa adp pc cdp a c) [Two.K.sl] M4 (writeLog M4 [(sp - 64, 8, 0#64)]) :=
    Frm.store (by simp only [LogIn, Iv.Sub, Two.klay, and_true]; omega)
  have hF5bk : Frm (Two.klay F sp pa adp pc cdp a c) [Two.K.bS] (writeLog M4 [(sp - 64, 8, 0#64)])
      (writeLog (writeLog M4 [(sp - 64, 8, 0#64)]) [(pc + 8, 4, BitVec.ofNat 64 1)]) :=
    Frm.sw (by simp only [Iv.Sub, Two.klay]; omega)
  have hF6k : Frm (Two.klay F sp pa adp pc cdp a c) [Two.K.bS]
      (writeLog (writeLog M4 [(sp - 64, 8, 0#64)]) [(pc + 8, 4, BitVec.ofNat 64 1)]) M6 :=
    Frm.call (w := Two.K.bS) hpost6.frame (Iv.sub_pre (by decide))
  have hF46 := (hF5ak.trans hF5bk).trans hF6k
  have hrf : RFacts M6 ra s0 sp :=
    { rs := hrs64, sp_al := hP.sp_al, sp_ge := by omega
      ra_v := hF46.keep hK (Reads.w8 (r := Two.K.sv) (by simp only [Iv.Sub, Two.klay]; omega)) hra4
      s0_v := hF46.keep hK (Reads.w8 (r := Two.K.sv) (by simp only [Iv.Sub, Two.klay]; omega)) hs04
      ra_al := hP.ra_al }
  have he : bytesT8 M6 (sp - 64) = 0#64 :=
    (hF5bk.trans hF6k).keep hK (Reads.w8 (r := Two.K.sl) (by simp only [Iv.Sub, Two.klay]; omega))
      (bytesT8_sd_self _ _ _)
  have hF6 : Frm ρ [R.bS] _ M6 := Frm.call (w := R.bS) hpost6.frame (Iv.sub_pre (by decide))
  have hF16 := (hF15.trans hF6).mono (ws' := ws)
  refine Triple.rmap (fun cf h => ⟨c', M6, h, hpost6.repr, big_res hP.va hs hnsm hspec hpost6.clamp, hF16⟩)
    (br_step ra s0 v outp sp M6 ((hF16.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img).mpAddD)
      hrf he) cf hat6

end

/-- **`mp_add_d` on the machine.** -/
theorem correct : Api.AddD.Statement := by
  intro m v outp sp pa adp pc cdp a b c ra s0 hP
  rcases sign_cases hP.va.sign_ok with h0 | h1
  · exact pos_correct (by decide) hP h0
  have hpos : a.sign ≠ Layout.mpZpos := by rw [h1]; decide
  refine Triple.seq (p_step ra s0 v outp sp pa b pc a.used c.alloc m hP.img.mpAddD (pfacts hP (by decide))) ?_
  by_cases hsm : AddDSmall a b
  · exact Triple.rmap (fun cf ⟨c', M, hat, ho⟩ => ⟨c', M, hat, ho.repr,
      ⟨fun h => absurd h hpos, fun _ h => absurd hsm h, fun _ _ => ho.res⟩, ho.frame⟩)
      (small hP (by decide) h1 hsm)
  · exact Triple.rmap (fun cf ⟨c', M, hat, ho⟩ => ⟨c', M, hat, ho.repr,
      ⟨fun h => absurd h hpos, fun _ _ => ho.res, fun _ h => absurd h hsm⟩, ho.frame⟩)
      (big hP (Nat.le_refl _) h1 hsm)

end Tom.Machine.Fn.AddD
