import Tom.Machine.Fn.SubDPos
import Tom.Machine.Fn.AddDPos
import Tom.Machine.Kit.Copy
import Tom.Machine.Kit.StackCall

/-!
# `mp_sub_d` on the machine: the whole function

`a ≥ 0`: `pos_correct` (`Fn/SubDPos.lean`). `a < 0`: `neg`, the recursive
branch: a stack copy `a_ = a` with `MP_ZPOS` at `sp - 40` (`MpAt.copy`) and
the sign spilled at `sp - 64`, the call `mp_add_d(&a_, b, c)`
(`AddD.pos_correct` with stack depth 64 below this frame; its layout from
ours by `Sound.refine`), then `c->sign := MP_NEG` and `mp_clamp`
(`DRes.resign`). The stack depth is 128.
-/


namespace Tom.Machine.Fn.SubD

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api
open Tom.Machine.Api.Two (R isW ws Saved2 Tail2 Snap2 calleeR callee_sub calleeK bytesT8_log_out)

section
variable {F : Nat} {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp : Nat} {a : MpInt} {b : Nat}
  {c : MpInt} {ra s0 : BitVec 64}

local notation "ρ" => Two.lay F sp pa adp pc cdp a c

/-! ## `a < 0`: the call of `mp_add_d` -/

/-- The stack copy's memory. -/
abbrev m3Of (m : Mem) (ra s0 : BitVec 64) (sp pa : Nat) : Mem :=
  writeLog (m1Of m ra s0 sp) (cpLog sp (bytesT8 (m1Of m ra s0 sp) pa) (bytesT8 (m1Of m ra s0 sp) (pa + 8))
    (bytesT8 (m1Of m ra s0 sp) (pa + 16)))

theorem f3 (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    Frm ρ [R.stk] (m1Of m ra s0 sp) (m3Of m ra s0 sp pa) := by
  have := hP.sp_ge
  exact Frm.store (by simp only [LogIn, cpLog, Iv.Sub, Two.lay, and_true]; omega)

/-- The copy holds `a` with `MP_ZPOS`. -/
theorem copy_at (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 64 ≤ F) :
    MpAt (m3Of m ra s0 sp pa) (sp - 40) adp (a.withSign 0) := by
  have := hP.sp_ge
  have hro := ro1 (s0 := s0) hP hF
  have e : ∀ (M : Mem) (w0 w8 w16 : BitVec 64), writeLog M (cpLog sp w0 w8 w16) =
      writeLog (writeLog M [(sp - 32, 8, w8), (sp - 24, 8, w16), (sp - 64, 8, BitVec.ofNat 64 1), (sp - 40, 8, w0)])
        [(sp - 32, 4, 0#64)] :=
    fun M w0 w8 w16 => writeLog_append M [(sp - 32, 8, w8), (sp - 24, 8, w16), (sp - 64, 8, BitVec.ofNat 64 1),
      (sp - 40, 8, w0)] _
  refine hro.ra_.copy 0 ?_ ?_ ?_ ?_
  · exact bytesT8_log _ _ 3 _ _ rfl (by simp [cpLog, OutLRange]; omega)
  · rw [show sp - 40 + 16 = sp - 24 by omega]
    exact bytesT8_log _ _ 1 _ _ rfl (by simp [cpLog, OutLRange]; omega)
  · rw [show sp - 40 + 8 = sp - 32 by omega]
    dsimp only [m3Of]
    rw [e]
    exact bytesT4_sw_self _ _ 0 (by decide)
  · exact (f3 hP hF).keep hP.lay (ArrAt.reads (r := R.aD) (Iv.sub_self _)) hro.ra_.arr

/-- The callee's precondition. -/
theorem callee_pre (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 128 ≤ F) (hs : a.sign = 1) :
    Api.AddD.Pre 64 (m3Of m ra s0 sp pa) (sp - 64) (sp - 40) adp pc cdp (a.withSign 0) b c 0x800065ec#64 := by
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

/-- `mp_add_d(&a_, b, c)` at `65e8`, back at `65ec`. -/
theorem add_call (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 128 ≤ F) (hs : a.sign = 1) :
    Triple (At 0x800065e8#64 (cpL ra sp b pc) (m3Of m ra s0 sp pa) v.keepR outp)
      (fun cf => ∃ c'' M4, At 0x800065ec#64 (sdL sp pc) M4 v.keepR outp cf ∧
        Api.AddD.Post 64 (m3Of m ra s0 sp pa) (sp - 64) (sp - 40) adp pc cdp (a.withSign 0) b c c'' M4) := by
  have hc := (callee_pre (s0 := s0) hP hF hs).img
  refine Triple.seq (jal_at (pc := 0x800065e8#64) (w := 0x849fe0ef#32) (imm := 0x1fe848#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 64)), (8, BitVec.ofNat 64 pc), (10, BitVec.ofNat 64 (sp - 40)),
        (11, BitVec.ofNat 64 b), (12, BitVec.ofNat 64 pc)])
      (hc.mpSubD.word (a := (0x800065e8#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [cpL]) (by simp [keysG]) (by simp [Abi.keepR, sKeepL, keysG])) ?_
  refine Triple.dimap (fun cf h => ?_) (fun cf ⟨c'', M4, hat, hpost⟩ => ⟨c'', M4, hat.reshape ?_ ?_, hpost⟩)
    (AddD.pos_correct (v := calleeAbi v sp pc) (outp := outp) (s0 := BitVec.ofNat 64 pc) (by decide)
      (callee_pre hP hF hs) rfl)
  · have hpc : (0x800065e8#64 : BitVec 64) + Functions.sign_extend (m := 64) (0x1fe848#21) = 0x80004e30#64 := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [AddD.entryL, Sail.BitVec.addInt]
    · simp [Abi.keepR, calleeAbi, sKeepL]
  · simp [sdL]
  · simp [Abi.keepR, calleeAbi, sKeepL]

/-- `a < 0`: `c := -(|a| + b)` by `mp_add_d` on a copy. -/
theorem neg (hP : Api.SubD.Pre F m sp pa adp pc cdp a b c ra) (hF : 128 ≤ F) (hs : a.sign = 1) :
    Triple (At 0x800064c8#64 (pL ra sp pa b pc a.used) (m1Of m ra s0 sp) v.keepR outp)
      (RetD F m v outp sp pa adp pc cdp a c ra s0 (addDDigits a b) (a.used + 1) 1) := by
  have hb := hP.hb; rw [radix_eq] at hb
  have := hP.sp_ge; have hroom := hP.room; have hal := hP.sc.alloc_lt
  have hro1 := ro1 (s0 := s0) hP (by omega)
  have hsa := hP.lay.disj (r := R.stk) (s := R.aS)
  have hsc := hP.lay.disj (r := R.stk) (s := R.bS)
  have hsd := hP.lay.disj (r := R.stk) (s := R.bD)
  have hstc := hP.lay.sub (r := R.stk) (s := R.code) (Iv.sub_self _) code_sub
  simp only [Iv.Disj, Disj, Two.lay] at hsa hsc hsd hstc
  have hrs := hP.rs
  have hrs64 : Ram (sp - 64) 64 := ⟨by have := hrs.lo_ge; omega, by have := hrs.hi_le; omega, by have := hrs.off; omega⟩
  have hcp : CpFacts (m1Of m ra s0 sp) sp pa :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
      rs := hrs64, sp_al := hP.sp_al, sp_ge := by omega
      sa_v := by rw [← hs]; simpa [Layout.offSign] using hro1.ra_.sign
      s_a := by omega, code_s := by omega }
  refine Triple.seq (n_step ra v outp sp pa b pc a.used (m1Of m ra s0 sp) hro1.img.mpSubD hcp)
    (Triple.seq (add_call hP hF hs) ?_)
  intro cf ⟨c'', M4, hat, hpost⟩
  have hF13 := (f1 (s0 := s0) hP (by omega)).trans (f3 hP (by omega))
  have hF4 : Frm ρ ws (m3Of m ra s0 sp pa) M4 := (Frm.push calleeR (callee_sub hF this) hpost.frame).mono
  have hspec := hpost.addd
  have hav : (a.withSign 0).Valid :=
    { len := hP.va.len, used_le := hP.va.used_le, alloc_lt := hP.va.alloc_lt, digit_lt := hP.va.digit_lt,
      high_zero := hP.va.high_zero, top := hP.va.top, sign_ok := Or.inl rfl, zero_pos := fun _ => rfl }
  have hcsh : c''.Valid := (AddDPost.spec hav hP.hb hroom hal hspec).1
  have hres := hspec.pos rfl
  have hcal : c''.alloc = c.alloc := hres.alloc
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
  have hsp4 : bytesT8 M4 (sp - 64) = BitVec.ofNat 64 1 :=
    hF4k.keep hK (Reads.w8 (r := Two.K.sl) (by simp only [Iv.Sub, Two.klay]; omega))
      (bytesT8_log _ _ 2 _ _ rfl (by simp [cpLog, OutLRange]; omega))
  have himg4 : Img M4 := ((hF13.trans hF4).mono (ws' := ws)).keep hP.lay
    (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
  -- `MP_OKAY` spilled, `c->sign := MP_NEG`
  have hn2 := n2_step v outp sp pc M4 himg4.mpSubD hrs64 hP.sp_al (by omega) (by omega)
    (by simpa [Layout.sizeofMpInt] using hP.gc.st) hP.gc.st_al (cfacts hP).code_c hsp4 (by omega)
  rw [show writeLog M4 [(sp - 64, 8, 0#64), (pc + 8, 4, BitVec.ofNat 64 1)] =
      writeLog (writeLog M4 [(sp - 64, 8, 0#64)]) [(pc + 8, 4, BitVec.ofNat 64 1)] from
    writeLog_append M4 [(sp - 64, 8, 0#64)] _] at hn2
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
  refine Triple.seq hn2 (Triple.seq (clamp_call2 v outp sp pc cdp _ _ himg5.mpSubD hcp) ?_) cf hat
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
  refine Triple.rmap (fun cf h => ⟨c', M6, h, hpost6.repr, hres.resign 1 hpost6.clamp, hF16⟩)
    (nr_step ra s0 v outp sp M6 ((hF16.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img).mpSubD)
      hrf he) cf hat6

end

/-- **`mp_sub_d` on the machine.** -/
theorem correct : Api.SubD.Statement := by
  intro m v outp sp pa adp pc cdp a b c ra s0 hP
  rcases sign_cases hP.va.sign_ok with h0 | h1
  · exact pos_correct (by decide) hP h0
  have hpos : a.sign ≠ Layout.mpZpos := by rw [h1]; decide
  refine Triple.seq (p_step ra s0 v outp sp pa b pc a.used c.alloc m hP.img.mpSubD (pfacts hP (by decide))) ?_
  exact Triple.rmap (fun cf ⟨c', M, hat, ho⟩ => ⟨c', M, hat, ho.repr,
      ⟨fun _ => ho.res, fun h => absurd h hpos, fun h => absurd h hpos⟩, ho.frame⟩)
    (neg hP (Nat.le_refl _) h1)

end Tom.Machine.Fn.SubD
