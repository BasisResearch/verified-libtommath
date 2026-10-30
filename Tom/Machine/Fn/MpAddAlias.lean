import Tom.Machine.Fn.BinATail
import Tom.Machine.Fn.MpAddMain
import Tom.Machine.Api.MpAddAlias

/-!
# `mp_add` in place on the machine

`Api.MpAddAlias.StatementCA`/`StatementCB`. The part both share is
`Alias.skel`: `mp_add`'s own segments (the sign loads, the frame,
`mp_cmp_mag(a, b)`, the branch, the sign store) over `BinA`'s regions with
either write set (`isW` with the stack written; the read facts by
`Frm.keep` with `Misses` from `isW .stk`), its three tail calls left as
hypotheses on the memory at the jump. `c = a` and `c = b` give them by the
in-place tail calls of `Fn/BinATail.lean`.
-/

namespace Tom.Machine.Fn.MpAdd

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api Tom.Machine.Api.BinA

namespace Alias

section
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc : Nat} {a b : MpInt}
  {ra s0 : BitVec 64}

local notation "ρ" => BinA.lay 64 sp pa adp pb bdp a b

/-- **`mp_add`'s own code, for either destination.** From the entry, with the
operands valid and the destination's sign slot at `pc`: the sign loads; same
signs, the store `c->sign := a->sign` and the jump to `s_mp_add(a, b, c)`
(`hsame`); otherwise the frame, `mp_cmp_mag(a, b)`, and the store and jump to
`s_mp_sub(b, a, c)` (`hlt`) or `s_mp_sub(a, b, c)` (`hge`) from a memory
changed only in the stack. -/
theorem skel {isW : BinA.R → Bool} (hS : Sound ρ isW) (hstk : isW BinA.R.stk = true)
    (hB : Base m 64 sp pa adp pb bdp a b ra) (va : a.Valid) (vb : b.Valid) (hcs : CSign pc)
    {Q : Vsa.Machine.Config → Prop}
    (hsame : a.sign = b.sign → Triple (At 0x8000219c#64 (entry1 ra s0 v.s.s1 sp pa pb pc)
      (writeLog m [(pc + 8, 4, BitVec.ofNat 64 a.sign)]) v.keepR1 outp) Q)
    (hlt : a.sign ≠ b.sign → cmpMag a b = .lt → ∀ M, Frm ρ [BinA.R.stk] m M →
      Triple (At 0x80004564#64 (entry1 ra s0 v.s.s1 sp pb pa pc)
        (writeLog M [(pc + 8, 4, BitVec.ofNat 64 b.sign)]) v.keepR1 outp) Q)
    (hge : a.sign ≠ b.sign → cmpMag a b ≠ .lt → ∀ M, Frm ρ [BinA.R.stk] m M →
      Triple (At 0x80004564#64 (entry1 ra s0 v.s.s1 sp pa pb pc)
        (writeLog M [(pc + 8, 4, BitVec.ofNat 64 a.sign)]) v.keepR1 outp) Q) :
    Triple (At 0x80000608#64 (entry1 ra s0 v.s.s1 sp pa pb pc) m v.keepR1 outp) Q := by
  have := hB.sp_ge
  have hm : Misses isW [BinA.R.code] [BinA.R.stk] = true := by simp [Misses, Sep, hstk]
  have hmA : Misses isW [BinA.R.aS, BinA.R.aD] [BinA.R.stk] = true := by simp [Misses, Sep, hstk]
  have hmB : Misses isW [BinA.R.bS, BinA.R.bD] [BinA.R.stk] = true := by simp [Misses, Sep, hstk]
  have himg : ∀ M, Frm ρ [BinA.R.stk] m M → Img M := fun M hF =>
    hF.keep hS (Img.reads (r := BinA.R.code) (Iv.sub_self _)) hB.img hm
  have ha := va.sign_ok; have hb := vb.sign_ok
  have hsf : SFacts m pa pb a.sign b.sign :=
    { ra_ := by simpa [Layout.sizeofMpInt] using hB.ga.st
      rb := by simpa [Layout.sizeofMpInt] using hB.gb.st
      sa_v := by simpa [Layout.offSign] using hB.ra_.sign
      sb_v := by simpa [Layout.offSign] using hB.rb.sign
      sa_lt := by simp only [Layout.mpZpos, Layout.mpNeg] at ha; omega
      sb_lt := by simp only [Layout.mpZpos, Layout.mpNeg] at hb; omega }
  by_cases he : a.sign = b.sign
  · exact Triple.seq (s_step ra s0 v.s.s1 v outp sp pa pb pc _ _ m hB.img.mpAdd hsf hcs he) (hsame he)
  have hfa := hS.disj (r := BinA.R.stk) (s := BinA.R.code) (by simp [Sep, hstk])
  simp only [Iv.Disj, Disj, BinA.lay, textIv, textBase, textLen] at hfa
  have hff : FFacts sp :=
    { rs := hB.rs, sp_al := hB.sp_al, sp_ge := hB.sp_ge, code_off := by simp only [mpAddBase]; omega }
  have hF1 : Frm ρ [BinA.R.stk] m (writeLog m (frameLog1 s0 v.s.s1 sp a.sign b.sign)) :=
    Frm.store (by simp only [LogIn, frameLog1, Iv.Sub, BinA.lay, and_true]; omega)
  have hF2 : Frm ρ [BinA.R.stk] m
      (writeLog (writeLog m (frameLog1 s0 v.s.s1 sp a.sign b.sign)) (frameLog2 ra sp pc)) :=
    (hF1.trans (Frm.store (w := BinA.R.stk) (by simp only [LogIn, frameLog2, Iv.Sub, BinA.lay, and_true]; omega))).mono
  have hrf : RFacts (writeLog (writeLog m (frameLog1 s0 v.s.s1 sp a.sign b.sign)) (frameLog2 ra sp pc))
      ra s0 v.s.s1 sp pc a.sign b.sign := by
    rw [← writeLog_append]
    exact { rs := hB.rs, sp_al := hB.sp_al, sp_ge := hB.sp_ge
            s0_v := bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]; omega)
            s1_v := bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]; omega)
            sb_v := bytesT8_log _ _ 2 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]; omega)
            sa_v := bytesT8_log _ _ 3 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]; omega)
            pc_v := bytesT8_log _ _ 4 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]; omega)
            ra_v := bytesT8_log _ _ 5 _ _ rfl (by simp [frameLog1, frameLog2, OutLRange]) }
  refine Triple.seq (d1_step ra s0 v.s.s1 v outp sp pa pb pc _ _ m hB.img.mpAdd hsf hff he)
    (Triple.seq (d2_step ra s0 v.s.s1 v outp sp pa pb pc _ _ _ (himg _ hF1).mpAdd hff) ?_)
  generalize writeLog (writeLog m (frameLog1 s0 v.s.s1 sp a.sign b.sign)) (frameLog2 ra sp pc) = M2
    at hF2 hrf ⊢
  have hcmp : CmpMag.Pre M2 pa adp pb bdp a b :=
    { ra := hF2.keep hS (MpAt.reads (rs := BinA.R.aS) (rd := BinA.R.aD) (Iv.sub_self _) (Iv.sub_self _)) hB.ra_ hmA
      rb := hF2.keep hS (MpAt.reads (rs := BinA.R.bS) (rd := BinA.R.bD) (Iv.sub_self _) (Iv.sub_self _)) hB.rb hmB
      va := va, vb := vb, ga := hB.ga, gb := hB.gb, code := (himg _ hF2).mpCmpMag }
  have hc2 := (himg _ hF2).mpAdd
  refine Triple.seq (cmp_call ra v outp sp pa adp pb bdp a b M2 hc2 hcmp) ?_
  rw [← cmpMag_eq va vb]
  by_cases hlt' : cmpMag a b = .lt
  · rw [hlt', show BitVec.ofInt 64 (ordCode .lt) = 0xffffffffffffffff#64 by decide]
    exact Triple.seq (bl_step ra s0 v.s.s1 v outp sp pa pb pc _ _ M2 hc2 hrf)
      (Triple.seq (l_step ra s0 v.s.s1 v outp sp pa pb pc _ _ M2 hc2 hrf hcs) (hlt he hlt' M2 hF2))
  · exact Triple.seq (b_step ra s0 v.s.s1 v outp sp pa pb pc _ _ _ M2 hc2 hrf (ne_lt _ hlt'))
      (Triple.seq (g_step ra s0 v.s.s1 v outp sp pa pb pc _ _ M2 hc2 hrf hcs) (hge he hlt' M2 hF2))

/-- The destination's sign slot, off `mp_add`'s code. -/
theorem csign {isW : BinA.R → Bool} {r : BinA.R} {p : Nat} (hS : Sound ρ isW) (hr : (ρ r) = ⟨p, 24⟩)
    (hsep : Sep isW r BinA.R.code = true) (hg : MpGeom p adp a.alloc ∨ MpGeom p bdp b.alloc) : CSign p :=
  have h := hS.disj hsep
  have hst : Ram p 24 ∧ p % 8 = 0 := by
    rcases hg with hg | hg
    · exact ⟨by simpa [Layout.sizeofMpInt] using hg.st, hg.st_al⟩
    · exact ⟨by simpa [Layout.sizeofMpInt] using hg.st, hg.st_al⟩
  { rc := hst.1, pc_al := hst.2
    code_off := by
      rw [hr] at h
      simp only [Iv.Disj, Disj, BinA.lay, textIv, textBase, textLen] at h
      simp only [mpAddBase]; omega }

/-- A tail call's result as the contract's. -/
theorem retA {Q : MpInt → Prop} (h : ∀ c', Q c' → AddPost a b a c') :
    ∀ cf, BinATail.RetQ m v outp sp ρ wsA pa adp ra s0 Q cf → MpAddAlias.RetCA m v outp sp pa adp pb bdp a b ra s0 cf
  | _, ⟨c', M, hat, ho⟩ => ⟨c', M, hat, ⟨ho.repr, h c' ho.q, ho.frame⟩⟩

theorem retB {Q : MpInt → Prop} (h : ∀ c', Q c' → AddPost a b b c') :
    ∀ cf, BinATail.RetQ m v outp sp ρ wsB pb bdp ra s0 Q cf → MpAddAlias.RetCB m v outp sp pa adp pb bdp a b ra s0 cf
  | _, ⟨c', M, hat, ho⟩ => ⟨c', M, hat, ⟨ho.repr, h c' ho.q, ho.frame⟩⟩

end

end Alias

/-- **`mp_add(a, b, a)` on the machine.** -/
theorem correctCA : MpAddAlias.StatementCA := by
  intro m v outp sp pa adp pb bdp a b ra s0 hP
  have hroom := hP.room
  have hT : ∀ M, Frm (BinA.lay 64 sp pa adp pb bdp a b) [BinA.R.stk] m M → BinATail.TA m M sp pa adp pb bdp a b ra :=
    fun M hF => { base := hP.toBase, sa := hP.va.toShape, sb := hP.vb.toShape, lay := hP.lay, fr := hF }
  refine Triple.lmap (fun cf h => h.reshape (L' := entry1 ra s0 v.s.s1 sp pa pb pa) (K' := v.keepR1)
    (by simp [SSub.entryL, entry1, Abi.keepR, sKeepL])
    (by simp [SSub.entryL, Abi.keepR1, Abi.keepR, sKeepL])) ?_
  refine Alias.skel hP.lay rfl hP.toBase hP.va hP.vb (Alias.csign (r := BinA.R.aS) hP.lay rfl rfl (Or.inl hP.ga)) ?_ ?_ ?_
  · intro he
    exact Triple.rmap (Alias.retA fun c' q => ⟨fun _ => q, fun h => absurd he h, fun h => absurd he h⟩)
      (BinATail.addA (hT m (Frm.refl _ m)) hroom _ hP.va.sign_ok)
  · intro hne hlt M hF
    exact Triple.rmap (Alias.retA fun c' q => ⟨fun h => absurd h hne, fun _ _ => q, fun _ h => absurd hlt h⟩)
      (BinATail.subBA (hT M hF) (cmpMag_lt_used hP.va hP.vb hlt) (by omega) _ hP.vb.sign_ok)
  · intro hne hge M hF
    exact Triple.rmap (Alias.retA fun c' q => ⟨fun h => absurd h hne, fun _ h => absurd h hge, fun _ _ => q⟩)
      (BinATail.subA (hT M hF) (cmpMag_ge_used hP.va hP.vb hge) _ hP.va.sign_ok)

/-- **`mp_add(a, b, b)` on the machine.** -/
theorem correctCB : MpAddAlias.StatementCB := by
  intro m v outp sp pa adp pb bdp a b ra s0 hP
  have hroom := hP.room
  have hT : ∀ M, Frm (BinA.lay 64 sp pa adp pb bdp a b) [BinA.R.stk] m M → BinATail.TB m M sp pa adp pb bdp a b ra :=
    fun M hF => { base := hP.toBase, sa := hP.va.toShape, sb := hP.vb.toShape, lay := hP.lay, fr := hF }
  refine Triple.lmap (fun cf h => h.reshape (L' := entry1 ra s0 v.s.s1 sp pa pb pb) (K' := v.keepR1)
    (by simp [SSub.entryL, entry1, Abi.keepR, sKeepL])
    (by simp [SSub.entryL, Abi.keepR1, Abi.keepR, sKeepL])) ?_
  refine Alias.skel hP.lay rfl hP.toBase hP.va hP.vb (Alias.csign (r := BinA.R.bS) hP.lay rfl rfl (Or.inr hP.gb)) ?_ ?_ ?_
  · intro he
    exact Triple.rmap (Alias.retB fun c' q => ⟨fun _ => q, fun h => absurd he h, fun h => absurd he h⟩)
      (BinATail.addB (hT m (Frm.refl _ m)) hroom _ hP.va.sign_ok)
  · intro hne hlt M hF
    exact Triple.rmap (Alias.retB fun c' q => ⟨fun h => absurd h hne, fun _ _ => q, fun _ h => absurd hlt h⟩)
      (BinATail.subAB (hT M hF) (cmpMag_lt_used hP.va hP.vb hlt) _ hP.vb.sign_ok)
  · intro hne hge M hF
    exact Triple.rmap (Alias.retB fun c' q => ⟨fun h => absurd h hne, fun _ h => absurd h hge, fun _ _ => q⟩)
      (BinATail.subB (hT M hF) (cmpMag_ge_used hP.va hP.vb hge) (by omega) _ hP.va.sign_ok)

end Tom.Machine.Fn.MpAdd
