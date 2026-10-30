import Tom.Machine.Fn.MulDCore
import Tom.Machine.Api.MulD

/-!
# `mp_mul_d` on the machine: the contracts

`Fn/MulDCore.lean`'s `whole` instantiated twice: with distinct operands over
`Api/Two.lean`'s regions (`correct : Api.MulD.Statement`; `a`'s digits are
read from the snapshot, off `c`'s), and in place over `Api/Un.lean`'s
(`correct_inplace : Api.MulD.StatementInPlace`; `a`'s digit `i` is read from
the array state, where it is still the old digit). The snapshots are the
memories after the prologue (`m3Of`/`m5Of`); read-only facts come by
`Frm.keep`, the layout by `Pre.lay`.
-/

namespace Tom.Machine.Fn.MulD

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api

theorem MulDPost.of_alloc {a c0 c c' : MpInt} {b : Nat} (h : MulDPost a b c0 c') (e : c0.alloc = c.alloc) :
    MulDPost a b c c' :=
  { alloc := h.alloc.trans e, len := e ▸ h.len, digit := h.digit, used := h.used, sign := h.sign }

/-- The entry state, with the callee-saved registers in the list. -/
theorem entry_reshape {ra s0 : BitVec 64} {v : Abi} {sp pa b pc : Nat} {m : Mem} {outp : Array String}
    {Q : Vsa.Machine.Config → Prop}
    (h : Triple (At 0x800019fc#64 (entL ra s0 v sp pa b pc) m (kMD v) outp) Q) :
    Triple (At MulD.entry (MulD.entryL ra s0 sp pa b pc) m v.keepR outp) Q :=
  Triple.lmap (fun _ h => h.reshape (by simp [entL, MulD.entryL, Abi.keepR, sKeepL])
    (by simp [kMD, Abi.keepR, sKeepL])) h

theorem ret_reshape {ra s0 : BitVec 64} {v : Abi} {sp : Nat} {M : Mem} {outp : Array String}
    {cf : Vsa.Machine.Config} (h : At ra (rL ra s0 v sp) M (kMD v) outp cf) :
    At ra [(1, ra), (2, BitVec.ofNat 64 sp), (8, s0), (10, 0#64)] M v.keepR outp cf :=
  h.reshape (by simp [rL]) (by simp [rL, kMD, Abi.keepR, sKeepL])

/-! ## Distinct operands -/

section
open Tom.Machine.Api.Two (R)
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pc cdp b : Nat} {a c : MpInt}
  {ra s0 : BitVec 64}

local notation "ρ" => MulD.lay sp pa adp pc cdp a c

theorem frm1 (hP : MulD.Pre m sp pa adp pc cdp a b c ra) :
    Frm ρ [R.stk] m (m1Of m ra v sp) := by
  have := hP.sp_ge
  exact Frm.store (by simp only [LogIn, log1, Iv.Sub, Two.lay, and_true]; omega)

theorem frm3 (hP : MulD.Pre m sp pa adp pc cdp a b c ra) :
    Frm ρ [R.stk, R.bS] m (m3Of m ra s0 v sp pc a.sign) := by
  have := hP.sp_ge
  have h2 : Frm ρ [R.stk] (m1Of m ra v sp) (m2Of m ra s0 v sp) :=
    Frm.store (by simp only [LogIn, log2, Iv.Sub, Two.lay, and_true]; omega)
  have h3 : Frm ρ [R.bS] (m2Of m ra s0 v sp) (m3Of m ra s0 v sp pc a.sign) :=
    Frm.sw (by simp only [Iv.Sub, Two.lay]; omega)
  exact ((frm1 hP).trans h2 |>.trans h3).mono

theorem frm5 (hP : MulD.Pre m sp pa adp pc cdp a b c ra) :
    Frm ρ [R.stk, R.bS] m (m5Of m ra s0 v sp pc a.sign) := by
  have := hP.sp_ge
  have h4 : Frm ρ [R.stk] (m3Of m ra s0 v sp pc a.sign) (m4Of m ra s0 v sp pc a.sign) :=
    Frm.store (by simp only [LogIn, log3, Iv.Sub, Two.lay, and_true]; omega)
  have h5 : Frm ρ [R.stk] (m4Of m ra s0 v sp pc a.sign) (m5Of m ra s0 v sp pc a.sign) :=
    Frm.store (by simp only [LogIn, log4, Iv.Sub, Two.lay, and_true]; omega)
  exact ((frm3 hP).trans h4 |>.trans h5).mono

/-- The placement facts, from `Pre.lay`. -/
structure Geo (sp pa adp pc cdp : Nat) (a c : MpInt) : Prop where
  k_t : sp ≤ textBase ∨ textBase + textLen ≤ sp - 80
  k_c : sp ≤ pc ∨ pc + 24 ≤ sp - 80
  k_d : sp ≤ cdp ∨ cdp + 4 * c.alloc ≤ sp - 80
  t_c : textBase + textLen ≤ pc ∨ pc + 24 ≤ textBase
  t_d : textBase + textLen ≤ cdp ∨ cdp + 4 * c.alloc ≤ textBase
  a_d : pa + 24 ≤ cdp ∨ cdp + 4 * c.alloc ≤ pa
  ad_d : adp + 4 * a.alloc ≤ cdp ∨ cdp + 4 * c.alloc ≤ adp

theorem geo (hP : MulD.Pre m sp pa adp pc cdp a b c ra) : Geo sp pa adp pc cdp a c := by
  have hS := hP.lay; have := hP.sp_ge
  have h1 := hS.disj (r := R.stk) (s := R.code); have h2 := hS.disj (r := R.stk) (s := R.bS)
  have h3 := hS.disj (r := R.stk) (s := R.bD); have h4 := hS.disj (r := R.code) (s := R.bS)
  have h5 := hS.disj (r := R.code) (s := R.bD); have h6 := hS.disj (r := R.aS) (s := R.bD)
  have h7 := hS.disj (r := R.aD) (s := R.bD)
  simp only [Iv.Disj, Disj, Two.lay, textIv] at h1 h2 h3 h4 h5 h6 h7
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem kfacts (hP : MulD.Pre m sp pa adp pc cdp a b c ra) : KFacts sp :=
  have hg := geo hP
  { rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
    code_off := by have := hg.k_t; simp only [mpMulDBase, textBase, textLen] at *; omega }

/-- What stays as at the entry. -/
structure RO (M : Mem) (pa adp : Nat) (a : MpInt) : Prop where
  img : Img M
  ra_ : MpAt M pa adp a

theorem RO.of (hP : MulD.Pre m sp pa adp pc cdp a b c ra) {M : Mem} (hF : Frm ρ [R.stk, R.bS] m M) :
    RO M pa adp a :=
  { img := hF.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
    ra_ := hF.keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_ }

theorem RO.of1 (hP : MulD.Pre m sp pa adp pc cdp a b c ra) {M : Mem} (hF : Frm ρ [R.stk] m M) :
    RO M pa adp a := RO.of hP hF.mono

theorem sign_lt (hP : MulD.Pre m sp pa adp pc cdp a b c ra) : a.sign < 2 := by
  have := hP.asign; simp only [Layout.mpZpos, Layout.mpNeg] at this; omega

/-- `c` after `c->sign := a->sign`. -/
theorem rc3 (hP : MulD.Pre m sp pa adp pc cdp a b c ra) :
    MpAt (m3Of m ra s0 v sp pc a.sign) pc cdp { c with sign := a.sign } := by
  have h2 : Frm ρ [R.stk] m (m2Of m ra s0 v sp) := by
    have := hP.sp_ge
    exact ((frm1 hP).trans (Frm.store (w := R.stk) (by simp only [LogIn, log2, Iv.Sub, Two.lay, and_true]; omega))).mono
  have hc2 := h2.keep hP.lay (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hP.rc
  have := sign_lt hP
  exact hc2.set_sign hP.gc _ (by omega)

theorem rc5 (hP : MulD.Pre m sp pa adp pc cdp a b c ra) :
    MpAt (m5Of m ra s0 v sp pc a.sign) pc cdp { c with sign := a.sign } := by
  have := hP.sp_ge
  have h4 : Frm ρ [R.stk] (m3Of m ra s0 v sp pc a.sign) (m5Of m ra s0 v sp pc a.sign) :=
    ((Frm.store (w := R.stk) (by simp only [LogIn, log3, Iv.Sub, Two.lay, and_true]; omega)).trans
      (Frm.store (w := R.stk) (by simp only [LogIn, log4, Iv.Sub, Two.lay, and_true]; omega))).mono
  exact h4.keep hP.lay
    (MpAt.reads (a := { c with sign := a.sign }) (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) (rc3 hP)

theorem proH (hP : MulD.Pre m sp pa adp pc cdp a b c ra) :
    ProH m ra s0 v sp pa adp pc cdp c.used a b c.alloc := by
  have hg := geo hP; have hk := kfacts hP; have := hP.sp_ge
  have hua := hP.sa.used_le; have hal := hP.sa.alloc_lt; have hcl := hP.sc.alloc_lt
  have hcu := hP.sc.used_le; have hroom := hP.room
  have hF2 : Frm ρ [R.stk] m (m2Of m ra s0 v sp) :=
    ((frm1 hP).trans (Frm.store (w := R.stk) (by simp only [LogIn, log2, Iv.Sub, Two.lay, and_true]; omega))).mono
  have hF4 : Frm ρ [R.stk, R.bS] m (m4Of m ra s0 v sp pc a.sign) :=
    ((frm3 hP).trans (Frm.store (w := R.stk) (by simp only [LogIn, log3, Iv.Sub, Two.lay, and_true]; omega))).mono
  have hc2 := hF2.keep hP.lay (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hP.rc
  have ha2 := (RO.of1 hP hF2).ra_
  have hgc := hg.t_c
  exact { c1 := hP.img.mpMulD, c2 := (RO.of1 hP (frm1 hP)).img.mpMulD, c3 := (RO.of1 hP hF2).img.mpMulD
          c4 := (RO.of hP (frm3 hP)).img.mpMulD, c5 := (RO.of hP hF4).img.mpMulD
          p1 := { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
                  rc := by simpa [Layout.sizeofMpInt] using hP.gc.st
                  rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
                  ua_v := by simpa [Layout.offUsed] using hP.ra_.used
                  al_v := by simpa [Layout.offAlloc] using hP.rc.alloc
                  ua_lt := by omega, al_lt := hcl, room := by omega, code_off := hk.code_off }
          k := hk
          p2 := { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
                  rc := by simpa [Layout.sizeofMpInt] using hP.gc.st
                  pc_al := hP.gc.st_al
                  sa_v := by simpa [Layout.offSign] using ha2.sign
                  ou_v := by simpa [Layout.offUsed] using hc2.used
                  cdp_v := by simpa [Layout.offDp] using hc2.dpv
                  sa_lt := by have := sign_lt hP; omega, ou_lt := by omega
                  code_c := by simp only [mpMulDBase, textBase, textLen] at *; omega }
          p3 := { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
                  adp_v := by simpa [Layout.offDp] using (RO.of hP hF4).ra_.dpv }
          hb := by have := hP.hb; simp only [radix, Layout.digitBits] at this; omega }

theorem tailH (hP : MulD.Pre m sp pa adp pc cdp a b c ra) {M0 : Mem} (hF : Frm ρ [R.stk, R.bS] m M0)
    (hrc : MpAt M0 pc cdp { c with sign := a.sign }) (hsv : EFacts M0 ra s0 v sp) :
    TailH (MulD.lay sp pa adp pc cdp a c) R.bD M0 ra s0 v sp pa pc cdp c.used a b { c with sign := a.sign } c.digit := by
  have hg := geo hP; have hro := RO.of hP hF
  have hua := hP.sa.used_le; have hal := hP.sa.alloc_lt
  exact { sa := hP.sa, hb := hP.hb, hw := rfl, room := hP.room, al_lt := hP.sc.alloc_lt
          ou_le := hP.sc.used_le, old_hz := fun j hj => hP.sc.high_zero j hj
          rc0 := hrc, gc := hP.gc, csign := rfl
          ua_v := by simpa [Layout.offUsed] using hro.ra_.used
          ra_ := by have := hP.ga.st; simp only [Layout.sizeofMpInt] at this
                    exact ⟨this.lo_ge, by have := this.hi_le; omega, by have := this.off; omega⟩
          img := hro.img, sv := hsv
          a_d := by have := hg.a_d; show pa + 4 ≤ cdp ∨ cdp + 4 * c.alloc ≤ pa; omega, k_d := hg.k_d, k_c := hg.k_c, t_d := hg.t_d, t_c := hg.t_c }

end

/-- **`mp_mul_d(a, b, c)` on the machine.** -/
theorem correct : Api.MulD.Statement := by
  intro m v outp sp pa adp pc cdp b a c ra s0 hP
  have hg := geo hP; have hk := kfacts hP
  have hrA : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  refine entry_reshape (Triple.rmap (fun cf h => ?_) (whole (ρ := MulD.lay sp pa adp pc cdp a c) (wD := .bD) (c0 := { c with sign := a.sign }) (old := c.digit)
    (proH (c := c) (v := v) (s0 := s0) hP)
    (fun _ => ⟨tailH hP (frm3 hP) (rc3 hP) (efacts3 hk hP.ra_al hg.k_c), (rc3 hP).arr⟩)
    (fun _ => ⟨tailH hP (frm5 hP) (rc5 hP) (efacts5 hk hP.ra_al hg.k_c), (rc5 hP).arr,
      fun M i hi hA => ?_⟩)))
  · have hfin : ∀ {M0 M : Mem}, Frm (MulD.lay sp pa adp pc cdp a c) [.stk, .bS] m M0 →
        (∀ x, (x < cdp ∨ cdp + 4 * c.alloc ≤ x) → (x < pc ∨ pc + 24 ≤ x) → M[x]? = M0[x]?) →
        Frm (MulD.lay sp pa adp pc cdp a c) Two.ws m M := fun hF hM x hx => by
      have := hP.sp_ge
      rw [hM x (by simp only [InAny, Iv.In, MulD.lay, Two.lay, Two.ws, or_false] at hx; omega)
        (by simp only [InAny, Iv.In, MulD.lay, Two.lay, Two.ws, or_false] at hx; omega)]
      exact hF x (by simp only [InAny, Iv.In, MulD.lay, Two.lay, Two.ws, or_false] at hx ⊢; omega)
    rcases h with ⟨_, c', M, hat, hr, hm, hM⟩ | ⟨_, c', M, hat, hr, hm, hM⟩
    · exact ⟨c', M, ret_reshape hat, hr, MulDPost.of_alloc hm rfl, hfin (frm3 hP) hM⟩
    · exact ⟨c', M, ret_reshape hat, hr, MulDPost.of_alloc hm rfl, hfin (frm5 hP) hM⟩

  · have hua := hP.sa.used_le
    have hro := RO.of hP (frm5 (s0 := s0) (v := v) hP)
    exact { r := ⟨by have := hrA.lo_ge; omega, by have := hrA.hi_le; omega, by have := hrA.off; omega⟩
            v := by
              have hM := hA.fr.keep hP.lay (MpAt.reads (rs := Two.R.aS) (rd := Two.R.aD) (Iv.sub_self _) (Iv.sub_self _))
                hro.ra_
              simpa [Layout.sizeofDigit] using hM.digits i (by omega)
            lt := by have := hP.sa.digit_lt i; simpa [radix, Layout.digitBits] using this }

/-! ## In place: `mp_mul_d(a, b, a)` -/

section
open Tom.Machine.Api.Un (R)
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp b : Nat} {a : MpInt} {ra s0 : BitVec 64}

local notation "σ" => MulD.layI sp pa adp a

theorem frmI1 (hP : MulD.PreI m sp pa adp a b ra) : Frm σ [R.stk] m (m1Of m ra v sp) := by
  have := hP.sp_ge
  exact Frm.store (by simp only [LogIn, log1, Iv.Sub, Un.lay, and_true]; omega)

theorem frmI2 (hP : MulD.PreI m sp pa adp a b ra) : Frm σ [R.stk] m (m2Of m ra s0 v sp) := by
  have := hP.sp_ge
  exact ((frmI1 hP).trans (Frm.store (w := R.stk) (by simp only [LogIn, log2, Iv.Sub, Un.lay, and_true]; omega))).mono

theorem frmI3 (hP : MulD.PreI m sp pa adp a b ra) : Frm σ [R.stk, R.aS] m (m3Of m ra s0 v sp pa a.sign) :=
  ((frmI2 hP).trans (Frm.sw (w := R.aS) (by simp only [Iv.Sub, Un.lay]; omega))).mono

theorem frmI4 (hP : MulD.PreI m sp pa adp a b ra) : Frm σ [R.stk, R.aS] m (m4Of m ra s0 v sp pa a.sign) := by
  have := hP.sp_ge
  exact ((frmI3 hP).trans (Frm.store (w := R.stk) (by simp only [LogIn, log3, Iv.Sub, Un.lay, and_true]; omega))).mono

theorem frmI5 (hP : MulD.PreI m sp pa adp a b ra) : Frm σ [R.stk, R.aS] m (m5Of m ra s0 v sp pa a.sign) := by
  have := hP.sp_ge
  exact ((frmI4 hP).trans (Frm.store (w := R.stk) (by simp only [LogIn, log4, Iv.Sub, Un.lay, and_true]; omega))).mono

structure GeoI (sp pa adp : Nat) (a : MpInt) : Prop where
  k_t : sp ≤ textBase ∨ textBase + textLen ≤ sp - 80
  k_c : sp ≤ pa ∨ pa + 24 ≤ sp - 80
  k_d : sp ≤ adp ∨ adp + 4 * a.alloc ≤ sp - 80
  t_c : textBase + textLen ≤ pa ∨ pa + 24 ≤ textBase
  t_d : textBase + textLen ≤ adp ∨ adp + 4 * a.alloc ≤ textBase
  a_d : pa + 24 ≤ adp ∨ adp + 4 * a.alloc ≤ pa

theorem geoI (hP : MulD.PreI m sp pa adp a b ra) : GeoI sp pa adp a := by
  have hS := hP.lay; have := hP.sp_ge
  have h1 := hS.disj (r := R.stk) (s := R.code); have h2 := hS.disj (r := R.stk) (s := R.aS)
  have h3 := hS.disj (r := R.stk) (s := R.aD); have h4 := hS.disj (r := R.code) (s := R.aS)
  have h5 := hS.disj (r := R.code) (s := R.aD)
  have h6 := hP.ga.disj
  simp only [Iv.Disj, Disj, Un.lay, textIv] at h1 h2 h3 h4 h5
  simp only [Layout.sizeofMpInt, Layout.sizeofDigit] at h6
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem kfactsI (hP : MulD.PreI m sp pa adp a b ra) : KFacts sp :=
  have hg := geoI hP
  { rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
    code_off := by have := hg.k_t; simp only [mpMulDBase, textBase, textLen] at *; omega }

theorem imgI (hP : MulD.PreI m sp pa adp a b ra) {M : Mem} (hF : Frm σ [R.stk, R.aS] m M) : Img M :=
  hF.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img

theorem raI2 (hP : MulD.PreI m sp pa adp a b ra) : MpAt (m2Of m ra s0 v sp) pa adp a :=
  (frmI2 hP).keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_

theorem signI_lt (hP : MulD.PreI m sp pa adp a b ra) : a.sign < 2 := by
  have := hP.asign; simp only [Layout.mpZpos, Layout.mpNeg] at this; omega

theorem raI3 (hP : MulD.PreI m sp pa adp a b ra) :
    MpAt (m3Of m ra s0 v sp pa a.sign) pa adp { a with sign := a.sign } :=
  (raI2 hP).set_sign hP.ga _ (by have := signI_lt hP; omega)

theorem raI5 (hP : MulD.PreI m sp pa adp a b ra) :
    MpAt (m5Of m ra s0 v sp pa a.sign) pa adp { a with sign := a.sign } := by
  have := hP.sp_ge
  have h4 : Frm σ [R.stk] (m3Of m ra s0 v sp pa a.sign) (m5Of m ra s0 v sp pa a.sign) :=
    ((Frm.store (w := R.stk) (by simp only [LogIn, log3, Iv.Sub, Un.lay, and_true]; omega)).trans
      (Frm.store (w := R.stk) (by simp only [LogIn, log4, Iv.Sub, Un.lay, and_true]; omega))).mono
  exact h4.keep hP.lay
    (MpAt.reads (a := { a with sign := a.sign }) (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) (raI3 hP)

theorem proHI (hP : MulD.PreI m sp pa adp a b ra) :
    ProH m ra s0 v sp pa adp pa adp a.used a b a.alloc := by
  have hg := geoI hP; have hk := kfactsI hP; have := hP.sp_ge
  have hua := hP.sa.used_le; have hal := hP.sa.alloc_lt; have hroom := hP.room
  have ha2 := raI2 (s0 := s0) (v := v) hP
  have ha4 : MpAt (m4Of m ra s0 v sp pa a.sign) pa adp { a with sign := a.sign } :=
    (Frm.store (ρ := σ) (w := R.stk) (by simp only [LogIn, log3, Iv.Sub, Un.lay, and_true]; omega)).keep hP.lay
      (MpAt.reads (a := { a with sign := a.sign }) (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _))
      (raI3 hP)
  have hgc := hg.t_c
  exact { c1 := hP.img.mpMulD, c2 := (imgI hP (frmI1 hP).mono).mpMulD, c3 := (imgI hP (frmI2 hP).mono).mpMulD
          c4 := (imgI hP (frmI3 hP)).mpMulD, c5 := (imgI hP (frmI4 hP)).mpMulD
          p1 := { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
                  rc := by simpa [Layout.sizeofMpInt] using hP.ga.st
                  rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
                  ua_v := by simpa [Layout.offUsed] using hP.ra_.used
                  al_v := by simpa [Layout.offAlloc] using hP.ra_.alloc
                  ua_lt := by omega, al_lt := hal, room := by omega, code_off := hk.code_off }
          k := hk
          p2 := { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
                  rc := by simpa [Layout.sizeofMpInt] using hP.ga.st
                  pc_al := hP.ga.st_al
                  sa_v := by simpa [Layout.offSign] using ha2.sign
                  ou_v := by simpa [Layout.offUsed] using ha2.used
                  cdp_v := by simpa [Layout.offDp] using ha2.dpv
                  sa_lt := by have := signI_lt hP; omega, ou_lt := by omega
                  code_c := by simp only [mpMulDBase, textBase, textLen] at *; omega }
          p3 := { ra_ := by simpa [Layout.sizeofMpInt] using hP.ga.st
                  adp_v := by simpa [Layout.offDp] using ha4.dpv }
          hb := by have := hP.hb; simp only [radix, Layout.digitBits] at this; omega }

theorem tailHI (hP : MulD.PreI m sp pa adp a b ra) {M0 : Mem} (hF : Frm σ [R.stk, R.aS] m M0)
    (hrc : MpAt M0 pa adp { a with sign := a.sign }) (hsv : EFacts M0 ra s0 v sp) :
    TailH (MulD.layI sp pa adp a) R.aD M0 ra s0 v sp pa pa adp a.used a b { a with sign := a.sign } a.digit := by
  have hg := geoI hP
  exact { sa := hP.sa, hb := hP.hb, hw := rfl, room := hP.room, al_lt := hP.sa.alloc_lt
          ou_le := hP.sa.used_le, old_hz := fun j hj => hP.sa.high_zero j hj
          rc0 := hrc, gc := hP.ga, csign := rfl
          ua_v := by simpa [Layout.offUsed] using hrc.used
          ra_ := by have := hP.ga.st; simp only [Layout.sizeofMpInt] at this
                    exact ⟨this.lo_ge, by have := this.hi_le; omega, by have := this.off; omega⟩
          img := imgI hP hF, sv := hsv
          a_d := by have := hg.a_d; show pa + 4 ≤ adp ∨ adp + 4 * a.alloc ≤ pa; omega
          k_d := hg.k_d, k_c := hg.k_c, t_d := hg.t_d, t_c := hg.t_c }

end

/-- **`mp_mul_d(a, b, a)` on the machine**: `a`'s digit `i` is read before it is overwritten. -/
theorem correct_inplace : Api.MulD.StatementInPlace := by
  intro m v outp sp pa adp b a ra s0 hP
  have hg := geoI hP; have hk := kfactsI hP
  have hrA : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using hP.ga.ds
  refine entry_reshape (Triple.rmap (fun cf h => ?_) (whole (ρ := MulD.layI sp pa adp a) (wD := .aD)
    (c0 := { a with sign := a.sign }) (old := a.digit)
    (proHI (v := v) (s0 := s0) hP)
    (fun _ => ⟨tailHI hP (frmI3 hP) (raI3 hP) (efacts3 hk hP.ra_al hg.k_c), (raI3 hP).arr⟩)
    (fun _ => ⟨tailHI hP (frmI5 hP) (raI5 hP) (efacts5 hk hP.ra_al hg.k_c), (raI5 hP).arr,
      fun M i hi hA => ?_⟩)))
  · have hfin : ∀ {M0 M : Mem}, Frm (MulD.layI sp pa adp a) [.stk, .aS] m M0 →
        (∀ x, (x < adp ∨ adp + 4 * a.alloc ≤ x) → (x < pa ∨ pa + 24 ≤ x) → M[x]? = M0[x]?) →
        Frm (MulD.layI sp pa adp a) Un.ws m M := fun hF hM x hx => by
      have := hP.sp_ge
      rw [hM x (by simp only [InAny, Iv.In, MulD.layI, Un.lay, Un.ws, or_false] at hx; omega)
        (by simp only [InAny, Iv.In, MulD.layI, Un.lay, Un.ws, or_false] at hx; omega)]
      exact hF x (by simp only [InAny, Iv.In, MulD.layI, Un.lay, Un.ws, or_false] at hx ⊢; omega)
    rcases h with ⟨_, c', M, hat, hr, hm, hM⟩ | ⟨_, c', M, hat, hr, hm, hM⟩
    · exact ⟨c', M, ret_reshape hat, hr, MulDPost.of_alloc hm rfl, hfin (frmI3 hP) hM⟩
    · exact ⟨c', M, ret_reshape hat, hr, MulDPost.of_alloc hm rfl, hfin (frmI5 hP) hM⟩
  · have hua := hP.sa.used_le
    exact { r := ⟨by have := hrA.lo_ge; omega, by have := hrA.hi_le; omega, by have := hrA.off; omega⟩
            v := by
              have := hA.arr i (show i < a.alloc by omega)
              simpa [ovl] using this
            lt := by have := hP.sa.digit_lt i; simpa [radix, Layout.digitBits] using this }

end Tom.Machine.Fn.MulD
