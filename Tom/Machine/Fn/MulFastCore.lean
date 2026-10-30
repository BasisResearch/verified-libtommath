import Tom.Machine.Fn.MulFastLoop

/-!
# `s_mp_mul_digs_fast` on the machine: the tail and the whole function, for any placement

After the column loop (`Fn/MulFastLoop.lean`): `c->used := pa`, `memcpy` of
`W` into `c->dp`, `memset` of the old digits above, `mp_clamp`, the epilogue
(`tailM`; `pa = 0`: `tailZ`); `whole` chains the prologue, the loop and the
tails from `Ent`, plain facts any placement of the operands meets (`c` may be
`a` or `b`).
-/

namespace Tom.Machine.Fn.MulFast

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api.Libgcc

/-! ## The calls after the loop -/

section calls
variable {v : Abi} {outp : Array String}

/-- `memcpy(c->dp, W, 4 pa)` at `4420`, back at `4424`. -/
theorem memcpy_call (v : Abi) (outp : Array String) (sp ua ub pa adp w ou cdp : Nat) (j2 j9 j10 : BitVec 64)
    (M : Mem) (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode)
    (hP : Memcpy.Pre M cdp (sp - 2160) (4 * pa)) :
    Triple (At 0x80004420#64 (mcL v sp ua ub pa adp w ou cdp j2 j9 j10) M (kF v) outp)
      (fun c => ∃ M', At 0x80004424#64 (m1L (fAbi v sp ua ub pa adp w ou j2 j9 j10) cdp) M' (kF v) outp c ∧
        Memcpy.Post M cdp (sp - 2160) (4 * pa) M') :=
  jal_call (pc := 0x80004420#64) (w := 0x060050ef#32) (imm := 0x005060#21)
    (Larg := mcL v sp ua ub pa adp w ou cdp j2 j9 j10)
    (L0 := Memcpy.entL 0x80004424#64 cdp (sp - 2160) (4 * pa))
    (K := (fAbi v sp ua ub pa adp w ou j2 j9 j10).keep)
    hc (by decide +kernel) (by decide) (by decide) (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide) (by decide) (fun p hp => hp)
    (by simp [mcL, abiL, sKeepL, keysG]) (by simp [kF, keysG])
    (by simp [Memcpy.entL, mcL, Sail.BitVec.addInt])
    (by simp [Abi.keep, fAbi, sKeepL, mcL, abiL, kF])
    (Triple.rmap (fun c ⟨M', hat, hpost⟩ => ⟨M', hat.reshape
        (by simp [m1L, Memcpy.retL, abiL, Abi.keep, fAbi, sKeepL])
        (by simp [kF, Abi.keep, fAbi, sKeepL]), hpost⟩)
      (Memcpy.correct 0x80004424#64 (fAbi v sp ua ub pa adp w ou j2 j9 j10) outp M _ _ _ (by decide) hP))

/-- `memset(c->dp + pa, 0, 4 (olduse - pa))` at `4448`, back at `444c`. -/
theorem memset_call (v : Abi) (outp : Array String) (u : Abi) (cdp pa ou : Nat) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hg : u.gp = v.gp) (ht : u.tp = v.tp)
    (hP : Memset.Pre M (cdp + 4 * pa) 0 (4 * (ou - pa))) :
    Triple (At 0x80004448#64 (msL u cdp pa ou) M (kF v) outp)
      (fun c => ∃ M', At 0x8000444c#64 (abiL u) M' (kF v) outp c ∧
        Memset.Post M (cdp + 4 * pa) (4 * (ou - pa)) 0#8 M') :=
  jal_call (pc := 0x80004448#64) (w := 0x75d040ef#32) (imm := 0x004f5c#21) (Larg := msL u cdp pa ou)
    (L0 := Memset.entryL 0x8000444c#64 (cdp + 4 * pa) 0#64 (4 * (ou - pa))) (K := u.keep)
    hc (by decide +kernel) (by decide) (by decide) (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide) (by decide) (fun p hp => hp)
    (by simp [msL, abiL, sKeepL, keysG]) (by simp [kF, keysG])
    (by simp [Memset.entryL, msL, Sail.BitVec.addInt])
    (by simp [Abi.keep, sKeepL, msL, abiL, kF, hg, ht])
    (Triple.rmap (fun c ⟨M', hat, hpost⟩ => ⟨M', hat.reshape (by simp [abiL, Abi.keep, sKeepL])
        (by simp [kF, Abi.keep, sKeepL, hg, ht]), hpost⟩)
      (Memset.correct_zero 0x8000444c#64 u outp M _ _ (by decide) hP))

/-- `mp_clamp(c)` at `4450`, back at `4454`. -/
theorem clamp_call (v : Abi) (outp : Array String) (u : Abi) (pc cdp : Nat) (cm : MpInt) (M : Mem)
    (hc : CodeAt M sMpMulDigsFastBase sMpMulDigsFastCode) (hg : u.gp = v.gp) (ht : u.tp = v.tp)
    (hP : Clamp.Pre M pc cdp cm) :
    Triple (At 0x80004450#64 (clL u pc) M (kF v) outp)
      (fun c => ∃ a' M', At 0x80004454#64 [(2, u.sp)] M' (kF v) outp c ∧ Clamp.Post M pc cdp cm a' M') :=
  jal_call (pc := 0x80004450#64) (w := 0x389000ef#32) (imm := 0x000b88#21) (Larg := clL u pc)
    (L0 := [(1, 0x80004454#64), (10, BitVec.ofNat 64 pc)]) (K := u.keep)
    hc (by decide +kernel) (by decide) (by decide) (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide) (by decide) (fun p hp => hp)
    (by simp [clL, abiL, sKeepL, keysG]) (by simp [kF, keysG])
    (by simp [clL, Sail.BitVec.addInt])
    (by simp [Abi.keep, sKeepL, clL, abiL, kF, hg, ht])
    (Triple.rmap (fun c ⟨a', M', hat, hpost⟩ => ⟨a', M', hat.reshape (by simp [Abi.keep])
        (by simp [kF, Abi.keep, sKeepL, hg, ht]), hpost⟩)
      (Clamp.correct 0x80004454#64 u outp pc cdp cm M (by decide) hP))

end calls

/-! ## After the loop -/

section tail
variable {m0 : Mem} {v : Abi} {outp : Array String} {ra s0 : BitVec 64} {sp pc cdp pa : Nat} {c0 : MpInt}

/-- What the code after the loop reads, and where things are; `m0` is the
snapshot at the loop's entry, `c0` is `c` there. -/
structure TailF (m0 : Mem) (ra s0 : BitVec 64) (v : Abi) (sp pc cdp : Nat) (c0 : MpInt) (pa : Nat) : Prop where
  k : KF sp
  hf : HFacts m0 ra s0 v sp
  pc_v : bytesT8 m0 (sp - 2184) = BitVec.ofNat 64 pc
  rc0 : MpAt m0 pc cdp c0
  gc : MpGeom pc cdp c0.alloc
  sc : c0.Shape
  room : pa ≤ c0.alloc
  pa_w : pa ≤ 512
  img : Img m0
  k_c : sp ≤ pc ∨ pc + 24 ≤ sp - 2192
  k_d : sp ≤ cdp ∨ cdp + 4 * c0.alloc ≤ sp - 2192
  k_t : sp ≤ textBase ∨ textBase + textLen ≤ sp - 2192
  t_c : textBase + textLen ≤ pc ∨ pc + 24 ≤ textBase
  t_d : textBase + textLen ≤ cdp ∨ cdp + 4 * c0.alloc ≤ textBase

/-- What the function leaves in `c`: the digits `g`, `used` clamped from `pa`. -/
structure FastOut (c0 c' : MpInt) (g : Nat → Nat) (pa : Nat) : Prop where
  alloc : c'.alloc = c0.alloc
  len : c'.digits.length = c0.alloc
  digit : c'.digit = g
  used : c'.used = clampUsed g pa
  sign : c'.sign = if c'.used = 0 then Layout.mpZpos else c0.sign

/-- The return, with memory as at `m0` off the stack and `c`. -/
def RetF (m0 : Mem) (v : Abi) (outp : Array String) (sp pc cdp : Nat) (c0 : MpInt) (g : Nat → Nat) (pa : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra (rL ra s0 v sp) M (kF v) outp cf ∧ MpAt M pc cdp c' ∧ FastOut c0 c' g pa ∧
    ∀ x, (x < sp - 2192 ∨ sp ≤ x) → (x < pc ∨ pc + 24 ≤ x) → (x < cdp ∨ cdp + 4 * c0.alloc ≤ x) → M[x]? = m0[x]?

/-- Off `W`, `c`'s struct and `c`'s digits. -/
def Off (sp pc cdp al x : Nat) : Prop :=
  (x < sp - 2160 ∨ sp - 112 ≤ x) ∧ (x < pc ∨ pc + 24 ≤ x) ∧ (x < cdp ∨ cdp + 4 * al ≤ x)

theorem TailF.imgOf (h : TailF m0 ra s0 v sp pc cdp c0 pa) {M : Mem}
    (hM : ∀ x, Off sp pc cdp c0.alloc x → M[x]? = m0[x]?) : Img M :=
  Img.of_text h.img fun x h1 h2 => hM x (by
    have := h.k_t; have := h.t_c; have := h.t_d; have := h.k.sp_ge
    unfold Off; simp only [textBase, textLen] at *; omega)

theorem TailF.hOf (h : TailF m0 ra s0 v sp pc cdp c0 pa) {M : Mem}
    (hM : ∀ x, Off sp pc cdp c0.alloc x → M[x]? = m0[x]?) : HFacts M ra s0 v sp := by
  have hf := h.hf; have := h.k.sp_ge; have hkc := h.k_c; have hkd := h.k_d
  have hr : ∀ k, sp - 104 ≤ k → k + 8 ≤ sp → bytesT8 M k = bytesT8 m0 k := fun k h1 h2 =>
    bytesT8_congr fun x h3 h4 => hM x (by unfold Off; omega)
  exact { k := hf.k, ra_al := hf.ra_al
          ra_v := (hr _ (by omega) (by omega)).trans hf.ra_v, s0_v := (hr _ (by omega) (by omega)).trans hf.s0_v
          s1_v := (hr _ (by omega) (by omega)).trans hf.s1_v, s2_v := (hr _ (by omega) (by omega)).trans hf.s2_v
          s3_v := (hr _ (by omega) (by omega)).trans hf.s3_v, s4_v := (hr _ (by omega) (by omega)).trans hf.s4_v
          s5_v := (hr _ (by omega) (by omega)).trans hf.s5_v, s6_v := (hr _ (by omega) (by omega)).trans hf.s6_v
          s7_v := (hr _ (by omega) (by omega)).trans hf.s7_v, s8_v := (hr _ (by omega) (by omega)).trans hf.s8_v
          s9_v := (hr _ (by omega) (by omega)).trans hf.s9_v, s10_v := (hr _ (by omega) (by omega)).trans hf.s10_v
          s11_v := (hr _ (by omega) (by omega)).trans hf.s11_v }

theorem TailF.pcOf (h : TailF m0 ra s0 v sp pc cdp c0 pa) {M : Mem}
    (hM : ∀ x, Off sp pc cdp c0.alloc x → M[x]? = m0[x]?) : bytesT8 M (sp - 2184) = BitVec.ofNat 64 pc := by
  have := h.k.sp_ge; have hkc := h.k_c; have hkd := h.k_d
  rw [bytesT8_congr fun x h3 h4 => hM x (by unfold Off; omega)]; exact h.pc_v

/-- `c` handed to `mp_clamp`: `used := pa`, the digits `g`. -/
def cMid (c0 : MpInt) (g : Nat → Nat) (pa : Nat) : MpInt :=
  { c0 with used := pa, digits := (List.range c0.alloc).map g }

theorem cMid_digit {c0 : MpInt} {g : Nat → Nat} {pa : Nat} (hg : ∀ j, c0.alloc ≤ j → g j = 0) :
    (cMid c0 g pa).digit = g := by
  funext i
  simp only [cMid, MpInt.digit, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < c0.alloc
  · simp [h]
  · simp [h, hg i (by omega)]

/-- From `444c`: `mp_clamp(c)` and the epilogue. -/
theorem tail444 (h : TailF m0 ra s0 v sp pc cdp c0 pa) (u : Abi) (hsp : u.sp = BitVec.ofNat 64 (sp - 2192))
    (hgp : u.gp = v.gp) (htp : u.tp = v.tp) (g : Nat → Nat) (hglt : ∀ j, g j < radix) (hgz : ∀ j, pa ≤ j → g j = 0)
    (M : Mem) (hM : ∀ x, Off sp pc cdp c0.alloc x → M[x]? = m0[x]?) (hrc : MpAt M pc cdp (cMid c0 g pa)) :
    Triple (At 0x8000444c#64 (abiL u) M (kF v) outp) (RetF m0 v outp sp pc cdp c0 g pa ra s0) := by
  have hroom := h.room; have hal := h.sc.alloc_lt; have hk := h.k; have := hk.sp_ge
  have hkc := h.k_c; have htc := h.t_c; have hst := h.gc.st
  simp only [Layout.sizeofMpInt] at hst
  have himg := h.imgOf hM
  have hdig := cMid_digit (pa := pa) (hg := fun j hj => hgz j (by omega)) (c0 := c0)
  have hpre : Clamp.Pre M pc cdp (cMid c0 g pa) :=
    { repr := hrc
      shape := { len := by simp [cMid]
                 used_le := hroom
                 alloc_lt := hal
                 digit_lt := fun i => by rw [hdig]; exact hglt i
                 high_zero := fun i hi => by rw [hdig]; exact hgz i hi }
      geom := h.gc, code := himg.mpClamp
      code_off := by simp only [mpClampBase, textBase, textLen] at *; omega }
  refine Triple.seq (gc_step v outp u sp pc M himg.sMpMulDigsFast hk hsp (h.pcOf hM))
    (Triple.seq (clamp_call v outp u pc cdp _ M himg.sMpMulDigsFast hgp htp hpre) ?_)
  intro cf ⟨c', M', hat, hpost⟩
  have hM' : ∀ x, Off sp pc cdp c0.alloc x → M'[x]? = m0[x]? := fun x hx =>
    (hpost.frame x (by unfold Off at hx; omega)).trans (hM x hx)
  have hat' : At 0x80004454#64 [(2, BitVec.ofNat 64 (sp - 2192))] M' (kF v) outp cf := by rw [← hsp]; exact hat
  refine Triple.rmap (fun cf hr => ⟨c', _, hr, hpost.repr, ?_, fun x h1 h2 h3 => ?_⟩)
    (h_step ra s0 v outp sp M' (h.imgOf hM').sMpMulDigsFast (h.hOf hM')) cf hat'
  · have hcp := hpost.clamp
    exact { alloc := hcp.alloc
            len := by rw [hcp.digits]; simp [cMid]
            digit := by rw [hcp.digit, hdig]
            used := by rw [hcp.used, hdig]; rfl
            sign := by rw [hcp.sign]; rfl }
  · exact (hpost.frame x (by omega)).trans (hM x (by unfold Off; omega))

end tail

theorem _root_.Tom.Machine.Ram.sub {lo len lo' len' : Nat} (h : Ram lo len) (h1 : lo ≤ lo')
    (h2 : lo' + len' ≤ lo + len) : Ram lo' len' :=
  ⟨by have := h.lo_ge; omega, by have := h.hi_le; omega, by have := h.off; omega⟩

theorem _root_.Tom.Machine.ArrFrm.outW {m0 M : Mem} {sp : Nat} {f : Nat → Nat}
    (hA : ArrFrm (ρW sp) () m0 M (sp - 2160) 512 f) (hsp : 2192 ≤ sp) {x : Nat}
    (hx : x < sp - 2160 ∨ sp - 112 ≤ x) : M[x]? = m0[x]? :=
  hA.fr x fun h => by
    rcases h with h | h
    · have h1 : sp - 2160 ≤ x := h.1
      have h2 : x < sp - 2160 + 2048 := h.2
      omega
    · exact h.elim

section tail2
variable {m0 : Mem} {v : Abi} {outp : Array String} {ra s0 : BitVec 64} {sp pc cdp pa : Nat} {c0 : MpInt}

/-- The digits after the copy: `g` below `pa`, `c`'s old digits above. -/
theorem TailF.cfacts (h : TailF m0 ra s0 v sp pc cdp c0 pa) {M : Mem}
    (hM : ∀ x, Off sp pc cdp c0.alloc x → M[x]? = m0[x]?) (hst : ∀ x, pc ≤ x → x < pc + 24 → M[x]? = m0[x]?) :
    CFacts M sp pc c0.used cdp :=
  have hst' := h.gc.st
  have hrc := h.rc0
  { rc := by simpa [Layout.sizeofMpInt] using hst', pc_al := h.gc.st_al, pc_v := h.pcOf hM
    ou_v := by rw [bytesT4_congr fun x h1 h2 => hst x (by omega) (by omega)]; simpa [Layout.offUsed] using hrc.used
    cdp_v := by
      rw [bytesT8_congr fun x h1 h2 => hst x (by omega) (by omega)]; simpa [Layout.offDp] using hrc.dpv
    ou_lt := by have := h.sc.used_le; have := h.sc.alloc_lt; omega
    code_c := by have := h.t_c; simp only [sMpMulDigsFastBase, textBase, textLen] at *; omega }

/-- **The tail of the main path**: from the loop's exit at `43fc` to the return. -/
theorem tailM (h : TailF m0 ra s0 v sp pc cdp c0 pa) (hpa1 : 1 ≤ pa) (hpa : pa < 2 ^ 30) (ua ub adp w : Nat)
    (D old : Nat → Nat) (hD : ∀ j, D j < radix) :
    Triple (fun cf => ∃ j0 j9 j10 : BitVec 64, WSt m0 v outp sp 0x800043fc#64
        (oH sp ua ub pa adp pa w j0 (BitVec.ofNat 64 pa) j9 j10) (ovl D old pa) cf)
      (RetF m0 v outp sp pc cdp c0 (fun j => if j < pa then D j else 0) pa ra s0) := by
  intro cf ⟨j0, j9, j10, M, hA, hat⟩
  have hk := h.k; have := hk.sp_ge; have hkc := h.k_c; have hkd := h.k_d; have htd := h.t_d
  have hroom := h.room; have hpw := h.pa_w; have hgd := h.gc.disj; have hcu := h.sc.used_le
  have hal := h.sc.alloc_lt
  simp only [Layout.sizeofMpInt, Layout.sizeofDigit] at hgd
  have hW : ∀ x, (x < sp - 2160 ∨ sp - 112 ≤ x) → M[x]? = m0[x]? := fun x hx => hA.outW (by omega) hx
  have hMo : ∀ x, Off sp pc cdp c0.alloc x → M[x]? = m0[x]? := fun x hx => hW x hx.1
  have hst : ∀ x, pc ≤ x → x < pc + 24 → M[x]? = m0[x]? := fun x h1 h2 => hW x (by omega)
  have hrcM : MpAt M pc cdp c0 := h.rc0.of_agree hst (fun x h1 h2 => hW x (by omega))
  have hcf := h.cfacts hMo hst
  have himg := h.imgOf hMo
  let g : Nat → Nat := fun j => if j < pa then D j else 0
  -- `M1`: `c->used := pa`
  have hM1 : ∀ x, Off sp pc cdp c0.alloc x → (writeLog M [(pc, 4, BitVec.ofNat 64 pa)])[x]? = m0[x]? :=
    fun x hx => (writeLog_out _ _ _ (by simp [OutL]; unfold Off at hx; omega)).trans (hMo x hx)
  have hW1 : ArrAt (writeLog M [(pc, 4, BitVec.ofNat 64 pa)]) (sp - 2160) pa D := fun j hj => by
    rw [bytesT4_congr fun x h1 h2 => writeLog_out _ _ _ (by simp [OutL]; omega)]
    have := hA.arr j (by omega); simp only [ovl, if_pos hj] at this; exact this
  have hrc1 := hrcM.set_used h.gc pa (by omega)
  have hrd : Ram cdp (4 * c0.alloc) := by simpa [Layout.sizeofDigit] using h.gc.ds
  have hrs := hk.rs
  have hmc : Memcpy.Pre (writeLog M [(pc, 4, BitVec.ofNat 64 pa)]) cdp (sp - 2160) (4 * pa) :=
    { img := h.imgOf hM1
      rd := hrd.sub (Nat.le_refl _) (by omega)
      rs := hrs.sub (by omega) (by omega)
      disj := by omega
      code_off := by
        have : memcpyCode.length = 74 := rfl
        rw [this]; simp only [memcpyBase, textBase, textLen] at *; omega }
  refine Triple.seq (f1_step v outp sp ua ub pa adp w pc c0.used cdp j0 _ j9 j10 M himg.sMpMulDigsFast hk hcf hpa)
    (Triple.seq (f1b_step v outp sp ua ub pa adp w pc c0.used cdp _ j9 j10 M himg.sMpMulDigsFast hcf hpa)
      (Triple.seq (memcpy_call v outp sp ua ub pa adp w c0.used cdp _ j9 j10 _ hmc.img.sMpMulDigsFast hmc) ?_)) cf hat
  intro cf ⟨M2, hat2, hpost⟩
  -- the digits after the copy
  have hA2 : ArrFrm (fun _ : Unit => (⟨cdp, 4 * c0.alloc⟩ : Iv)) () (writeLog M [(pc, 4, BitVec.ofNat 64 pa)]) M2
      cdp c0.alloc (ovl g c0.digit pa) :=
    { rgn := Iv.sub_self _
      fr := Frm.call hpost.frame (by simp only [Iv.Sub]; omega)
      arr := fun j hj => by
        by_cases hjp : j < pa
        · have := (hpost.arr hW1 (Nat.le_refl _)) j hjp
          simp only [ovl, if_pos hjp, g]; exact this
        · rw [bytesT4_congr fun x h1 h2 => hpost.frame x (by omega),
            bytesT4_congr fun x h1 h2 => writeLog_out _ _ _ (by simp [OutL]; omega)]
          simp only [ovl, if_neg hjp]
          exact hrcM.arr j hj }
  have hM2 : ∀ x, Off sp pc cdp c0.alloc x → M2[x]? = m0[x]? := fun x hx =>
    (hpost.frame x (by unfold Off at hx; omega)).trans (hM1 x hx)
  have hfin : ∀ {M3 : Mem}, ArrFrm (fun _ : Unit => (⟨cdp, 4 * c0.alloc⟩ : Iv)) ()
      (writeLog M [(pc, 4, BitVec.ofNat 64 pa)]) M3 cdp c0.alloc g → MpAt M3 pc cdp (cMid c0 g pa) := fun hA3 =>
    hrc1.of_hdr (fun x h1 h2 => hA3.fr x (by simp only [InAny, Iv.In, or_false]; omega))
      (by rw [cMid_digit (fun j hj => by simp only [g]; rw [if_neg (by omega)])]; exact hA3.arr) rfl rfl rfl
  have hglt : ∀ j, g j < radix := fun j => by simp only [g]; split; exact hD j; exact radix_pos
  have hgz : ∀ j, pa ≤ j → g j = 0 := fun j hj => by simp only [g]; rw [if_neg (by omega)]
  have hcode2 := (h.imgOf hM2).sMpMulDigsFast
  by_cases hou : c0.used ≤ pa
  · have hA3 := hA2.congr fun j hj => by
      simp only [ovl]; split
      · rfl
      · rw [h.sc.high_zero j (by omega), hgz j (by omega)]
    exact Triple.seq (f2t_step v outp (fAbi v sp ua ub pa adp w c0.used (BitVec.ofNat 64 pa) j9 j10) cdp pa c0.used M2
        hcode2 rfl rfl hou hpa1 hpa (by omega))
      (tail444 h (fAbi v sp ua ub pa adp w c0.used (BitVec.ofNat 64 pa) j9 j10) (by simp only [fAbi]) (by simp only [fAbi])
        (by simp only [fAbi]) g hglt hgz M2 hM2 (hfin hA3))
        cf hat2
  have hms : Memset.Pre M2 (cdp + 4 * pa) 0 (4 * (c0.used - pa)) :=
    { byte := by decide, code := (h.imgOf hM2).memset
      ram := hrd.sub (by omega) (by omega)
      code_off := by
        have : memsetCode.length = 55 := rfl
        rw [this]; simp only [memsetBase, textBase, textLen] at *; omega }
  have := hrd.hi_le
  refine Triple.seq (f2m_step v outp (fAbi v sp ua ub pa adp w c0.used (BitVec.ofNat 64 pa) j9 j10) cdp pa c0.used M2
      hcode2 rfl rfl (by omega) hpa1 (by omega) (by omega))
    (Triple.seq (memset_call v outp (fAbi v sp ua ub pa adp w c0.used (BitVec.ofNat 64 pa) j9 j10) cdp pa c0.used M2
      hcode2 (by simp only [fAbi]) (by simp only [fAbi]) hms) ?_) cf hat2
  intro cf ⟨M3, hat3, hp3⟩
  have hA3 := (hA2.fill (k := c0.used) (by omega) hcu
      (fun t ht => hp3.fill t (by omega)) (fun x hx => hp3.frame x (by omega))
      (fun j h1 _ => hgz j h1)).congr fun j hj => by
    simp only [ovl]; split
    · rfl
    · rw [h.sc.high_zero j (by omega), hgz j (by omega)]
  have hM3 : ∀ x, Off sp pc cdp c0.alloc x → M3[x]? = m0[x]? := fun x hx =>
    (hp3.frame x (by unfold Off at hx; omega)).trans (hM2 x hx)
  exact tail444 h (fAbi v sp ua ub pa adp w c0.used (BitVec.ofNat 64 pa) j9 j10) (by simp only [fAbi]) (by simp only [fAbi])
        (by simp only [fAbi]) g hglt hgz M3 hM3
    (hfin hA3) cf hat3

end tail2

section tailz
variable {m0 : Mem} {v : Abi} {outp : Array String} {ra s0 : BitVec 64} {sp pc cdp : Nat} {c0 : MpInt}

/-- **The tail of the `pa = 0` path**: from `450c` to the return. -/
theorem tailZ (h : TailF m0 ra s0 v sp pc cdp c0 0) (pa pb dg ua ub : Nat) (g : Nat → Nat) (hg : ∀ j, g j = 0) :
    Triple (At 0x8000450c#64 (zL v sp pa pb dg ua ub) m0 (kF v) outp)
      (RetF m0 v outp sp pc cdp c0 g 0 ra s0) := by
  have hk := h.k; have := hk.sp_ge; have hkc := h.k_c; have hkd := h.k_d; have htd := h.t_d; have htc := h.t_c
  have hgd := h.gc.disj; have hcu := h.sc.used_le; have hal := h.sc.alloc_lt; have hst := h.gc.st
  simp only [Layout.sizeofMpInt, Layout.sizeofDigit] at hgd hst
  have hrd : Ram cdp (4 * c0.alloc) := by simpa [Layout.sizeofDigit] using h.gc.ds
  have hm0 : ∀ x, Off sp pc cdp c0.alloc x → m0[x]? = m0[x]? := fun _ _ => rfl
  have hcf := h.cfacts hm0 (fun _ _ _ => rfl)
  have himg := h.img
  have hglt : ∀ j, g j < radix := fun j => by rw [hg]; exact radix_pos
  have hgz : ∀ j, 0 ≤ j → g j = 0 := fun j _ => hg j
  have hu : UFacts pc := { rc := hst, pc_al := h.gc.st_al
                           code_c := by simp only [sMpMulDigsFastBase, textBase, textLen] at *; omega }
  have hrc1 := h.rc0.set_used h.gc 0 (by omega)
  have hM1 : ∀ x, Off sp pc cdp c0.alloc x → (writeLog m0 [(pc, 4, 0#64)])[x]? = m0[x]? :=
    fun x hx => writeLog_out _ _ _ (by simp [OutL]; unfold Off at hx; omega)
  have hfin : ∀ {M : Mem}, ArrFrm (fun _ : Unit => (⟨cdp, 4 * c0.alloc⟩ : Iv)) () (writeLog m0 [(pc, 4, 0#64)]) M
      cdp c0.alloc g → MpAt M pc cdp (cMid c0 g 0) := fun hA =>
    hrc1.of_hdr (fun x h1 h2 => hA.fr x (by simp only [InAny, Iv.In, or_false]; omega))
      (by rw [cMid_digit (fun j _ => hg j)]; exact hA.arr) rfl rfl rfl
  have hA1 : ArrFrm (fun _ : Unit => (⟨cdp, 4 * c0.alloc⟩ : Iv)) () (writeLog m0 [(pc, 4, 0#64)])
      (writeLog m0 [(pc, 4, 0#64)]) cdp c0.alloc (ovl g c0.digit 0) :=
    ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; exact hrc1.arr)
  refine Triple.seq (z_step v outp sp pa pb dg ua ub pc c0.used cdp m0 himg.sMpMulDigsFast hk hcf) ?_
  by_cases hou : c0.used = 0
  · rw [hou]
    have hA := hA1.congr (f' := g) fun j hj => by rw [ovl_zero, hg]; exact h.sc.high_zero j (by omega)
    exact Triple.seq (zt_step v outp sp pa pb dg ua ub pc cdp _ himg.sMpMulDigsFast hu)
      (tail444 h (zAbi v sp pa pb dg ua ub) (by simp only [zAbi]) (by simp only [zAbi]) (by simp only [zAbi])
        g hglt hgz _ hM1 (hfin hA))
  have hms : Memset.Pre (writeLog m0 [(pc, 4, 0#64)]) (cdp + 4 * 0) 0 (4 * (c0.used - 0)) :=
    { byte := by decide, code := (h.imgOf hM1).memset
      ram := hrd.sub (by omega) (by omega)
      code_off := by
        have : memsetCode.length = 55 := rfl
        rw [this]; simp only [memsetBase, textBase, textLen] at *; omega }
  refine Triple.seq (zm_step v outp sp pa pb dg ua ub pc c0.used cdp _ himg.sMpMulDigsFast hu (by omega) (by omega))
    (Triple.seq (memset_call v outp (zAbi v sp pa pb dg ua ub) cdp 0 c0.used _ (h.imgOf hM1).sMpMulDigsFast
      (by simp only [zAbi]) (by simp only [zAbi]) hms) ?_)
  intro cf ⟨M2, hat2, hp2⟩
  have hA2 := (hA1.fill (k := c0.used) (by omega) hcu
      (fun t ht => hp2.fill t (by omega)) (fun x hx => hp2.frame x (by omega))
      (fun j h1 _ => hg j)).congr fun j hj => by
    simp only [ovl]; split
    · rfl
    · rw [h.sc.high_zero j (by omega), hg]
  have hM2 : ∀ x, Off sp pc cdp c0.alloc x → M2[x]? = m0[x]? := fun x hx =>
    (hp2.frame x (by unfold Off at hx; omega)).trans (hM1 x hx)
  exact tail444 h (zAbi v sp pa pb dg ua ub) (by simp only [zAbi]) (by simp only [zAbi]) (by simp only [zAbi])
    g hglt hgz M2 hM2 (hfin hA2) cf hat2

end tailz

/-! ## The whole function, for any placement -/

/-- The prologue's stores: the saves, `c`, then (for `pa > 0`) the spills. -/
def proLog (ra s0 : BitVec 64) (v : Abi) (sp pc : Nat) : List WEntry :=
  log1a s0 v sp ++ log1b ra v sp ++ log2 v sp ++ [(sp - 2184, 8, BitVec.ofNat 64 pc)]

/-- What `s_mp_mul_digs_fast(a, b, c, digs)` needs, as plain facts: the three
operands in memory, the C's conditions (`digs < MP_WARRAY`, `min(a->used,
b->used) ≤ MP_MAXFAST`, no `mp_grow`), and the frame `[sp - 2192, sp)` and
`c` off the text and the frame off everything. `c` may be `a` or `b`. -/
structure Ent (m : Mem) (sp pa adp pb bdp pc cdp dg : Nat) (a b c : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  rc : MpAt m pc cdp c
  sa : a.ShapeU
  sb : b.ShapeU
  sc : c.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  gc : MpGeom pc cdp c.alloc
  dg_w : dg < 512
  maxf : min a.used b.used ≤ 256
  uab : a.used + b.used < 2 ^ 30
  room : dg ≤ c.alloc
  rs : Ram (sp - 2192) 2192
  sp_al : sp % 16 = 0
  sp_ge : 2192 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  k_as : sp ≤ pa ∨ pa + 24 ≤ sp - 2192
  k_ad : sp ≤ adp ∨ adp + 4 * a.alloc ≤ sp - 2192
  k_bs : sp ≤ pb ∨ pb + 24 ≤ sp - 2192
  k_bd : sp ≤ bdp ∨ bdp + 4 * b.alloc ≤ sp - 2192
  k_cs : sp ≤ pc ∨ pc + 24 ≤ sp - 2192
  k_cd : sp ≤ cdp ∨ cdp + 4 * c.alloc ≤ sp - 2192
  k_t : sp ≤ textBase ∨ textBase + textLen ≤ sp - 2192
  t_cs : textBase + textLen ≤ pc ∨ pc + 24 ≤ textBase
  t_cd : textBase + textLen ≤ cdp ∨ cdp + 4 * c.alloc ≤ textBase

/-- What it leaves, off the frame and `c`: memory as at the entry. -/
def RetE (m : Mem) (v : Abi) (outp : Array String) (sp pc cdp dg : Nat) (a b c : MpInt) (ra s0 : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra (rL ra s0 v sp) M (kF v) outp cf ∧ MpAt M pc cdp c' ∧ MulFastPost a b c c' dg ∧
    ∀ x, (x < sp - 2192 ∨ sp ≤ x) → (x < pc ∨ pc + 24 ≤ x) → (x < cdp ∨ cdp + 4 * c.alloc ≤ x) → M[x]? = m[x]?

section whole
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp pc cdp dg : Nat} {a b c : MpInt}
  {ra s0 : BitVec 64}

theorem Ent.kf (h : Ent m sp pa adp pb bdp pc cdp dg a b c ra) : KF sp :=
  { rs := h.rs, sp_al := h.sp_al, sp_ge := h.sp_ge
    code_off := by have := h.k_t; simp only [sMpMulDigsFastBase, textBase, textLen] at *; omega }

/-- A store log inside the frame. -/
def InK (sp : Nat) : List WEntry → Prop
  | [] => True
  | e :: l => sp - 2192 ≤ e.1 ∧ e.1 + e.2.1 ≤ sp ∧ InK sp l

theorem inK_out {sp x : Nat} (hx : x < sp - 2192 ∨ sp ≤ x) : ∀ {l : List WEntry}, InK sp l → OutL l x
  | [], _ => trivial
  | _ :: _, ⟨h1, h2, h3⟩ => ⟨by omega, inK_out hx h3⟩

theorem inK_append {sp : Nat} : ∀ {l l' : List WEntry}, InK sp l → InK sp l' → InK sp (l ++ l')
  | [], _, _, h => h
  | _ :: _, _, ⟨h1, h2, h3⟩, h' => ⟨h1, h2, inK_append h3 h'⟩

/-- Off the frame, a memory after frame stores is the entry memory. -/
theorem Ent.offK (h : Ent m sp pa adp pb bdp pc cdp dg a b c ra) {l : List WEntry} (hl : InK sp l) :
    ∀ x, (x < sp - 2192 ∨ sp ≤ x) → (writeLog m l)[x]? = m[x]? := fun x hx => writeLog_out _ _ _ (inK_out hx hl)

theorem inK_pro (h : 2192 ≤ sp) : InK sp (proLog ra s0 v sp pc) := by
  simp only [proLog, log1a, log1b, log2, List.cons_append, List.nil_append, InK, and_true]; omega

theorem inK_sp (h : 2192 ≤ sp) (ua ub bdp : Nat) : InK sp (spLog sp ua ub bdp) := by
  simp only [spLog, InK, and_true]; omega

theorem Ent.imgK (h : Ent m sp pa adp pb bdp pc cdp dg a b c ra) {l : List WEntry} (hl : InK sp l) :
    Img (writeLog m l) :=
  Img.of_text h.img fun x h1 h2 => h.offK hl x (by have := h.k_t; simp only [textBase, textLen] at *; omega)

theorem Ent.mpK (h : Ent m sp pa adp pb bdp pc cdp dg a b c ra) {l : List WEntry} (hl : InK sp l) {p dp : Nat}
    {x : MpInt} (hx : MpAt m p dp x) (h1 : sp ≤ p ∨ p + 24 ≤ sp - 2192)
    (h2 : sp ≤ dp ∨ dp + 4 * x.alloc ≤ sp - 2192) : MpAt (writeLog m l) p dp x :=
  hx.of_agree (fun y h3 h4 => h.offK hl y (by omega)) (fun y h3 h4 => h.offK hl y (by omega))

/-- The saved registers, read back from the snapshot after the prologue's stores. -/
theorem hfacts4 (h : Ent m sp pa adp pb bdp pc cdp dg a b c ra) :
    HFacts (writeLog m (proLog ra s0 v sp pc)) ra s0 v sp := by
  have := h.sp_ge
  exact { k := h.kf, ra_al := h.ra_al
          s0_v := bytesT8_log _ _ 0 _ _ rfl (by simp [proLog, log1a, log1b, log2, OutLRange]; omega)
          s1_v := bytesT8_log _ _ 1 _ _ rfl (by simp [proLog, log1a, log1b, log2, OutLRange]; omega)
          s2_v := bytesT8_log _ _ 2 _ _ rfl (by simp [proLog, log1a, log1b, log2, OutLRange]; omega)
          ra_v := bytesT8_log _ _ 3 _ _ rfl (by simp [proLog, log1a, log1b, log2, OutLRange]; omega)
          s3_v := bytesT8_log _ _ 4 _ _ rfl (by simp [proLog, log1a, log1b, log2, OutLRange]; omega)
          s4_v := bytesT8_log _ _ 5 _ _ rfl (by simp [proLog, log1a, log1b, log2, OutLRange]; omega)
          s5_v := bytesT8_log _ _ 6 _ _ rfl (by simp [proLog, log1a, log1b, log2, OutLRange]; omega)
          s6_v := bytesT8_log _ _ 7 _ _ rfl (by simp [proLog, log1a, log1b, log2, OutLRange]; omega)
          s7_v := bytesT8_log _ _ 8 _ _ rfl (by simp [proLog, log1a, log1b, log2, OutLRange]; omega)
          s8_v := bytesT8_log _ _ 9 _ _ rfl (by simp [proLog, log1a, log1b, log2, OutLRange]; omega)
          s9_v := bytesT8_log _ _ 10 _ _ rfl (by simp [proLog, log1a, log1b, log2, OutLRange]; omega)
          s10_v := bytesT8_log _ _ 11 _ _ rfl (by simp [proLog, log1a, log1b, log2, OutLRange]; omega)
          s11_v := bytesT8_log _ _ 12 _ _ rfl (by simp [proLog, log1a, log1b, log2, OutLRange]; omega) }

theorem pcv4 (h : Ent m sp pa adp pb bdp pc cdp dg a b c ra) :
    bytesT8 (writeLog m (proLog ra s0 v sp pc)) (sp - 2184) = BitVec.ofNat 64 pc :=
  bytesT8_log _ _ 13 _ _ rfl (by simp [proLog, log1a, log1b, log2, OutLRange])

theorem HFacts.mono {M M' : Mem} (hf : HFacts M ra s0 v sp)
    (hs : ∀ x, sp - 104 ≤ x → x < sp → M'[x]? = M[x]?) : HFacts M' ra s0 v sp := by
  have := hf.k.sp_ge
  have hr : ∀ k, sp - 104 ≤ k → k + 8 ≤ sp → bytesT8 M' k = bytesT8 M k := fun k h1 h2 =>
    bytesT8_congr fun x h3 h4 => hs x (by omega) (by omega)
  exact { k := hf.k, ra_al := hf.ra_al
          ra_v := (hr _ (by omega) (by omega)).trans hf.ra_v, s0_v := (hr _ (by omega) (by omega)).trans hf.s0_v
          s1_v := (hr _ (by omega) (by omega)).trans hf.s1_v, s2_v := (hr _ (by omega) (by omega)).trans hf.s2_v
          s3_v := (hr _ (by omega) (by omega)).trans hf.s3_v, s4_v := (hr _ (by omega) (by omega)).trans hf.s4_v
          s5_v := (hr _ (by omega) (by omega)).trans hf.s5_v, s6_v := (hr _ (by omega) (by omega)).trans hf.s6_v
          s7_v := (hr _ (by omega) (by omega)).trans hf.s7_v, s8_v := (hr _ (by omega) (by omega)).trans hf.s8_v
          s9_v := (hr _ (by omega) (by omega)).trans hf.s9_v, s10_v := (hr _ (by omega) (by omega)).trans hf.s10_v
          s11_v := (hr _ (by omega) (by omega)).trans hf.s11_v }

/-- The column bound: the carry plus a column fits in 64 bits (`MP_MAXFAST`). -/
theorem col_bnd {a b : MpInt} (ha : a.ShapeU) (hb : b.ShapeU) (hm : min a.used b.used ≤ 256) (k : Nat) :
    combaW (col a.digit b.digit a.used b.used) k + col a.digit b.digit a.used b.used k < 2 ^ 64 := by
  have hcl : ∀ k, col a.digit b.digit a.used b.used k + 2 ^ 36 ≤ 2 ^ 64 := fun k => by
    by_cases h0 : b.used = 0
    · rw [h0, col_zero_ub]; omega
    · rw [← colC_eq _ _ _ _ k (by omega)]
      exact colC_room ha.digit_lt hb.digit_lt _ _ k (by omega) hm
  have := combaW_lt hcl k
  have := hcl k
  omega

/-- Off the frame is off `W` (`omega` exceeds the recursion depth on this one). -/
theorem offW {sp x : Nat} (hx : x < sp - 2192 ∨ sp ≤ x) : x < sp - 2160 ∨ sp - 112 ≤ x := by
  rcases hx with hx | hx
  · exact Or.inl (Nat.lt_of_lt_of_le hx (Nat.sub_le_sub_left (by decide) sp))
  · exact Or.inr (Nat.le_trans (Nat.sub_le sp 112) hx)

/-- The loop's facts, on every array state over the snapshot `m5`. -/
theorem loopH (h : Ent m sp pa adp pb bdp pc cdp dg a b c ra) :
    LoopH (writeLog (writeLog m (proLog ra s0 v sp pc)) (spLog sp a.used b.used bdp)) sp a.used b.used
      (min dg (a.used + b.used)) adp bdp a.digit b.digit := by
  have := h.sp_ge; have hua := h.sa.used_le; have hub := h.sb.used_le; have huab := h.uab; have hdw := h.dg_w
  have hkad := h.k_ad; have hkbd := h.k_bd; have hkt := h.k_t
  have hra : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using h.ga.ds
  have hrb : Ram bdp (4 * b.alloc) := by simpa [Layout.sizeofDigit] using h.gb.ds
  refine { ch := fun M f hA => ?_, bnd := col_bnd h.sa h.sb h.maxf, pa_lt := by omega, pa_w := by omega }
  have hW : ∀ x, (x < sp - 2160 ∨ sp - 112 ≤ x) → M[x]? =
      (writeLog (writeLog m (proLog ra s0 v sp pc)) (spLog sp a.used b.used bdp))[x]? := fun x hx => hA.outW this hx
  clear hA
  have hoff : ∀ x, (x < sp - 2192 ∨ sp ≤ x) → M[x]? = m[x]? := fun x hx =>
    (hW x (offW hx)).trans ((writeLog_out _ _ _ (inK_out hx (inK_sp this _ _ _))).trans (h.offK (inK_pro this) x hx))
  exact
    { k := h.kf
      sf := { bdp_v := by
                rw [bytesT8_congr fun x h1 h2 => hW x (by omega)]
                exact bytesT8_log _ _ 0 _ _ rfl (by simp [spLog, OutLRange]; omega)
              s16_v := by
                rw [bytesT8_congr fun x h1 h2 => hW x (by omega)]
                exact bytesT8_log _ _ 1 _ _ rfl (by simp [spLog, OutLRange]; omega)
              s24_v := by
                rw [bytesT8_congr fun x h1 h2 => hW x (by omega)]
                exact bytesT8_log _ _ 2 _ _ rfl (by simp [spLog, OutLRange]) }
      img := Img.of_text h.img fun x h1 h2 => hoff x (by simp only [textBase, textLen] at *; omega)
      rdA := fun i hi =>
        { r := hra.sub (by omega) (by omega)
          v := by
            rw [bytesT4_congr fun x h1 h2 => hoff x (by omega)]
            simpa [Layout.sizeofDigit] using h.ra_.digits i (by omega)
          lt := by have := h.sa.digit_lt i; simpa [radix, Layout.digitBits] using this }
      rdB := fun i hi =>
        { r := hrb.sub (by omega) (by omega)
          v := by
            rw [bytesT4_congr fun x h1 h2 => hoff x (by omega)]
            simpa [Layout.sizeofDigit] using h.rb.digits i (by omega)
          lt := by have := h.sb.digit_lt i; simpa [radix, Layout.digitBits] using this }
      ua_lt := by omega, ub_lt := by omega, pa_le := by omega, pa_w := by omega
      ha := by have := hra.hi_le; omega
      hb4 := by have := hrb.lo_ge; omega }

/-- The tail's facts on a snapshot after frame stores whose saves read back. -/
theorem tailF (h : Ent m sp pa adp pb bdp pc cdp dg a b c ra) {l : List WEntry} (hl : InK sp l) (q : Nat)
    (hq : q ≤ dg) (hf : HFacts (writeLog m l) ra s0 v sp)
    (hpc : bytesT8 (writeLog m l) (sp - 2184) = BitVec.ofNat 64 pc) :
    TailF (writeLog m l) ra s0 v sp pc cdp c q :=
  { k := h.kf, hf := hf, pc_v := hpc, rc0 := h.mpK hl h.rc h.k_cs h.k_cd, gc := h.gc, sc := h.sc
    room := by have := h.room; omega, pa_w := by have := h.dg_w; omega, img := h.imgK hl
    k_c := h.k_cs, k_d := h.k_cd, k_t := h.k_t, t_c := h.t_cs, t_d := h.t_cd }

theorem fastPost {c' : MpInt} {q : Nat} (hq : q = min dg (a.used + b.used))
    (h : FastOut c c' (mulFastDigit a b q) q) : MulFastPost a b c c' dg := by
  subst hq
  exact { alloc := h.alloc, len := h.len, digit := h.digit, used := h.used, sign := h.sign }

/-- **`s_mp_mul_digs_fast` from the entry**, for any placement meeting `Ent`. -/
theorem whole (h : Ent m sp pa adp pb bdp pc cdp dg a b c ra) :
    Triple (At 0x800042f0#64 (entL ra s0 v sp pa pb pc dg) m (kF v) outp)
      (RetE m v outp sp pc cdp dg a b c ra s0) := by
  have hk := h.kf; have := h.sp_ge; have hdw := h.dg_w; have huab := h.uab
  have hua := h.sa.used_le; have hub := h.sb.used_le; have hcl := h.sc.alloc_lt; have hroom := h.room
  have hst := h.gc.st
  simp only [Layout.sizeofMpInt] at hst
  -- the prologue's memories
  have e2 : writeLog (writeLog m (log1a s0 v sp)) (log1b ra v sp) = writeLog m (log1a s0 v sp ++ log1b ra v sp) :=
    (writeLog_append _ _ _).symm
  have e3 : writeLog (writeLog m (log1a s0 v sp ++ log1b ra v sp)) (log2 v sp) =
      writeLog m (log1a s0 v sp ++ log1b ra v sp ++ log2 v sp) := (writeLog_append _ _ _).symm
  have e4 : writeLog (writeLog m (log1a s0 v sp ++ log1b ra v sp ++ log2 v sp)) [(sp - 2184, 8, BitVec.ofNat 64 pc)] =
      writeLog m (proLog ra s0 v sp pc) := by rw [← writeLog_append]; rfl
  have k1 : InK sp (log1a s0 v sp) := by simp only [log1a, InK, and_true]; omega
  have k2 : InK sp (log1a s0 v sp ++ log1b ra v sp) := by
    simp only [log1a, log1b, List.cons_append, List.nil_append, InK, and_true]; omega
  have k3 : InK sp (log1a s0 v sp ++ log1b ra v sp ++ log2 v sp) := by
    simp only [log1a, log1b, log2, List.cons_append, List.nil_append, InK, and_true]; omega
  have k4 := inK_pro (ra := ra) (s0 := s0) (v := v) (pc := pc) this
  have hp1 : P1Facts m pc dg c.alloc :=
    { rc := hst, al_v := by simpa [Layout.offAlloc] using h.rc.alloc, al_lt := hcl, dg_lt := by omega }
  have hpro : Triple (At 0x800042f0#64 (entL ra s0 v sp pa pb pc dg) m (kF v) outp)
      (At 0x80004348#64 (p3L v sp pa pb dg) (writeLog m (proLog ra s0 v sp pc)) (kF v) outp) := by
    refine Triple.seq (p1a_step ra s0 v outp sp pa pb pc dg c.alloc m h.img.sMpMulDigsFast hk hp1) ?_
    refine Triple.seq (p1d_step ra s0 v outp sp pa pb pc dg c.alloc _ (h.imgK k1).sMpMulDigsFast hk) ?_
    rw [e2]
    refine Triple.seq (p1b_step ra s0 v outp sp pa pb pc dg c.alloc _ (h.imgK k2).sMpMulDigsFast hk) ?_
    rw [e3]
    have := p1c_step ra s0 v outp sp pa pb pc dg c.alloc _ (h.imgK k3).sMpMulDigsFast hk hcl hroom
    rwa [e4] at this
  -- the snapshot facts, then the snapshot as a variable
  have ha4 := h.mpK k4 h.ra_ h.k_as h.k_ad
  have hb4 := h.mpK k4 h.rb h.k_bs h.k_bd
  have hp2 : P2Facts (writeLog m (proLog ra s0 v sp pc)) pa pb a.used b.used :=
    { ra_ := by simpa [Layout.sizeofMpInt] using h.ga.st, rb := by simpa [Layout.sizeofMpInt] using h.gb.st
      ua_v := by simpa [Layout.offUsed] using ha4.used, ub_v := by simpa [Layout.offUsed] using hb4.used
      ua_lt := by omega, ub_lt := by omega }
  have hp3 : P3Facts (writeLog m (proLog ra s0 v sp pc)) pa pb adp bdp :=
    { ra_ := hp2.ra_, rb := hp2.rb, adp_v := by simpa [Layout.offDp] using ha4.dpv
      bdp_v := by simpa [Layout.offDp] using hb4.dpv }
  have hc4 := (h.imgK k4).sMpMulDigsFast
  have ht4 := tailF h k4 0 (Nat.zero_le _) (hfacts4 (s0 := s0) (v := v) h) (pcv4 h)
  have hoff4 := h.offK k4
  have hL5 := loopH (s0 := s0) (v := v) h
  have k5 := inK_sp this a.used b.used bdp
  have hf5 := (hfacts4 (s0 := s0) (v := v) h).mono (M' := writeLog (writeLog m (proLog ra s0 v sp pc))
    (spLog sp a.used b.used bdp)) fun x h1 h2 => writeLog_out _ _ _ (by simp [spLog, OutL]; omega)
  have hpc5 : bytesT8 (writeLog (writeLog m (proLog ra s0 v sp pc)) (spLog sp a.used b.used bdp)) (sp - 2184) =
      BitVec.ofNat 64 pc := by
    rw [bytesT8_congr fun x h1 h2 => writeLog_out _ _ _ (by simp [spLog, OutL]; omega)]; exact pcv4 h
  have hm5 : ∀ x, (x < sp - 2192 ∨ sp ≤ x) →
      (writeLog (writeLog m (proLog ra s0 v sp pc)) (spLog sp a.used b.used bdp))[x]? = m[x]? := fun x hx =>
    (writeLog_out _ _ _ (inK_out hx k5)).trans (h.offK k4 x hx)
  have ht5 : TailF (writeLog (writeLog m (proLog ra s0 v sp pc)) (spLog sp a.used b.used bdp)) ra s0 v sp pc cdp c
      (min dg (a.used + b.used)) :=
    { k := hk, hf := hf5, pc_v := hpc5
      rc0 := h.rc.of_agree (fun y h3 h4 => hm5 y (by have := h.k_cs; omega))
        (fun y h3 h4 => hm5 y (by have := h.k_cd; omega))
      gc := h.gc, sc := h.sc, room := by omega, pa_w := by omega
      img := Img.of_text h.img fun x h1 h2 => hm5 x (by have := h.k_t; simp only [textBase, textLen] at *; omega)
      k_c := h.k_cs, k_d := h.k_cd, k_t := h.k_t, t_c := h.t_cs, t_d := h.t_cd }
  refine Triple.seq hpro ?_
  generalize writeLog m (proLog ra s0 v sp pc) = M4 at *
  have hpq : Triple (At 0x80004348#64 (p3L v sp pa pb dg) M4 (kF v) outp)
      (At 0x8000435c#64 (p4L v sp pa pb dg a.used b.used (min dg (a.used + b.used))) M4 (kF v) outp) := by
    by_cases hlt : dg < a.used + b.used
    · rw [Nat.min_eq_left (by omega)]
      exact Triple.rmap (fun _ h => h) (p2t_step v outp sp pa pb dg a.used b.used _ hc4 hp2 (by omega) hlt)
    · rw [Nat.min_eq_right (by omega)]
      exact Triple.rmap (fun _ h => h) (p2f_step v outp sp pa pb dg a.used b.used _ hc4 hp2 (by omega) (by omega))
  refine Triple.seq hpq ?_
  by_cases hq0 : min dg (a.used + b.used) = 0
  · -- `pa = 0`
    rw [hq0]
    refine Triple.seq (p3z_step v outp sp pa pb dg a.used b.used _ hc4) ?_
    exact Triple.rmap (fun cf ⟨c', M, hat, hr, hfo, hfr⟩ => ⟨c', M, hat, hr, fastPost hq0.symm hfo,
        fun x h1 h2 h3 => (hfr x h1 h2 h3).trans (hoff4 x h1)⟩)
      (tailZ ht4 pa pb dg a.used b.used _ (fun j => by simp [mulFastDigit]))
  -- `pa > 0`: the loop over the snapshot after the spills
  refine Triple.seq (p3_step v outp sp pa pb dg a.used b.used _ adp bdp _ hc4 hk hp3 (by omega) (by omega)
    (by omega) (by omega) (by omega)) ?_
  generalize writeLog M4 (spLog sp a.used b.used bdp) = M5 at *
  have hAi : ArrFrm (ρW sp) () M5 M5 (sp - 2160) 512
      (ovl (combaD (col a.digit b.digit a.used b.used)) (fun j => (bytesT4 M5 (sp - 2160 + 4 * j)).toNat) 0) :=
    ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; intro j _; simp)
  have hinit : Triple (At 0x8000439c#64 (oH sp a.used b.used (min dg (a.used + b.used)) adp 0 0
        (BitVec.ofNat 64 dg) (BitVec.ofNat 64 pa) v.s.s9 v.s.s10) M5 (kF v) outp)
      (fun cf => ∃ j0 j2 j9 j10 : BitVec 64, WSt M5 v outp sp 0x8000439c#64
        (oH sp a.used b.used (min dg (a.used + b.used)) adp 0 (combaW (col a.digit b.digit a.used b.used) 0)
          j0 j2 j9 j10)
        (ovl (combaD (col a.digit b.digit a.used b.used)) (fun j => (bytesT4 M5 (sp - 2160 + 4 * j)).toNat) 0) cf) :=
    Triple.rmap (fun cf h => ⟨_, _, _, _, M5, hAi, h⟩) Triple.rfl
  refine Triple.seq hinit ?_
  refine Triple.seq (loop (v := v) (outp := outp) hL5 (by omega) 0 (by omega)) ?_
  exact Triple.rmap (fun cf ⟨c', M, hat, hr, hfo, hfr⟩ => ⟨c', M, hat, hr, fastPost rfl hfo,
      fun x h1 h2 h3 => (hfr x h1 h2 h3).trans (hm5 x h1)⟩)
    (tailM ht5 (by omega) (by omega) a.used b.used adp _ _ _ (combaD_lt _))

end whole

end Tom.Machine.Fn.MulFast
