import Tom.Machine.Fn.SqrFastLoop
import Tom.Machine.Fn.MulFastCore

/-!
# `s_mp_sqr_fast` on the machine: the tail and the whole function, for any placement

After the column loop (`Fn/SqrFastLoop.lean`): `b->used := pa`, the copy loop
`b->dp[j] := W[j] & MP_MASK` (an in-place array state on `b`'s digits),
`memset` of the old digits above, `mp_clamp(b)`, the epilogue (`tailM`;
`a->used = 0`: `tailZ`); `whole` chains the prologue, the loop and the tails
from `SEnt`, plain facts any placement meets (`b` may be `a`: the loop reads
`a` into `W` before `b` is written). The tail reuses `s_mp_mul_digs_fast`'s
`FastOut`/`cMid`.
-/

namespace Tom.Machine.Fn.SqrFast

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api.Libgcc
open Tom.Machine.Fn.MulFast (kF kFKeys abiL msL clL rL DRead pS WSt ρW FastOut cMid cMid_digit)

/-! ## The calls after the copy -/

/-- `memset(b->dp + pa, 0, 4 (olduse - pa))` at `7254`, back at `7258`. -/
theorem memset_call (v : Abi) (outp : Array String) (u : Abi) (cdp pa ou : Nat) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hg : u.gp = v.gp) (ht : u.tp = v.tp)
    (hP : Memset.Pre M (cdp + 4 * pa) 0 (4 * (ou - pa))) :
    Triple (At 0x80007254#64 (msL u cdp pa ou) M (kF v) outp)
      (fun c => ∃ M', At 0x80007258#64 (abiL u) M' (kF v) outp c ∧
        Memset.Post M (cdp + 4 * pa) (4 * (ou - pa)) 0#8 M') :=
  jal_call (pc := 0x80007254#64) (w := 0x150020ef#32) (imm := 0x002150#21) (Larg := msL u cdp pa ou)
    (L0 := Memset.entryL 0x80007258#64 (cdp + 4 * pa) 0#64 (4 * (ou - pa))) (K := u.keep)
    hc (by decide +kernel) (by decide) (by decide) (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide) (by decide) (fun p hp => hp)
    (by simp [msL, abiL, sKeepL, keysG]) (by simp [kF, keysG])
    (by simp [Memset.entryL, msL, Sail.BitVec.addInt])
    (by simp [Abi.keep, sKeepL, msL, abiL, kF, hg, ht])
    (Triple.rmap (fun c ⟨M', hat, hpost⟩ => ⟨M', hat.reshape (by simp [abiL, Abi.keep, sKeepL])
        (by simp [kF, Abi.keep, sKeepL, hg, ht]), hpost⟩)
      (Memset.correct_zero 0x80007258#64 u outp M _ _ (by decide) hP))

/-- `mp_clamp(b)` at `725c`, back at `7260`. -/
theorem clamp_call (v : Abi) (outp : Array String) (u : Abi) (pc cdp : Nat) (cm : MpInt) (M : Mem)
    (hc : CodeAt M sMpSqrFastBase sMpSqrFastCode) (hg : u.gp = v.gp) (ht : u.tp = v.tp)
    (hP : Clamp.Pre M pc cdp cm) :
    Triple (At 0x8000725c#64 (clL u pc) M (kF v) outp)
      (fun c => ∃ a' M', At 0x80007260#64 [(2, u.sp)] M' (kF v) outp c ∧ Clamp.Post M pc cdp cm a' M') :=
  jal_call (pc := 0x8000725c#64) (w := 0xd7dfd0ef#32) (imm := 0x1fdd7c#21) (Larg := clL u pc)
    (L0 := [(1, 0x80007260#64), (10, BitVec.ofNat 64 pc)]) (K := u.keep)
    hc (by decide +kernel) (by decide) (by decide) (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide) (by decide) (fun p hp => hp)
    (by simp [clL, abiL, sKeepL, keysG]) (by simp [kF, keysG])
    (by simp [clL, Sail.BitVec.addInt])
    (by simp [Abi.keep, sKeepL, clL, abiL, kF, hg, ht])
    (Triple.rmap (fun c ⟨a', M', hat, hpost⟩ => ⟨a', M', hat.reshape (by simp [Abi.keep])
        (by simp [kF, Abi.keep, sKeepL, hg, ht]), hpost⟩)
      (Clamp.correct 0x80007260#64 u outp pc cdp cm M (by decide) hP))

/-! ## After the loop -/

section tail
variable {m0 : Mem} {v : Abi} {outp : Array String} {ra s0 : BitVec 64} {sp pc cdp pa : Nat} {c0 : MpInt}

/-- What the code after the loop reads, and where things are (`b` is `c0` at `pc`). -/
structure TailF (m0 : Mem) (ra s0 : BitVec 64) (v : Abi) (sp pc cdp : Nat) (c0 : MpInt) (pa : Nat) : Prop where
  k : KS sp
  hf : HFacts m0 ra s0 v sp
  pc_v : bytesT8 m0 (sp - 2192) = BitVec.ofNat 64 pc
  rc0 : MpAt m0 pc cdp c0
  gc : MpGeom pc cdp c0.alloc
  sc : c0.Shape
  room : pa ≤ c0.alloc
  pa_w : pa ≤ 512
  img : Img m0
  k_c : sp ≤ pc ∨ pc + 24 ≤ sp - 2208
  k_d : sp ≤ cdp ∨ cdp + 4 * c0.alloc ≤ sp - 2208
  k_t : sp ≤ textBase ∨ textBase + textLen ≤ sp - 2208
  t_c : textBase + textLen ≤ pc ∨ pc + 24 ≤ textBase
  t_d : textBase + textLen ≤ cdp ∨ cdp + 4 * c0.alloc ≤ textBase

def RetF (m0 : Mem) (v : Abi) (outp : Array String) (sp pc cdp : Nat) (c0 : MpInt) (g : Nat → Nat) (pa : Nat)
    (ra s0 : BitVec 64) (cf : Vsa.Machine.Config) : Prop :=
  ∃ c' M, At ra (rL ra s0 v sp) M (kF v) outp cf ∧ MpAt M pc cdp c' ∧ FastOut c0 c' g pa ∧
    ∀ x, (x < sp - 2208 ∨ sp ≤ x) → (x < pc ∨ pc + 24 ≤ x) → (x < cdp ∨ cdp + 4 * c0.alloc ≤ x) → M[x]? = m0[x]?

/-- Off `W`, `b`'s struct and `b`'s digits. -/
def Off (sp pc cdp al x : Nat) : Prop :=
  (x < sp - 2160 ∨ sp - 112 ≤ x) ∧ (x < pc ∨ pc + 24 ≤ x) ∧ (x < cdp ∨ cdp + 4 * al ≤ x)

theorem TailF.imgOf (h : TailF m0 ra s0 v sp pc cdp c0 pa) {M : Mem}
    (hM : ∀ x, Off sp pc cdp c0.alloc x → M[x]? = m0[x]?) : Img M :=
  Img.of_text h.img fun x h1 h2 => hM x (by
    have := h.k_t; have := h.t_c; have := h.t_d; have := h.k.sp_ge
    unfold Off; simp only [textBase, textLen] at *; omega)

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

theorem TailF.hOf (h : TailF m0 ra s0 v sp pc cdp c0 pa) {M : Mem}
    (hM : ∀ x, Off sp pc cdp c0.alloc x → M[x]? = m0[x]?) : HFacts M ra s0 v sp :=
  have := h.k.sp_ge; have hkc := h.k_c; have hkd := h.k_d
  h.hf.mono fun x h1 h2 => hM x (by unfold Off; omega)

theorem TailF.pcOf (h : TailF m0 ra s0 v sp pc cdp c0 pa) {M : Mem}
    (hM : ∀ x, Off sp pc cdp c0.alloc x → M[x]? = m0[x]?) : bytesT8 M (sp - 2192) = BitVec.ofNat 64 pc := by
  have := h.k.sp_ge; have hkc := h.k_c; have hkd := h.k_d
  rw [bytesT8_congr fun x h3 h4 => hM x (by unfold Off; omega)]; exact h.pc_v

/-- From `7258`: `mp_clamp(b)` and the epilogue. -/
theorem tail7258 (h : TailF m0 ra s0 v sp pc cdp c0 pa) (u : Abi) (hsp : u.sp = BitVec.ofNat 64 (sp - 2208))
    (hgp : u.gp = v.gp) (htp : u.tp = v.tp) (g : Nat → Nat) (hglt : ∀ j, g j < radix) (hgz : ∀ j, pa ≤ j → g j = 0)
    (M : Mem) (hM : ∀ x, Off sp pc cdp c0.alloc x → M[x]? = m0[x]?) (hrc : MpAt M pc cdp (cMid c0 g pa)) :
    Triple (At 0x80007258#64 (abiL u) M (kF v) outp) (RetF m0 v outp sp pc cdp c0 g pa ra s0) := by
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
  refine Triple.seq (gc_step v outp u sp pc M himg.sMpSqrFast hk hsp (h.pcOf hM))
    (Triple.seq (clamp_call v outp u pc cdp _ M himg.sMpSqrFast hgp htp hpre) ?_)
  intro cf ⟨c', M', hat, hpost⟩
  have hM' : ∀ x, Off sp pc cdp c0.alloc x → M'[x]? = m0[x]? := fun x hx =>
    (hpost.frame x (by unfold Off at hx; omega)).trans (hM x hx)
  have hat' : At 0x80007260#64 [(2, BitVec.ofNat 64 (sp - 2208))] M' (kF v) outp cf := by rw [← hsp]; exact hat
  refine Triple.rmap (fun cf hr => ⟨c', _, hr, hpost.repr, ?_, fun x h1 h2 h3 => ?_⟩)
    (h_step ra s0 v outp sp M' (h.imgOf hM').sMpSqrFast (h.hOf hM')) cf hat'
  · have hcp := hpost.clamp
    exact { alloc := hcp.alloc
            len := by rw [hcp.digits]; simp [cMid]
            digit := by rw [hcp.digit, hdig]
            used := by rw [hcp.used, hdig]; rfl
            sign := by rw [hcp.sign]; rfl }
  · exact (hpost.frame x (by omega)).trans (hM x (by unfold Off; omega))

end tail

section tail2
variable {m0 : Mem} {v : Abi} {outp : Array String} {ra s0 : BitVec 64} {sp pc cdp : Nat} {c0 : MpInt}

theorem _root_.Tom.Machine.ArrFrm.outU {m0 M : Mem} {b al : Nat} {f : Nat → Nat}
    (hA : ArrFrm (fun _ : Unit => (⟨b, 4 * al⟩ : Iv)) () m0 M b al f) {x : Nat} (hx : x < b ∨ b + 4 * al ≤ x) :
    M[x]? = m0[x]? :=
  hA.fr x fun h => by
    rcases h with h | h
    · have h1 : b ≤ x := h.1
      have h2 : x < b + 4 * al := h.2
      omega
    · exact h.elim

/-- **The tail of the main path**: from the last column's store point at `71ec` to the return. -/
theorem tailM (h : TailF m0 ra s0 v sp pc cdp c0 (2 * ua)) (hua1 : 1 ≤ ua) (hua : ua < 256)
    (hpa : bytesT8 m0 (sp - 2168) = BitVec.ofNat 64 (2 * ua)) (adp s : Nat) (D old : Nat → Nat)
    (hD : ∀ j, D j < radix) :
    Triple (fun cf => ∃ j0 j9 j10 j11 : BitVec 64, WSt m0 v outp sp 0x800071ec#64
        (sP sp ua adp (2 * ua - 1) s j0 j9 j10 j11) (ovl D old (2 * ua)) cf)
      (RetF m0 v outp sp pc cdp c0 (fun j => if j < 2 * ua then D j else 0) (2 * ua) ra s0) := by
  intro cf ⟨j0, j9, j10, j11, M, hA, hat⟩
  have hk := h.k; have := hk.sp_ge; have hkc := h.k_c; have hkd := h.k_d; have htd := h.t_d; have htc := h.t_c
  have hroom := h.room; have hpw := h.pa_w; have hgd := h.gc.disj; have hcu := h.sc.used_le
  have hal := h.sc.alloc_lt; have hkt := h.k_t
  simp only [Layout.sizeofMpInt, Layout.sizeofDigit] at hgd
  have hW : ∀ x, (x < sp - 2160 ∨ sp - 112 ≤ x) → M[x]? = m0[x]? := fun x hx => hA.outW (by omega) hx
  have hMo : ∀ x, Off sp pc cdp c0.alloc x → M[x]? = m0[x]? := fun x hx => hW x hx.1
  have hst : ∀ x, pc ≤ x → x < pc + 24 → M[x]? = m0[x]? := fun x h1 h2 => hW x (by omega)
  have hrcM : MpAt M pc cdp c0 := h.rc0.of_agree hst (fun x h1 h2 => hW x (by omega))
  have himg := h.imgOf hMo
  have hrd : Ram cdp (4 * c0.alloc) := by simpa [Layout.sizeofDigit] using h.gc.ds
  have hb : BFacts M sp pc c0.used cdp ua :=
    { rb := by simpa [Layout.sizeofMpInt] using h.gc.st, pb_al := h.gc.st_al, pb_v := h.pcOf hMo
      pa_v := by rw [bytesT8_congr fun x h1 h2 => hW x (by omega)]; exact hpa
      ou_v := by simpa [Layout.offUsed] using hrcM.used
      bdp_v := by simpa [Layout.offDp] using hrcM.dpv
      ou_lt := by omega
      code_b := by simp only [sMpSqrFastBase, textBase, textLen] at *; omega }
  let g : Nat → Nat := fun j => if j < 2 * ua then D j else 0
  have hglt : ∀ j, g j < radix := fun j => by simp only [g]; split; exact hD j; exact radix_pos
  have hgz : ∀ j, 2 * ua ≤ j → g j = 0 := fun j hj => by simp only [g]; rw [if_neg (by omega)]
  have hM1 : ∀ x, Off sp pc cdp c0.alloc x → (writeLog M [(pc, 4, BitVec.ofNat 64 (2 * ua))])[x]? = m0[x]? :=
    fun x hx => (writeLog_out _ _ _ (by simp [OutL]; unfold Off at hx; omega)).trans (hMo x hx)
  have hrc1 := hrcM.set_used h.gc (2 * ua) (by omega)
  refine Triple.seq (f1_step v outp sp ua adp (2 * ua - 1) s pc cdp c0.used j0 j9 j10 j11 M himg.sMpSqrFast hk hb
    (by omega)) (Triple.seq (f1b_step v outp sp ua adp (2 * ua - 1) s pc cdp c0.used j0 j9 j10 j11 M himg.sMpSqrFast
      hb (by omega)) ?_) cf hat
  -- the copy loop, an array state on `b`'s digits since `M1`
  generalize hm1 : writeLog M [(pc, 4, BitVec.ofNat 64 (2 * ua))] = M1 at hM1 hrc1
  have hA0 : ArrFrm (fun _ : Unit => (⟨cdp, 4 * c0.alloc⟩ : Iv)) () M1 M1 cdp c0.alloc (ovl g c0.digit 0) :=
    ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; exact hrc1.arr)
  have hMB : ∀ {M' : Mem} {f : Nat → Nat}, ArrFrm (fun _ : Unit => (⟨cdp, 4 * c0.alloc⟩ : Iv)) () M1 M' cdp c0.alloc f →
      ∀ x, Off sp pc cdp c0.alloc x → M'[x]? = m0[x]? := fun hB x hx =>
    (hB.outU hx.2.2).trans (hM1 x hx)
  have hcf : ∀ {M' : Mem} {f : Nat → Nat} (j : Nat), j < 2 * ua →
      ArrFrm (fun _ : Unit => (⟨cdp, 4 * c0.alloc⟩ : Iv)) () M1 M' cdp c0.alloc f → CFacts M' sp cdp ua j (D j) :=
    @fun M' _ j hj hB =>
      { k := hk, rd := hrd.sub (by omega) (by omega), al := h.gc.ds_al
        code_b := by simp only [sMpSqrFastBase, textBase, textLen] at *; omega
        j_lt := by omega
        w_v := by
          have e1 : ∀ x, sp - 2160 + 4 * j ≤ x → x < sp - 2160 + 4 * j + 4 → M'[x]? = M[x]? := fun x h1 h2 =>
            (hB.outU (by omega)).trans (by rw [← hm1]; exact writeLog_out _ _ _ (by simp [OutL]; omega))
          rw [bytesT4_congr e1]
          have := hA.arr j (by omega); simp only [ovl, if_pos (show j < 2 * ua by omega)] at this; exact this
        w_lt := by have := hD j; simpa [radix, Layout.digitBits] using this
        hb := by have := hrd.hi_le; omega }
  have hcode : ∀ {M' : Mem} {f : Nat → Nat}, ArrFrm (fun _ : Unit => (⟨cdp, 4 * c0.alloc⟩ : Iv)) () M1 M' cdp c0.alloc f →
      CodeAt M' sMpSqrFastBase sMpSqrFastCode := fun hB => (h.imgOf (hMB hB)).sMpSqrFast
  have hcopy : ∀ j, j < 2 * ua →
      Triple (ASt (fun _ : Unit => (⟨cdp, 4 * c0.alloc⟩ : Iv)) () M1 cdp c0.alloc (kF v) outp 0x80007218#64
          (cL sp ua adp (2 * ua - 1) s cdp c0.used j j0 j9 j10 j11) (ovl g c0.digit j))
        (ASt (fun _ : Unit => (⟨cdp, 4 * c0.alloc⟩ : Iv)) () M1 cdp c0.alloc (kF v) outp 0x80007230#64
          (cL sp ua adp (2 * ua - 1) s cdp c0.used (2 * ua) j0 j9 j10 j11) (ovl g c0.digit (2 * ua))) := by
    refine Triple.countup (fun j hj => ?_) ?_
    · exact ASt.store (fun M' hB => c_step v outp sp ua adp (2 * ua - 1) s cdp c0.used j (D j) j0 j9 j10 j11 M'
        (hcode hB) (hcf j (by omega) hB) hj) (by omega)
        (by simp only [g, if_pos (show j < 2 * ua by omega)]; have := hD j; simp only [radix, Layout.digitBits] at this
            omega) (by omega)
    · have := ASt.store (g := g) (old := c0.digit) (i := 2 * ua - 1) (fun M' hB => ce_step v outp sp ua adp (2 * ua - 1) s
        cdp c0.used (2 * ua - 1) (D (2 * ua - 1)) j0 j9 j10 j11 M' (hcode hB) (hcf (2 * ua - 1) (by omega) hB)
        (by omega)) (by omega)
        (by simp only [g, if_pos (show 2 * ua - 1 < 2 * ua by omega)]; have := hD (2 * ua - 1)
            simp only [radix, Layout.digitBits] at this; omega) (by omega)
      rwa [show 2 * ua - 1 + 1 = 2 * ua by omega] at this
  intro cf hat1
  refine Triple.seq (hcopy 0 (by omega)) ?_ cf ⟨M1, hA0, hat1⟩
  intro cf ⟨M2, hA2, hat2⟩
  have hfin : ∀ {M3 : Mem}, ArrFrm (fun _ : Unit => (⟨cdp, 4 * c0.alloc⟩ : Iv)) () M1 M3 cdp c0.alloc g →
      MpAt M3 pc cdp (cMid c0 g (2 * ua)) := fun hA3 =>
    hrc1.of_hdr (fun x h1 h2 => hA3.outU (by omega))
      (by rw [cMid_digit (fun j hj => hgz j (by omega))]; exact hA3.arr) rfl rfl rfl
  have hcode2 := hcode hA2
  by_cases hou : c0.used ≤ 2 * ua
  · have hA3 := hA2.congr fun j hj => by
      simp only [ovl]; split
      · rfl
      · rw [h.sc.high_zero j (by omega), hgz j (by omega)]
    exact Triple.seq (f2t_step v outp sp ua adp (2 * ua - 1) s cdp c0.used j0 j9 j10 j11 M2 hcode2 hou hua1
        (by omega) (by omega))
      (tail7258 h (sAbi v sp ua adp (2 * ua - 1) s j0 j9 j10 j11) (by simp only [sAbi]) (by simp only [sAbi])
        (by simp only [sAbi]) g hglt hgz M2 (hMB hA2) (hfin hA3)) cf hat2
  have hms : Memset.Pre M2 (cdp + 4 * (2 * ua)) 0 (4 * (c0.used - 2 * ua)) :=
    { byte := by decide, code := (h.imgOf (hMB hA2)).memset
      ram := hrd.sub (by omega) (by omega)
      code_off := by
        have : memsetCode.length = 55 := rfl
        rw [this]; simp only [memsetBase, textBase, textLen] at *; omega }
  have := hrd.hi_le
  refine Triple.seq (f2m_step v outp sp ua adp (2 * ua - 1) s cdp c0.used j0 j9 j10 j11 M2 hcode2 (by omega) hua1
      (by omega) (by omega))
    (Triple.seq (memset_call v outp (sAbi v sp ua adp (2 * ua - 1) s j0 j9 j10 j11) cdp (2 * ua) c0.used M2 hcode2
      (by simp only [sAbi]) (by simp only [sAbi]) hms) ?_) cf hat2
  intro cf ⟨M3, hat3, hp3⟩
  have hA3 := (hA2.fill (k := c0.used) (by omega) hcu
      (fun t ht => hp3.fill t (by omega)) (fun x hx => hp3.frame x (by omega))
      (fun j h1 _ => hgz j h1)).congr fun j hj => by
    simp only [ovl]; split
    · rfl
    · rw [h.sc.high_zero j (by omega), hgz j (by omega)]
  exact tail7258 h (sAbi v sp ua adp (2 * ua - 1) s j0 j9 j10 j11) (by simp only [sAbi]) (by simp only [sAbi])
    (by simp only [sAbi]) g hglt hgz M3 (hMB hA3) (hfin hA3) cf hat3

/-- **The tail of the `a->used = 0` path**: from `72b0` to the return. -/
theorem tailZ (h : TailF m0 ra s0 v sp pc cdp c0 0) (pa : Nat) (g : Nat → Nat) (hg : ∀ j, g j = 0) :
    Triple (At 0x800072b0#64 (zL v sp pa) m0 (kF v) outp) (RetF m0 v outp sp pc cdp c0 g 0 ra s0) := by
  have hk := h.k; have := hk.sp_ge; have hkc := h.k_c; have hkd := h.k_d; have htd := h.t_d; have htc := h.t_c
  have hgd := h.gc.disj; have hcu := h.sc.used_le; have hal := h.sc.alloc_lt; have hst := h.gc.st
  simp only [Layout.sizeofMpInt, Layout.sizeofDigit] at hgd hst
  have hrd : Ram cdp (4 * c0.alloc) := by simpa [Layout.sizeofDigit] using h.gc.ds
  have hm0 : ∀ x, Off sp pc cdp c0.alloc x → m0[x]? = m0[x]? := fun _ _ => rfl
  have hz : ZFacts m0 sp pc c0.used cdp :=
    { rb := hst, pb_v := h.pc_v, ou_v := by simpa [Layout.offUsed] using h.rc0.used
      bdp_v := by simpa [Layout.offDp] using h.rc0.dpv, ou_lt := by omega }
  have himg := h.img
  have hglt : ∀ j, g j < radix := fun j => by rw [hg]; exact radix_pos
  have hgz : ∀ j, 0 ≤ j → g j = 0 := fun j _ => hg j
  have hu : UFacts pc := { rb := hst, pb_al := h.gc.st_al
                           code_b := by simp only [sMpSqrFastBase, textBase, textLen] at *; omega }
  have hrc1 := h.rc0.set_used h.gc 0 (by omega)
  have hM1 : ∀ x, Off sp pc cdp c0.alloc x → (writeLog m0 [(pc, 4, 0#64)])[x]? = m0[x]? :=
    fun x hx => writeLog_out _ _ _ (by simp [OutL]; unfold Off at hx; omega)
  have hfin : ∀ {M : Mem}, ArrFrm (fun _ : Unit => (⟨cdp, 4 * c0.alloc⟩ : Iv)) () (writeLog m0 [(pc, 4, 0#64)]) M
      cdp c0.alloc g → MpAt M pc cdp (cMid c0 g 0) := fun hA =>
    hrc1.of_hdr (fun x h1 h2 => hA.outU (by omega))
      (by rw [cMid_digit (fun j _ => hg j)]; exact hA.arr) rfl rfl rfl
  have hA1 : ArrFrm (fun _ : Unit => (⟨cdp, 4 * c0.alloc⟩ : Iv)) () (writeLog m0 [(pc, 4, 0#64)])
      (writeLog m0 [(pc, 4, 0#64)]) cdp c0.alloc (ovl g c0.digit 0) :=
    ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; exact hrc1.arr)
  refine Triple.seq (z_step v outp sp pa pc c0.used cdp m0 himg.sMpSqrFast hk hz) ?_
  by_cases hou : c0.used = 0
  · rw [hou]
    have hA := hA1.congr (f' := g) fun j hj => by rw [ovl_zero, hg]; exact h.sc.high_zero j (by omega)
    exact Triple.seq (zt_step v outp sp pa pc cdp _ himg.sMpSqrFast hu)
      (tail7258 h (zAbi v sp pa) (by simp only [zAbi]) (by simp only [zAbi]) (by simp only [zAbi])
        g hglt hgz _ hM1 (hfin hA))
  have hms : Memset.Pre (writeLog m0 [(pc, 4, 0#64)]) (cdp + 4 * 0) 0 (4 * (c0.used - 0)) :=
    { byte := by decide, code := (h.imgOf hM1).memset
      ram := hrd.sub (by omega) (by omega)
      code_off := by
        have : memsetCode.length = 55 := rfl
        rw [this]; simp only [memsetBase, textBase, textLen] at *; omega }
  refine Triple.seq (zm_step v outp sp pa pc c0.used cdp _ himg.sMpSqrFast hu (by omega) (by omega))
    (Triple.seq (memset_call v outp (zAbi v sp pa) cdp 0 c0.used _ (h.imgOf hM1).sMpSqrFast
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
  exact tail7258 h (zAbi v sp pa) (by simp only [zAbi]) (by simp only [zAbi]) (by simp only [zAbi])
    g hglt hgz M2 hM2 (hfin hA2) cf hat2

end tail2

/-! ## The whole function, for any placement -/

/-- The prologue's saves and `b`. -/
def proLog (ra s0 : BitVec 64) (v : Abi) (sp pb : Nat) : List WEntry :=
  log1a s0 v sp ++ log1b ra v sp ++ log1c v sp ++ [(sp - 2192, 8, BitVec.ofNat 64 pb)]

/-- What `s_mp_sqr_fast(a, b)` needs, as plain facts (`b` may be `a`). -/
structure SEnt (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (ra : BitVec 64) : Prop where
  ra_ : MpAt m pa adp a
  rb : MpAt m pb bdp b
  sa : a.Shape
  sb : b.Shape
  ga : MpGeom pa adp a.alloc
  gb : MpGeom pb bdp b.alloc
  warr : 2 * a.used + 1 < 512
  room : 2 * a.used ≤ b.alloc
  rs : Ram (sp - 2208) 2208
  sp_al : sp % 16 = 0
  sp_ge : 2208 ≤ sp
  ra_al : ra.toNat % 4 = 0
  img : Img m
  k_as : sp ≤ pa ∨ pa + 24 ≤ sp - 2208
  k_ad : sp ≤ adp ∨ adp + 4 * a.alloc ≤ sp - 2208
  k_bs : sp ≤ pb ∨ pb + 24 ≤ sp - 2208
  k_bd : sp ≤ bdp ∨ bdp + 4 * b.alloc ≤ sp - 2208
  k_t : sp ≤ textBase ∨ textBase + textLen ≤ sp - 2208
  t_bs : textBase + textLen ≤ pb ∨ pb + 24 ≤ textBase
  t_bd : textBase + textLen ≤ bdp ∨ bdp + 4 * b.alloc ≤ textBase

/-- What it leaves, off the frame and `b`: memory as at the entry. -/
def RetE (m : Mem) (v : Abi) (outp : Array String) (sp pb bdp : Nat) (a b : MpInt) (ra s0 : BitVec 64)
    (cf : Vsa.Machine.Config) : Prop :=
  ∃ b' M, At ra (rL ra s0 v sp) M (kF v) outp cf ∧ MpAt M pb bdp b' ∧ SqrFastPost a b b' ∧
    ∀ x, (x < sp - 2208 ∨ sp ≤ x) → (x < pb ∨ pb + 24 ≤ x) → (x < bdp ∨ bdp + 4 * b.alloc ≤ x) → M[x]? = m[x]?

section whole
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt} {ra s0 : BitVec 64}

theorem SEnt.ks (h : SEnt m sp pa adp pb bdp a b ra) : KS sp :=
  { rs := h.rs, sp_al := h.sp_al, sp_ge := h.sp_ge
    code_off := by have := h.k_t; simp only [sMpSqrFastBase, textBase, textLen] at *; omega }

/-- A store log inside the frame `[sp - 2208, sp)`. -/
def InK (sp : Nat) : List WEntry → Prop
  | [] => True
  | e :: l => sp - 2208 ≤ e.1 ∧ e.1 + e.2.1 ≤ sp ∧ InK sp l

theorem inK_out {sp x : Nat} (hx : x < sp - 2208 ∨ sp ≤ x) : ∀ {l : List WEntry}, InK sp l → OutL l x
  | [], _ => trivial
  | _ :: _, ⟨h1, h2, h3⟩ => ⟨by omega, inK_out hx h3⟩

theorem inK_pro (h : 2208 ≤ sp) : InK sp (proLog ra s0 v sp pb) := by
  simp only [proLog, log1a, log1b, log1c, List.cons_append, List.nil_append, InK, and_true]; omega

theorem SEnt.offK (h : SEnt m sp pa adp pb bdp a b ra) {l : List WEntry} (hl : InK sp l) :
    ∀ x, (x < sp - 2208 ∨ sp ≤ x) → (writeLog m l)[x]? = m[x]? := fun x hx => writeLog_out _ _ _ (inK_out hx hl)

theorem hfacts4 (h : SEnt m sp pa adp pb bdp a b ra) :
    HFacts (writeLog m (proLog ra s0 v sp pb)) ra s0 v sp := by
  have := h.sp_ge
  exact { k := h.ks, ra_al := h.ra_al
          s0_v := bytesT8_log _ _ 0 _ _ rfl (by simp [proLog, log1a, log1b, log1c, OutLRange]; omega)
          s8_v := bytesT8_log _ _ 1 _ _ rfl (by simp [proLog, log1a, log1b, log1c, OutLRange]; omega)
          ra_v := bytesT8_log _ _ 2 _ _ rfl (by simp [proLog, log1a, log1b, log1c, OutLRange]; omega)
          s1_v := bytesT8_log _ _ 3 _ _ rfl (by simp [proLog, log1a, log1b, log1c, OutLRange]; omega)
          s2_v := bytesT8_log _ _ 4 _ _ rfl (by simp [proLog, log1a, log1b, log1c, OutLRange]; omega)
          s3_v := bytesT8_log _ _ 5 _ _ rfl (by simp [proLog, log1a, log1b, log1c, OutLRange]; omega)
          s4_v := bytesT8_log _ _ 6 _ _ rfl (by simp [proLog, log1a, log1b, log1c, OutLRange]; omega)
          s5_v := bytesT8_log _ _ 7 _ _ rfl (by simp [proLog, log1a, log1b, log1c, OutLRange]; omega)
          s6_v := bytesT8_log _ _ 8 _ _ rfl (by simp [proLog, log1a, log1b, log1c, OutLRange]; omega)
          s7_v := bytesT8_log _ _ 9 _ _ rfl (by simp [proLog, log1a, log1b, log1c, OutLRange]; omega)
          s9_v := bytesT8_log _ _ 10 _ _ rfl (by simp [proLog, log1a, log1b, log1c, OutLRange]; omega)
          s10_v := bytesT8_log _ _ 11 _ _ rfl (by simp [proLog, log1a, log1b, log1c, OutLRange]; omega)
          s11_v := bytesT8_log _ _ 12 _ _ rfl (by simp [proLog, log1a, log1b, log1c, OutLRange]; omega) }

theorem pcv4 (h : SEnt m sp pa adp pb bdp a b ra) :
    bytesT8 (writeLog m (proLog ra s0 v sp pb)) (sp - 2192) = BitVec.ofNat 64 pb :=
  bytesT8_log _ _ 13 _ _ rfl (by simp [proLog, log1a, log1b, log1c, OutLRange])

/-- The squaring columns fit with the carry in 64 bits (`MP_MAXFAST`). -/
theorem colS_bnd {a : MpInt} (ha : a.Shape) (hm : a.used ≤ 256) (k : Nat) :
    combaW (colS a.digit a.used) k + colS a.digit a.used k < 2 ^ 64 := by
  have hcl : ∀ k, colS a.digit a.used k + 2 ^ 36 ≤ 2 ^ 64 := fun k => by
    by_cases h0 : a.used = 0
    · have : colS a.digit a.used k = 0 := by
        unfold colS combaIyS combaIy; rw [h0]
        simp only [Nat.zero_sub, Nat.min_eq_left (Nat.zero_le _), combaPart, sumTo]
        rw [ha.high_zero _ (by omega)]; simp
      omega
    by_cases hk : k < 2 * a.used
    · rw [colS_eq _ _ _ (by omega) hk, ← colC_eq _ _ _ _ k (by omega)]
      exact colC_room ha.digit_lt ha.digit_lt _ _ k (by omega) (by omega)
    · have : colS a.digit a.used k = 0 := by
        have hiy : combaIyS a.used k = 0 := by unfold combaIyS combaIy combaTx combaTy; omega
        unfold colS; rw [hiy]
        simp only [combaPart, sumTo, Nat.mul_zero, Nat.zero_add]
        split
        · rw [ha.high_zero _ (by omega)]
        · rfl
      omega
  have := combaW_lt hcl k
  have := hcl k
  omega

theorem sqrPost {b b' : MpInt} {g : Nat → Nat} {q : Nat} (hq : q = a.used + a.used)
    (hg : g = mulFastDigit a a (min (a.used + a.used) (a.used + a.used))) (h : FastOut b b' g q) :
    SqrFastPost a b b' := by
  subst hq hg
  exact { alloc := h.alloc, len := h.len, digit := h.digit, used := by rw [h.used, Nat.min_self]
          sign := h.sign }

/-- **`s_mp_sqr_fast` from the entry**, for any placement meeting `SEnt`. -/
theorem whole (h : SEnt m sp pa adp pb bdp a b ra) :
    Triple (At 0x80007010#64 (entL ra s0 v sp pa pb) m (kF v) outp) (RetE m v outp sp pb bdp a b ra s0) := by
  have hk := h.ks; have := h.sp_ge; have hw := h.warr; have hua := h.sa.used_le; have hal := h.sb.alloc_lt
  have hroom := h.room
  have e2 : writeLog (writeLog m (log1a s0 v sp)) (log1b ra v sp) = writeLog m (log1a s0 v sp ++ log1b ra v sp) :=
    (writeLog_append _ _ _).symm
  have e3 : writeLog (writeLog m (log1a s0 v sp ++ log1b ra v sp)) (log1c v sp) =
      writeLog m (log1a s0 v sp ++ log1b ra v sp ++ log1c v sp) := (writeLog_append _ _ _).symm
  have e4 : writeLog (writeLog m (log1a s0 v sp ++ log1b ra v sp ++ log1c v sp)) [(sp - 2192, 8, BitVec.ofNat 64 pb)] =
      writeLog m (proLog ra s0 v sp pb) := by rw [← writeLog_append]; rfl
  have k1 : InK sp (log1a s0 v sp) := by simp only [log1a, InK, and_true]; omega
  have k2 : InK sp (log1a s0 v sp ++ log1b ra v sp) := by
    simp only [log1a, log1b, List.cons_append, List.nil_append, InK, and_true]; omega
  have k3 : InK sp (log1a s0 v sp ++ log1b ra v sp ++ log1c v sp) := by
    simp only [log1a, log1b, log1c, List.cons_append, List.nil_append, InK, and_true]; omega
  have k4 := inK_pro (ra := ra) (s0 := s0) (v := v) (pb := pb) this
  have imgK : ∀ {l : List WEntry}, InK sp l → Img (writeLog m l) := fun hl =>
    Img.of_text h.img fun x h1 h2 => h.offK hl x (by have := h.k_t; simp only [textBase, textLen] at *; omega)
  have hp1 : P1Facts m pa pb a.used b.alloc :=
    { ra_ := by simpa [Layout.sizeofMpInt] using h.ga.st, rb := by simpa [Layout.sizeofMpInt] using h.gb.st
      ua_v := by simpa [Layout.offUsed] using h.ra_.used, al_v := by simpa [Layout.offAlloc] using h.rb.alloc
      ua_lt := by omega, al_lt := hal }
  have hpro : Triple (At 0x80007010#64 (entL ra s0 v sp pa pb) m (kF v) outp)
      (At 0x80007064#64 (q2L v sp pa a.used) (writeLog (writeLog m (proLog ra s0 v sp pb)) []) (kF v) outp) := by
    refine Triple.seq (p1a_step ra s0 v outp sp pa pb a.used b.alloc m h.img.sMpSqrFast hk hp1) ?_
    refine Triple.seq (p1b_step ra s0 v outp sp pa pb a.used b.alloc _ (imgK k1).sMpSqrFast hk) ?_
    rw [e2]
    refine Triple.seq (p1c_step ra s0 v outp sp pa pb a.used b.alloc _ (imgK k2).sMpSqrFast hk) ?_
    rw [e3]
    have h1 := p1d_step ra s0 v outp sp pa pb a.used b.alloc _ (imgK k3).sMpSqrFast hk (by omega)
    rw [e4] at h1
    exact Triple.seq h1 (p1e_step v outp sp pa a.used b.alloc _ (imgK k4).sMpSqrFast (by omega) hal hroom)
  -- facts on the snapshot `M4`, then on `M5` (after the spills)
  have hoff4 := h.offK k4
  have ha4 : MpAt (writeLog m (proLog ra s0 v sp pb)) pa adp a :=
    h.ra_.of_agree (fun y h3 h4 => hoff4 y (by have := h.k_as; omega)) (fun y h3 h4 => hoff4 y (by have := h.k_ad; omega))
  have hb4 : MpAt (writeLog m (proLog ra s0 v sp pb)) pb bdp b :=
    h.rb.of_agree (fun y h3 h4 => hoff4 y (by have := h.k_bs; omega)) (fun y h3 h4 => hoff4 y (by have := h.k_bd; omega))
  have hc4 := (imgK k4).sMpSqrFast
  have ht : ∀ {M : Mem} (q : Nat), q ≤ 2 * a.used → (∀ x, (x < sp - 2208 ∨ sp ≤ x) → M[x]? = m[x]?) →
      HFacts M ra s0 v sp → bytesT8 M (sp - 2192) = BitVec.ofNat 64 pb → TailF M ra s0 v sp pb bdp b q :=
    fun q hq hM hf hpc =>
      { k := hk, hf := hf, pc_v := hpc
        rc0 := h.rb.of_agree (fun y h3 h4 => hM y (by have := h.k_bs; omega))
          (fun y h3 h4 => hM y (by have := h.k_bd; omega))
        gc := h.gb, sc := h.sb, room := by omega, pa_w := by omega
        img := Img.of_text h.img fun x h1 h2 => hM x (by have := h.k_t; simp only [textBase, textLen] at *; omega)
        k_c := h.k_bs, k_d := h.k_bd, k_t := h.k_t, t_c := h.t_bs, t_d := h.t_bd }
  have ht4 := ht 0 (Nat.zero_le _) hoff4 (hfacts4 h) (pcv4 h)
  -- the spills
  have hl2a : InK sp (log2a sp a.used) := by simp only [log2a, InK, and_true]; omega
  have hlx : InK sp [(sp - 2176, 8, BitVec.ofNat 64 (4 * (a.used - 1)))] := by simp only [InK, and_true]; omega
  have hl2c : InK sp (log2c sp a.used) := by simp only [log2c, InK, and_true]; omega
  have hm5 : ∀ x, (x < sp - 2208 ∨ sp ≤ x) → (writeLog (writeLog (writeLog (writeLog m (proLog ra s0 v sp pb))
      (log2a sp a.used)) [(sp - 2176, 8, BitVec.ofNat 64 (4 * (a.used - 1)))]) (log2c sp a.used))[x]? = m[x]? :=
    fun x hx => (writeLog_out _ _ _ (inK_out hx hl2c)).trans ((writeLog_out _ _ _ (inK_out hx hlx)).trans
      ((writeLog_out _ _ _ (inK_out hx hl2a)).trans (hoff4 x hx)))
  have hhi : ∀ x, sp - 104 ≤ x → x < sp → (writeLog (writeLog (writeLog (writeLog m (proLog ra s0 v sp pb))
      (log2a sp a.used)) [(sp - 2176, 8, BitVec.ofNat 64 (4 * (a.used - 1)))]) (log2c sp a.used))[x]? =
      (writeLog m (proLog ra s0 v sp pb))[x]? := fun x h1 h2 =>
    (writeLog_out _ _ _ (by simp [log2c, OutL]; omega)).trans ((writeLog_out _ _ _ (by simp [OutL]; omega)).trans
      (writeLog_out _ _ _ (by simp [log2a, OutL]; omega)))
  have hpc5 : bytesT8 (writeLog (writeLog (writeLog (writeLog m (proLog ra s0 v sp pb))
      (log2a sp a.used)) [(sp - 2176, 8, BitVec.ofNat 64 (4 * (a.used - 1)))]) (log2c sp a.used)) (sp - 2192) =
      BitVec.ofNat 64 pb := by
    rw [bytesT8_congr fun x h1 h2 => (writeLog_out _ _ _ (by simp [log2c, OutL]; omega)).trans
      ((writeLog_out _ _ _ (by simp [OutL]; omega)).trans (writeLog_out _ _ _ (by simp [log2a, OutL]; omega)))]
    exact pcv4 h
  have ht5 := ht (2 * a.used) (Nat.le_refl _) hm5 ((hfacts4 h).mono hhi) hpc5
  have hpa5 : bytesT8 (writeLog (writeLog (writeLog (writeLog m (proLog ra s0 v sp pb))
      (log2a sp a.used)) [(sp - 2176, 8, BitVec.ofNat 64 (4 * (a.used - 1)))]) (log2c sp a.used)) (sp - 2168) =
      BitVec.ofNat 64 (2 * a.used) := bytesT8_log _ _ 1 _ _ rfl (by simp [log2c, OutLRange])
  have hadp : bytesT8 (writeLog (writeLog m (proLog ra s0 v sp pb)) (log2a sp a.used)) (pa + 16) =
      BitVec.ofNat 64 adp := by
    rw [bytesT8_congr fun x h1 h2 => writeLog_out _ _ _ (by have := h.k_as; simp [log2a, OutL]; omega)]
    simpa [Layout.offDp] using ha4.dpv
  have hs24 : bytesT8 (writeLog (writeLog (writeLog m (proLog ra s0 v sp pb)) (log2a sp a.used))
      [(sp - 2176, 8, BitVec.ofNat 64 (4 * (a.used - 1)))]) (sp - 2184) = BitVec.ofNat 64 a.used := by
    rw [bytesT8_congr fun x h1 h2 => writeLog_out _ _ _ (by simp [OutL]; omega)]
    exact bytesT8_log _ _ 0 _ _ rfl (by simp [log2a, OutLRange]; omega)
  have hsc : ∀ M f, ArrFrm (ρW sp) () (writeLog (writeLog (writeLog (writeLog m (proLog ra s0 v sp pb))
      (log2a sp a.used)) [(sp - 2176, 8, BitVec.ofNat 64 (4 * (a.used - 1)))]) (log2c sp a.used)) M (sp - 2160) 512 f →
      0 < a.used → SColH M sp a.used adp a.digit := by
    intro M f hA hpos
    have hW : ∀ x, (x < sp - 2160 ∨ sp - 112 ≤ x) → M[x]? = (writeLog (writeLog (writeLog (writeLog m
        (proLog ra s0 v sp pb)) (log2a sp a.used)) [(sp - 2176, 8, BitVec.ofNat 64 (4 * (a.used - 1)))])
        (log2c sp a.used))[x]? := fun x hx => hA.outW (by omega) hx
    clear hA
    have hra : Ram adp (4 * a.alloc) := by simpa [Layout.sizeofDigit] using h.ga.ds
    have hoff : ∀ x, (x < sp - 2208 ∨ sp ≤ x) → M[x]? = m[x]? := fun x hx =>
      (hW x (Or.elim hx (fun h' => Or.inl (Nat.lt_of_lt_of_le h' (Nat.sub_le_sub_left (by decide) sp)))
        (fun h' => Or.inr (Nat.le_trans (Nat.sub_le sp 112) h')))).trans (hm5 x hx)
    have r8 : ∀ k, sp - 2208 ≤ k → k + 8 ≤ sp - 2160 → bytesT8 M k = bytesT8 (writeLog (writeLog (writeLog
        (writeLog m (proLog ra s0 v sp pb)) (log2a sp a.used)) [(sp - 2176, 8, BitVec.ofNat 64 (4 * (a.used - 1)))])
        (log2c sp a.used)) k := fun k h1 h2 => bytesT8_congr fun x h3 h4 => hW x (Or.inl (by omega))
    exact
      { k := hk
        img := Img.of_text h.img fun x h1 h2 => hoff x (by have := h.k_t; simp only [textBase, textLen] at *; omega)
        rdA := fun i hi =>
          { r := hra.sub (by omega) (by omega)
            v := by
              rw [bytesT4_congr fun x h1 h2 => hoff x (by have := h.k_ad; omega)]
              simpa [Layout.sizeofDigit] using h.ra_.digits i (by omega)
            lt := by have := h.sa.digit_lt i; simpa [radix, Layout.digitBits] using this }
        ua0 := by
          rw [r8 _ (by omega) (by omega)]
          exact bytesT8_log _ _ 0 _ _ rfl (by simp [log2c, OutLRange]; omega)
        ua1 := by
          rw [r8 _ (by omega) (by omega), bytesT8_congr fun x h1 h2 => (writeLog_out _ _ _ (by simp [log2c, OutL]; omega)).trans
            (writeLog_out _ _ _ (by simp [OutL]; omega))]
          exact bytesT8_log _ _ 1 _ _ rfl (by simp [log2a, OutLRange])
        ua24 := by
          rw [r8 _ (by omega) (by omega), bytesT8_congr fun x h1 h2 => writeLog_out _ _ _ (by simp [log2c, OutL]; omega)]
          exact hs24
        ua32 := by
          rw [r8 _ (by omega) (by omega), bytesT8_congr fun x h1 h2 => writeLog_out _ _ _ (by simp [log2c, OutL]; omega)]
          exact bytesT8_log _ _ 0 _ _ rfl (by simp [OutLRange])
        ua_pos := hpos, ua_lt := by omega
        ha := by have := hra.hi_le; omega
        hb4 := by have := hra.lo_ge; omega }
  refine Triple.seq hpro ?_
  generalize writeLog m (proLog ra s0 v sp pb) = M4 at *
  refine Triple.lmap (P := At 0x80007064#64 (q2L v sp pa a.used) M4 (kF v) outp) (fun _ h => h) ?_
  by_cases h0 : a.used = 0
  · have hg : mulFastDigit a a (min (a.used + a.used) (a.used + a.used)) = mulFastDigit a a 0 := by simp [h0]
    rw [h0]
    refine Triple.seq (p2z_step v outp sp pa _ hc4) ?_
    exact Triple.rmap (fun cf ⟨c', M, hat, hr, hfo, hfr⟩ => ⟨c', M, hat, hr, sqrPost (by omega) hg.symm hfo,
        fun x h1 h2 h3 => (hfr x h1 h2 h3).trans (hoff4 x h1)⟩)
      (Triple.lmap (fun _ h => h) (tailZ ht4 pa _ (fun j => by simp [mulFastDigit])))
  refine Triple.seq (p2a_step v outp sp pa a.used _ hc4 hk (by omega) (by omega)) ?_
  refine Triple.seq (p2b_step v outp sp pa a.used adp _ (Img.of_text h.img fun x h1 h2 =>
    (writeLog_out _ _ _ (inK_out (x := x) (by have := h.k_t; simp only [textBase, textLen] at *; omega) hl2a)).trans
      (hoff4 x (by have := h.k_t; simp only [textBase, textLen] at *; omega))).sMpSqrFast hk
    (by simpa [Layout.sizeofMpInt] using h.ga.st) hadp) ?_
  refine Triple.seq (p2c_step v outp sp pa a.used adp _ (Img.of_text h.img fun x h1 h2 =>
    ((writeLog_out _ _ _ (inK_out (x := x) (by have := h.k_t; simp only [textBase, textLen] at *; omega) hlx)).trans
    ((writeLog_out _ _ _ (inK_out (x := x) (by have := h.k_t; simp only [textBase, textLen] at *; omega) hl2a)).trans
      (hoff4 x (by have := h.k_t; simp only [textBase, textLen] at *; omega))))).sMpSqrFast hk (by omega) (by omega)
    hs24) ?_
  generalize writeLog (writeLog (writeLog M4 (log2a sp a.used)) [(sp - 2176, 8, BitVec.ofNat 64 (4 * (a.used - 1)))])
    (log2c sp a.used) = M5 at *
  have hL : SLoopH M5 sp a.used adp a.digit :=
    { ch := fun M f hA => hsc M f hA (by omega), bnd := colS_bnd h.sa (by omega), pa_w := by omega
      dlt := h.sa.digit_lt }
  have hAi : ArrFrm (ρW sp) () M5 M5 (sp - 2160) 512
      (ovl (combaD (colS a.digit a.used)) (fun j => (bytesT4 M5 (sp - 2160 + 4 * j)).toNat) 0) :=
    ArrFrm.init (Iv.sub_self _) (by rw [ovl_zero]; intro j _; simp)
  have e0 : combaW (colS a.digit a.used) 0 + 2 * hp a.digit a.used 0 = 0 := by
    simp [combaW, hp, combaIyS, combaIy, combaTx, combaTy, MulFast.pS, sumTo]
  have hinit : Triple (At 0x800070a8#64 (qH sp a.used adp 0 0 (BitVec.ofNat 64 pa) v.s.s9 v.s.s10 v.s.s11) M5
        (kF v) outp)
      (fun cf => ∃ j0 j9 j10 j11 : BitVec 64, WSt M5 v outp sp 0x800070a8#64
        (qH sp a.used adp 0 (combaW (colS a.digit a.used) 0 + 2 * hp a.digit a.used 0) j0 j9 j10 j11)
        (ovl (combaD (colS a.digit a.used)) (fun j => (bytesT4 M5 (sp - 2160 + 4 * j)).toNat) 0) cf) := by
    rw [e0]; exact Triple.rmap (fun cf h => ⟨_, _, _, _, M5, hAi, h⟩) Triple.rfl
  refine Triple.seq (Triple.rmap (fun _ h => h) hinit) ?_
  refine Triple.seq (loop (v := v) (outp := outp) hL (by omega) 0 (by omega)) ?_
  have hg : (fun j => if j < 2 * a.used then combaD (colS a.digit a.used) j else 0) =
      mulFastDigit a a (min (a.used + a.used) (a.used + a.used)) := by
    funext j
    simp only [mulFastDigit, Nat.min_self, show 2 * a.used = a.used + a.used by omega]
    split
    · rw [sqrFast_digit a (by omega) j (by omega)]
    · rfl
  exact Triple.rmap (fun cf ⟨c', M, hat, hr, hfo, hfr⟩ => ⟨c', M, hat, hr, sqrPost (by omega) hg hfo,
      fun x h1 h2 h3 => (hfr x h1 h2 h3).trans (hm5 x h1)⟩)
    (tailM ht5 (by omega) (by omega) hpa5 adp _ _ _ (combaD_lt _))

end whole

end Tom.Machine.Fn.SqrFast
