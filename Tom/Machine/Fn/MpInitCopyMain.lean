import Tom.Machine.Api.MpInitCopy
import Tom.Machine.Fn.MpInitMain
import Tom.Machine.Fn.MpCopyMain

/-!
# `mp_init_copy` on the machine: the whole function

The segments of `Fn/MpInitCopy.lean` around `mp_init_size(a, b->used)`
(`Fn.MpInit.size_correct`, from `calloc`'s contract) and `mp_copy(b, a)`
(`Fn.MpCopy.correct`). `mp_init_size`'s layout comes by
renaming (`Sound.pull`), its frame back by `HFrm.push`; `mp_copy`'s layout is
built from ours and the fresh block (`Fresh.off_heap`, `Fresh.disj_blk`).
-/


namespace Tom.Machine.Fn.MpInitCopy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api
open Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
open Tom.Machine.Api.MpInitCopy (R)

/-- The Abi `mp_init_size` sees: our frame's `sp`, `s0 = b`, `s1 = a`. -/
def sizeAbi (v : Abi) (sp pa pb : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 48), s0 := BitVec.ofNat 64 pb, s := { v.s with s1 := BitVec.ofNat 64 pa } }

/-- The Abi `mp_copy` sees: `s1 = a`. -/
def copyAbi (v : Abi) (pa : Nat) : Abi := { v with s := { v.s with s1 := BitVec.ofNat 64 pa } }

/-- The `mp_init_size` call at `1368`, back at `136c`. -/
theorem size_call (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa pb u : Nat) (M : Mem)
    (hc : CodeAt M mpInitCopyBase mpInitCopyCode) :
    Triple (At 0x80001368#64 (callL ra sp pa pb u) M v.keepR1 outp)
      (At Fn.MpInit.sizeEntry (Api.MpInit.sizeL 0x8000136c#64 pa (BitVec.ofNat 64 u)) M
        (sizeAbi v sp pa pb).keep outp) := by
  refine Triple.rmap (fun c h => ?_)
    (jal_at (pc := 0x80001368#64) (w := 0x130000ef#32) (imm := 0x130#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa),
        (10, BitVec.ofNat 64 pa), (11, BitVec.ofNat 64 u)])
      (hc.word (a := (0x80001368#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [callL]) (by simp [keysG]) (by simp [Abi.keepR1, keysG]))
  have hpc : (0x80001368#64 : BitVec 64) + sign_extend (m := 64) (0x130#21) = Fn.MpInit.sizeEntry := by decide
  have hra : Sail.BitVec.addInt (0x80001368#64 : BitVec 64) 4 = 0x8000136c#64 := by decide
  rw [hpc, hra] at h
  exact At.reshape h (by simp [Api.MpInit.sizeL]) (by simp [sizeAbi, Abi.keep, Abi.keepR1, sKeepL])

/-- The `mp_copy(b, a)` call at `1394`, back at `1398`. -/
theorem copy_call (v : Abi) (outp : Array String) (sp pa pb : Nat) (M : Mem)
    (hc : CodeAt M mpInitCopyBase mpInitCopyCode) :
    Triple (At 0x80001394#64 (copyL sp pa pb) M v.keepR1 outp)
      (At MpCopy.entry (Fn.MpCopy.entryL 0x80001398#64 (BitVec.ofNat 64 pb) (sp - 48) pb pa) M
        (copyAbi v pa).keepR outp) := by
  refine Triple.rmap (fun c h => ?_)
    (jal_at (pc := 0x80001394#64) (w := 0xc4cff0ef#32) (imm := 0x1ff44c#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 pb), (9, BitVec.ofNat 64 pa),
        (10, BitVec.ofNat 64 pb), (11, BitVec.ofNat 64 pa)])
      (hc.word (a := (0x80001394#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [copyL]) (by simp [keysG]) (by simp [Abi.keepR1, keysG]))
  have hpc : (0x80001394#64 : BitVec 64) + sign_extend (m := 64) (0x1ff44c#21) = MpCopy.entry := by decide
  have hra : Sail.BitVec.addInt (0x80001394#64 : BitVec 64) 4 = 0x80001398#64 := by decide
  rw [hpc, hra] at h
  exact At.reshape h (by simp [Fn.MpCopy.entryL]) (by simp [copyAbi, Abi.keepR, Abi.keepR1, sKeepL])

/-- `mp_init_size`'s regions inside ours. -/
def sizeMap : Api.MpInit.R → R
  | .stk => .stk | .aS => .aS | .code => .code

section
variable {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp pa pb bdp : Nat} {b : MpInt}
  {ra : BitVec 64}

local notation "ρ" => MpInitCopy.lay MpInitCopy.F sp pa pb bdp b

theorem sfacts (hP : MpInitCopy.Pre m v H sp pa pb bdp b ra) : SFacts sp :=
  have := hP.ctx.sp_lo; have := hP.ctx.sp_hi; have := hP.ctx.sp_al
  have eE : heapEnd = 0x87800000 := rfl
  have eD : callocDepth = 544 := rfl
  { rs := ⟨by omega, by omega, .inr (by unfold tohostAddr; omega)⟩, sp_al := this, sp_ge := by omega
    code_off := by unfold mpInitCopyBase; omega }

theorem size_sub (hs : MpInitCopy.F ≤ sp) :
    ∀ k, (Api.MpInit.lay Api.MpInit.Fsize (sp - 48) pa k).Sub (ρ (sizeMap k)) := by
  have e1 : MpInitCopy.F = 624 := rfl
  have e2 : Api.MpInit.Fsize = 576 := rfl
  intro k; cases k <;> simp only [Iv.Sub, Api.MpInit.lay, MpInitCopy.lay, sizeMap, e1, e2] <;> omega

/-- After `mp_init_size` returns `r` in `M2`. -/
theorem tail (hP : MpInitCopy.Pre m v H sp pa pb bdp b ra) {M1 : Mem}
    (hF1 : Frm ρ [R.stk] m M1) (h16 : bytesT8 M1 (sp - 16) = v.s0) (h24 : bytesT8 M1 (sp - 24) = v.s.s1)
    (h8 : bytesT8 M1 (sp - 8) = ra) (hbl : MpAt M1 pb bdp b) (hheap1 : Heap M1 H) (himg1 : Img M1)
    (r : BitVec 64) (M2 : Mem)
    (hpost : Api.MpInit.Post M1 M2 H (sp - 48) pa MpInit.Fsize (initPrec b.used) r) :
    Triple (At 0x8000136c#64 [(1, 0x8000136c#64), (10, r)] M2 (sizeAbi v sp pa pb).keep outp)
      (MpInitCopy.Ret m v outp H sp pa pb bdp b ra) := by
  have hs := sfacts hP
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
  have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  have eD : callocDepth = 544 := rfl
  have eF : MpInitCopy.F = 624 := rfl
  have eFs : Api.MpInit.Fsize = 576 := rfl
  have hsv := hP.ctx.sp_v
  have hsd := hP.lay.disj (r := R.aS) (s := R.stk)
  simp only [Iv.Disj, Disj, MpInitCopy.lay, eF] at hsd
  have hsoff := hP.soff
  unfold OffHeap at hsoff
  have eL : allocLo = 0x800188a0 := rfl
  have hn : initPrec b.used < 2 ^ 31 := by
    have := hP.vb.used_le; have := hP.vb.alloc_lt; simp only [initPrec, minPrec_eq]; omega
  have hF1' := HFrm.of_frm (H := H) (hF1.mono (ws' := MpInitCopy.ws))
  -- our frame slots across `mp_init_size`
  have kslot2 : ∀ x, sp - 24 ≤ x → x < sp → ¬ ((InAny (Api.MpInit.lay Api.MpInit.Fsize (sp - 48) pa) Api.MpInit.ws x) ∨
      Foot H x) := fun x h1 h2 hx => hx.elim
    (fun h => by simp only [InAny, Api.MpInit.ws, Iv.In, MpInit.lay, eFs, or_false] at h; omega)
    (fun h => OffHeap.off_foot (a := x) (n := 1) (.inr (by omega)) (Nat.le_refl _) (by omega) h)
  have r2 : ∀ (M3 : Mem) (W : Nat → Prop), Keep W M2 M3 → (∀ x, sp - 24 ≤ x → x < sp → ¬ W x) →
      HFrm (Api.MpInit.lay Api.MpInit.Fsize (sp - 48) pa) Api.MpInit.ws H M1 M2 →
      bytesT8 M3 (sp - 48 + 40) = ra ∧ bytesT8 M3 (sp - 48 + 32) = v.s0 ∧ bytesT8 M3 (sp - 48 + 24) = v.s.s1 :=
    fun M3 W hk hw hf =>
      have hk2 : Keep (fun x => W x ∨ (InAny (Api.MpInit.lay Api.MpInit.Fsize (sp - 48) pa) Api.MpInit.ws x ∨ Foot H x)) M1 M3 :=
        Keep.mono (Keep.trans hf hk) fun x hx => hx.elim (fun h => .inr h) (fun h => .inl h)
      ⟨by rw [hk2.bytesT8 fun x h1 h2 hx => hx.elim (hw x (by omega) (by omega)) (kslot2 x (by omega) (by omega)),
          show sp - 48 + 40 = sp - 8 by omega]; exact h8,
       by rw [hk2.bytesT8 fun x h1 h2 hx => hx.elim (hw x (by omega) (by omega)) (kslot2 x (by omega) (by omega)),
          show sp - 48 + 32 = sp - 16 by omega]; exact h16,
       by rw [hk2.bytesT8 fun x h1 h2 hx => hx.elim (hw x (by omega) (by omega)) (kslot2 x (by omega) (by omega)),
          show sp - 48 + 24 = sp - 24 by omega]; exact h24⟩
  have himg2 : ∀ (M2' : Mem), HFrm (Api.MpInit.lay Api.MpInit.Fsize (sp - 48) pa) Api.MpInit.ws H M1 M2' → Img M1 → Img M2' :=
    fun M2' hf hi => (hf.push sizeMap (size_sub (by omega))).keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _))
      (OffFoot.cons (OffFoot.of_offHeap text_off_heap) (OffFoot.nil _)) hi
  have hpush : ∀ {M2' : Mem}, HFrm (Api.MpInit.lay Api.MpInit.Fsize (sp - 48) pa) Api.MpInit.ws H M1 M2' →
      HFrm ρ MpInitCopy.ws H M1 M2' := fun hf => (hf.push sizeMap (size_sub (by omega))).mono
  cases hpost with
  | mem heap2 dp2 frame2 =>
    obtain ⟨r40, r32, r24⟩ := r2 M2 (fun _ => False) (fun _ _ => rfl) (fun _ _ _ h => h) frame2
    exact Triple.lmap (fun c h => At.reshape (L' := backL sp pa pb Api.MpInit.memBV) (K' := v.keepR1) h
        (by simp [backL, sizeAbi, Abi.keep, sKeepL]) (by simp [sizeAbi, Abi.keep, Abi.keepR1, sKeepL]))
      (Triple.rmap (fun c hA => ⟨Api.MpInit.memBV, M2, hA.reshape (by simp [retL])
          (by simp [retL, Abi.keep, Abi.keepR1, sKeepL, hsv]), .mem heap2 dp2 (hF1'.trans (hpush frame2))⟩)
        (err_step ra v.s0 v.s.s1 v outp sp pa pb _ M2 (himg2 M2 frame2 himg1).mpInitCopy hP.ra_al hs (by decide)
          r40 r32 r24))
  | @ok q fresh2 heap2 live2 frame2 =>
    have hfr := fresh2
    have hqlo := hfr.lo; have hqhi := hfr.hi; have hqal := hfr.al
    have hF2 := hpush frame2
    have hbl2 : MpAt M2 pb bdp b := hF2.keep hP.lay
      (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _))
      (OffFoot.cons (OffFoot.of_offHeap hP.live.soff) (OffFoot.cons (OffFoot.of_blk hheap1 hP.live.blk)
        (OffFoot.nil _))) hbl
    have himg2' := himg2 M2 frame2 himg1
    -- the layout `mp_copy(b, a)` needs
    have hl := hP.lay
    have d1 : Disj (sp - 48 - 32) 32 pb 24 := by
      have := hl.disj (r := R.stk) (s := R.bS); simp only [Iv.Disj, Disj, MpInitCopy.lay, eF] at this ⊢; omega
    have d2 : Disj (sp - 48 - 32) 32 bdp (4 * b.alloc) := by
      have := hl.disj (r := R.stk) (s := R.bD); simp only [Iv.Disj, Disj, MpInitCopy.lay, eF] at this ⊢; omega
    have d3 : Disj (sp - 48 - 32) 32 pa 24 := by simp only [Disj]; omega
    have d4 : Disj (sp - 48 - 32) 32 q (4 * (MpInt.zeroN (initPrec b.used)).alloc) := by
      simp only [Disj, MpInt.zeroN]; omega
    have d5 : Disj (sp - 48 - 32) 32 textBase textLen := by
      have := hl.disj (r := R.stk) (s := R.code); simp only [Iv.Disj, Disj, MpInitCopy.lay, eF, textIv] at this ⊢; omega
    have d6 : Disj pa 24 pb 24 := hl.disj (r := R.aS) (s := R.bS)
    have d7 : Disj pa 24 bdp (4 * b.alloc) := hl.disj (r := R.aS) (s := R.bD)
    have d8 : Disj q (4 * (MpInt.zeroN (initPrec b.used)).alloc) pa 24 := hfr.off_heap hP.soff
    have d9 : Disj pa 24 textBase textLen := hl.disj (r := R.aS) (s := R.code)
    have d10 : Disj q (4 * (MpInt.zeroN (initPrec b.used)).alloc) pb 24 := hfr.off_heap hP.live.soff
    have d11 : Disj q (4 * (MpInt.zeroN (initPrec b.used)).alloc) bdp (4 * b.alloc) :=
      hfr.disj_blk hP.live.blk (by simp only [initPrec, minPrec_eq]; omega) (by simp only; have := hP.apos; omega)
    have d12 : Disj q (4 * (MpInt.zeroN (initPrec b.used)).alloc) textBase textLen :=
      hfr.off_heap text_off_heap
    have hlay : Sound (MpCopy.lay (sp - 48) pb bdp pa q b (MpInt.zeroN (initPrec b.used))) Two.isW := by
      intro r s h
      cases r <;> cases s <;> first
        | exact absurd h (by decide)
        | (show Disj _ _ _ _
           first
           | exact d1 | exact Disj.symm d1 | exact d2 | exact Disj.symm d2 | exact d3 | exact Disj.symm d3
           | exact d4 | exact Disj.symm d4 | exact d5 | exact Disj.symm d5 | exact d6 | exact Disj.symm d6
           | exact d7 | exact Disj.symm d7 | exact d8 | exact Disj.symm d8 | exact d9 | exact Disj.symm d9
           | exact d10 | exact Disj.symm d10 | exact d11 | exact Disj.symm d11 | exact d12
           | exact Disj.symm d12)
    have hpre : MpCopy.Pre M2 (sp - 48) pb bdp pa q b (MpInt.zeroN (initPrec b.used)) 0x80001398#64 :=
      { ra_ := hbl2, rb := live2.repr, sa := hP.vb.toShape, sb := (MpInt.zeroN_valid hn).toShape
        asign := hP.vb.sign_ok, ga := hP.gb
        gb := { st := hP.st, st_al := hP.st_al
                ds := ⟨by omega, by simp only [Layout.sizeofDigit, MpInt.zeroN]; omega,
                  .inr (by unfold tohostAddr; omega)⟩
                ds_al := by omega
                disj := by simp only [Layout.sizeofMpInt, Layout.sizeofDigit, MpInt.zeroN, Disj] at d8 ⊢; omega }
        room := by simp only [MpInt.zeroN, initPrec]; omega
        rs := ⟨by omega, by omega, .inr (by unfold tohostAddr; omega)⟩
        sp_al := by have := hP.ctx.sp_al; omega, sp_ge := by omega, ra_al := by decide, img := himg2', lay := hlay }
    refine Triple.lmap (fun c h => At.reshape (L' := backL sp pa pb 0#64) (K' := v.keepR1) h
        (by simp [backL, sizeAbi, Abi.keep, sKeepL]) (by simp [sizeAbi, Abi.keep, Abi.keepR1, sKeepL]))
      (Triple.seq (ok_step v outp sp pa pb M2 himg2'.mpInitCopy)
        (Triple.seq (copy_call v outp sp pa pb _ himg2'.mpInitCopy)
          (Triple.seq (Fn.MpCopy.correct (v := copyAbi v pa) (s0 := BitVec.ofNat 64 pb) hpre) ?_)))
    intro c ⟨a', M3, hA3, hpost3⟩
    have hk3 : Keep (fun x => InAny (MpCopy.lay (sp - 48) pb bdp pa q b (MpInt.zeroN (initPrec b.used))) Two.ws x)
      M2 M3 := hpost3.frame
    have hw3 : ∀ x, InAny (MpCopy.lay (sp - 48) pb bdp pa q b (MpInt.zeroN (initPrec b.used))) Two.ws x →
        (sp - 48 - 32 ≤ x ∧ x < sp - 48) ∨ (pa ≤ x ∧ x < pa + 24) ∨
          (q ≤ x ∧ x < q + 4 * (MpInt.zeroN (initPrec b.used)).alloc) := by
      intro x hx
      simp only [InAny, Two.ws, Iv.In, Two.lay, or_false] at hx
      rcases hx with h | h | h
      · exact .inl ⟨h.1, by omega⟩
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    obtain ⟨r40, r32, r24⟩ := r2 M3 _ hk3 (fun x h1 h2 hx => by
      rcases hw3 x hx with h | h | h <;> (try simp only [MpInt.zeroN] at h) <;> omega) frame2
    have himg3 : Img M3 := Frm.keep hlay (Img.reads (r := Two.R.code) (Iv.sub_self _)) hpost3.frame himg2'
    have hal' : (MpInt.zeroN (initPrec b.used)).alloc = initPrec b.used := rfl
    refine Triple.rmap (fun c hA => ⟨0#64, M3, hA.reshape (by simp [retL])
        (by simp [retL, Abi.keep, Abi.keepR1, sKeepL, hsv]), ?_⟩)
      (Triple.lmap (fun c h => At.reshape (L' := backL sp pa pb 0#64) (K' := v.keepR1) h
          (by simp [backL, copyAbi, Abi.keepR, sKeepL]) (by simp [copyAbi, Abi.keepR, Abi.keepR1, sKeepL]))
        (cok_step ra v.s0 v.s.s1 v outp sp pa pb M3 himg3.mpInitCopy hP.ra_al hs r40 r32 r24))
      c hA3
    -- the post
    refine .ok fresh2 (heap2.frame fun x hx => hk3 x fun hin => ?_)
      ⟨hpost3.repr, by
        show (q, 4 * a'.alloc) ∈ _
        rw [hpost3.copy.alloc, hal']; exact List.mem_cons_self .., hP.soff⟩
      hpost3.copy ((hF1'.trans hF2).trans (HFrm.ofKeep hk3 fun x hx => ?_))
    · rcases hw3 x hin with h | h | h
      · exact OffHeap.off_foot (a := x) (n := 1) (.inr (by omega)) (Nat.le_refl _) (by omega) hx
      · exact hP.soff.off_foot h.1 h.2 hx
      · rcases hx with hg | ⟨_, _, h3⟩
        · have := Global.lt hg; omega
        · exact h3 _ (List.mem_cons_self ..) ⟨h.1, by rw [hal'] at h; exact h.2⟩
    · rcases hw3 x hx with h | h | h
      · exact .inl (Or.inl (by simp only [Iv.In, MpInitCopy.lay, eF]; omega))
      · exact .inl (Or.inr (Or.inl h))
      · exact .inr (hfr.foot ⟨h.1, by rw [hal'] at h; exact h.2⟩)

end

/-- **`mp_init_copy` on the machine**. -/
theorem correct : Api.MpInitCopy.Statement := by
  intro m v outp H sp pa pb bdp b ra hP
  have hs := sfacts hP
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi; have hsal := hP.ctx.sp_al
  have eE : heapEnd = 0x87800000 := rfl
  have eD : callocDepth = 544 := rfl
  have eF : MpInitCopy.F = 624 := rfl
  have hsv := hP.ctx.sp_v
  have hl := hP.lay
  have hd : pb + 24 ≤ sp - 48 ∨ sp ≤ pb := by
    have := hl.disj (r := R.stk) (s := R.bS); simp only [Iv.Disj, Disj, MpInitCopy.lay, eF] at this; omega
  have hpb : Ram pb 24 := by simpa [Layout.sizeofMpInt] using hP.gb.st
  have hu31 : b.used < 2 ^ 31 := by have := hP.vb.used_le; have := hP.vb.alloc_lt; omega
  have hu : BitVec.signExtend 64 (bytesT4 m pb) = BitVec.ofNat 64 b.used := by
    have := hP.live.repr.used; simp only [Layout.offUsed, Nat.add_zero] at this
    rw [this, signExtend_ofNat32 _ hu31]
  have hF1 : Frm (MpInitCopy.lay MpInitCopy.F sp pa pb bdp b) [R.stk] m (writeLog m (frameLog ra v.s0 v.s.s1 sp)) :=
    Frm.store (by simp only [LogIn, frameLog, Iv.Sub, MpInitCopy.lay, eF, and_true]; omega)
  have himg1 : Img (writeLog m (frameLog ra v.s0 v.s.s1 sp)) :=
    hF1.keep hl (Img.reads (r := R.code) (Iv.sub_self _)) hP.ctx.img
  have himp1 : ImpureAt (writeLog m (frameLog ra v.s0 v.s.s1 sp)) :=
    ImpureAt.of_keep hF1 (fun x h1 h2 hx => by
      simp only [InAny, Iv.In, MpInitCopy.lay, eF, or_false] at hx; unfold impurePtr at h2; omega) hP.ctx.impure
  have hheap1 : Heap (writeLog m (frameLog ra v.s0 v.s.s1 sp)) H :=
    hP.heap.frame fun x hx => hF1 x fun hs' => by
      simp only [InAny, Iv.In, MpInitCopy.lay, or_false] at hs'
      exact hP.ctx.off.off_foot hs'.1 hs'.2 hx
  have hbl1 : MpAt (writeLog m (frameLog ra v.s0 v.s.s1 sp)) pb bdp b :=
    hF1.keep hl (MpAt.reads (rs := R.bS) (rd := R.bD) (Iv.sub_self _) (Iv.sub_self _)) hP.live.repr
  have h16 : bytesT8 (writeLog m (frameLog ra v.s0 v.s.s1 sp)) (sp - 16) = v.s0 :=
    bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog, OutLRange]; omega)
  have h24 : bytesT8 (writeLog m (frameLog ra v.s0 v.s.s1 sp)) (sp - 24) = v.s.s1 :=
    bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog, OutLRange]; omega)
  have h8 : bytesT8 (writeLog m (frameLog ra v.s0 v.s.s1 sp)) (sp - 8) = ra :=
    bytesT8_log _ _ 2 _ _ rfl (by simp [frameLog, OutLRange])
  have hpre : Api.MpInit.Pre (writeLog m (frameLog ra v.s0 v.s.s1 sp)) (sizeAbi v sp pa pb) H (sp - 48) pa
      Api.MpInit.Fsize 0x8000136c#64 :=
    { heap := hheap1, st := hP.st, st_al := hP.st_al, soff := hP.soff
      ctx := { img := himg1, impure := himp1, gp := hP.ctx.gp, sp_v := rfl, sp_al := by omega
               sp_lo := by simp only [Api.MpInit.Fsize]; omega, sp_hi := by omega }
      ra_al := by decide
      lay := hl.pull sizeMap _ Api.MpInit.all (size_sub (by omega)) }
  refine Triple.lmap (fun c h => At.reshape (L' := entryL ra v.s0 v.s.s1 sp pa pb) (K' := v.keepR1) h
      (by simp [entryL, Api.MpInitCopy.entryL, Abi.keep, sKeepL, hsv]) (by simp [Abi.keep, Abi.keepR1, sKeepL]))
    (Triple.seq (pro_step ra v.s0 v.s.s1 v outp sp pa pb b.used m hP.ctx.img.mpInitCopy hs hpb hd hu)
      (Triple.seq (size_call ra v outp sp pa pb b.used _ himg1.mpInitCopy)
        (Triple.seq (Fn.MpInit.size_correct hpre hu31)
          (fun c ⟨r, M2, hA, hpost⟩ =>
            tail hP hF1 h16 h24 h8 hbl1 hheap1 himg1 r M2 hpost c hA))))

end Tom.Machine.Fn.MpInitCopy
