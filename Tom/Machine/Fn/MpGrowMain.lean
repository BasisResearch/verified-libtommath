import Tom.Machine.Api.MpGrow
import Tom.Machine.Fn.AllocRealloc

/-!
# `mp_grow` on the machine: the whole function, all paths

The segments of `Fn/MpGrowR.lean` around `realloc(dp, 4 * size)`
(`Fn.Alloc.realloc_correct`) and `memset(dp + 4 * alloc, 0, 4 * (size -
alloc))` (`Fn.Memset.correct_zero`). The regions are `Un`'s with stack depth 544; the frame is
`HFrm`: the frame stores in `stk`; `realloc`'s writes in `stk` (its stack),
`aD` (the old block) and `Foot H`; the struct stores in `aS`; `memset`'s in the
new block, inside `Foot H`.
-/


namespace Tom.Machine.Fn.MpGrowR

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api
open Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
open Tom.Machine.Api.Un (R)

/-- The Abi `realloc` and `memset` see: our frame's `sp`. -/
def reallocAbi (v : Abi) (sp : Nat) : Abi := { v with sp := BitVec.ofNat 64 (sp - 32) }

/-- The `realloc` call at `12a4`, back at `12a8`. -/
theorem realloc_call (ra : BitVec 64) (v : Abi) (outp : Array String) (sp p dp size : Nat) (M : Mem)
    (hc : CodeAt M mpGrowBase mpGrowCode) :
    Triple (At 0x800012a4#64 (callL ra v.s0 sp p dp size) M v.keepR outp)
      (At Api.Alloc.reallocEntry (reallocL 0x800012a8#64 dp (size * 4)) M (reallocAbi v sp).keep outp) := by
  refine Triple.rmap (fun c h => ?_)
    (jal_at (pc := 0x800012a4#64) (w := 0x799060ef#32) (imm := 0x6f98#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 32)), (8, v.s0), (10, BitVec.ofNat 64 dp),
        (11, BitVec.ofNat 64 (size * 4))])
      (hc.word (a := (0x800012a4#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [callL]) (by simp [keysG]) (by simp [Abi.keepR, keysG, sKeepL]))
  have hpc : (0x800012a4#64 : BitVec 64) + sign_extend (m := 64) (0x6f98#21) = Api.Alloc.reallocEntry := by decide
  have hra : Sail.BitVec.addInt (0x800012a4#64 : BitVec 64) 4 = 0x800012a8#64 := by decide
  rw [hpc, hra] at h
  exact At.reshape h (by simp [reallocL]) (by simp [reallocAbi, Abi.keep, Abi.keepR, sKeepL])

/-- The `memset` call at `12d8`, back at `12dc`. -/
theorem memset_call (v : Abi) (outp : Array String) (sp q al size : Nat) (M : Mem)
    (hc : CodeAt M mpGrowBase mpGrowCode) :
    Triple (At 0x800012d8#64 (setL v.s0 sp q al size) M v.keepR outp)
      (At Memset.entry (Memset.entryL 0x800012dc#64 (q + al * 4) 0#64 ((size - al) * 4)) M
        (reallocAbi v sp).keep outp) := by
  refine Triple.rmap (fun c h => ?_)
    (jal_at (pc := 0x800012d8#64) (w := 0x0cc080ef#32) (imm := 0x80cc#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 32)), (8, v.s0), (10, BitVec.ofNat 64 (q + al * 4)), (11, 0#64),
        (12, BitVec.ofNat 64 ((size - al) * 4))])
      (hc.word (a := (0x800012d8#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [setL]) (by simp [keysG]) (by simp [Abi.keepR, keysG, sKeepL]))
  have hpc : (0x800012d8#64 : BitVec 64) + sign_extend (m := 64) (0x80cc#21) = Memset.entry := by decide
  have hra : Sail.BitVec.addInt (0x800012d8#64 : BitVec 64) 4 = 0x800012dc#64 := by decide
  rw [hpc, hra] at h
  exact At.reshape h (by simp [Memset.entryL]) (by simp [reallocAbi, Abi.keep, Abi.keepR, sKeepL])

section
variable {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp p dp : Nat} {a : MpInt}
  {size : Nat} {ra : BitVec 64}

local notation "ρ" => Un.lay MpGrow.F sp p dp a

theorem sfacts (hP : MpGrow.Pre m v H sp p dp a size ra) : SFacts sp :=
  have := hP.ctx.sp_lo; have := hP.ctx.sp_hi; have := hP.ctx.sp_al
  have eE : heapEnd = 0x87800000 := rfl
  have eD : depth = 512 := rfl
  { rs := ⟨by omega, by omega, .inr (by unfold tohostAddr; omega)⟩, sp_al := this, sp_ge := by omega
    code_off := by unfold mpGrowBase; omega }

theorem stfacts (hP : MpGrow.Pre m v H sp p dp a size ra) : StFacts p :=
  have h := hP.lay.disj (r := R.aS) (s := R.code)
  { rs := hP.st, al := hP.st_al
    code_off := by simp only [Iv.Disj, Disj, Un.lay, textIv] at h; exact h }

/-- `realloc`'s writes lie in our stack, the old block and the footprint. -/
theorem blkW_sub (hP : MpGrow.Pre m v H sp p dp a size ra) :
    ∀ x, blkW H dp (4 * a.alloc) (sp - 32) x → InAny ρ Un.ws x ∨ Foot H x := by
  have := hP.ctx.sp_lo
  have eD : depth = 512 := rfl
  have eF : MpGrow.F = 544 := rfl
  rintro x (hf | hb | hk)
  · exact .inr (Foot.of_cons hf)
  · exact .inl (Or.inr (Or.inr (Or.inl hb)))
  · exact .inl (Or.inl (by unfold Stk at hk; simp only [Iv.In, Un.lay, eF]; omega))

/-- The realloc path: from the `realloc` return on. -/
theorem after (hP : MpGrow.Pre m v H sp p dp a size ra) (hlt : a.alloc < size)
    {M1 : Mem} (hF1 : Frm ρ [R.stk] m M1) (hM1 : MpAt M1 p dp a)
    (h24 : bytesT8 M1 (sp - 8) = ra) (h8 : bytesT8 M1 (sp - 24) = BitVec.ofNat 64 p)
    (h0 : bytesT8 M1 (sp - 32) = BitVec.ofNat 64 size) (himg : Img M1) (q : Nat) (M2 : Mem)
    (hpost : ReallocPost M1 M2 H dp (4 * a.alloc) (size * 4) (sp - 32) q) :
    Triple (At 0x800012a8#64 [(1, 0x800012a8#64), (10, BitVec.ofNat 64 q)] M2
        (reallocAbi v sp).keep outp)
      (MpGrow.Ret m v outp H sp p dp a size ra) := by
  have hs := sfacts hP
  have hst := stfacts hP
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
  have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  have eD : depth = 512 := rfl
  have eF : MpGrow.F = 544 := rfl
  have hsv := hP.ctx.sp_v
  have h31 := hP.size_lt
  have hblk := Fn.Alloc.Heap.blk hP.heap (List.mem_cons_self ..)
  simp only at hblk
  have hb' : heapStart ≤ dp ∧ dp + 4 * a.alloc ≤ heapEnd := ⟨by omega, hblk.2⟩
  have hsd := hP.lay.disj (r := R.aS) (s := R.stk)
  simp only [Iv.Disj, Disj, Un.lay, eF] at hsd
  have hsoff := hP.soff
  unfold OffHeap at hsoff
  have eL : allocLo = 0x800188a0 := rfl
  -- what `realloc` keeps: our frame slots, the struct, the text
  have kslot : ∀ {W : Nat → Prop} {M : Mem}, (∀ x, sp - 32 ≤ x → x < sp → ¬ W x) → Keep W M1 M →
      bytesT8 M (sp - 32 + 24) = ra ∧ bytesT8 M (sp - 32 + 8) = BitVec.ofNat 64 p ∧
        bytesT8 M (sp - 32) = BitVec.ofNat 64 size := fun hw hk =>
    ⟨by rw [hk.bytesT8 fun x h1 h2 => hw x (by omega) (by omega), show sp - 32 + 24 = sp - 8 by omega]; exact h24,
     by rw [hk.bytesT8 fun x h1 h2 => hw x (by omega) (by omega), show sp - 32 + 8 = sp - 24 by omega]; exact h8,
     by rw [hk.bytesT8 fun x h1 h2 => hw x (by omega) (by omega)]; exact h0⟩
  have wslot : ∀ x, sp - 32 ≤ x → x < sp → ¬ blkW H dp (4 * a.alloc) (sp - 32) x :=
    fun x h1 h2 => blkW_off hb' (.inr (by omega)) (.inr h1)
  have wst : ∀ x, p ≤ x → x < p + 24 → ¬ blkW H dp (4 * a.alloc) (sp - 32) x :=
    fun x h1 h2 => blkW_off hb' (hP.soff.sub h1 (by omega)) (by omega)
  have wtext : ∀ x, textBase ≤ x → x < textBase + textLen → ¬ blkW H dp (4 * a.alloc) (sp - 32) x :=
    fun x h1 h2 => blkW_off hb' (OffHeap.text h1 h2) (.inl (by unfold textBase textLen at h2; omega))
  have hfr1 := HFrm.of_frm (H := H) (hF1.mono (ws' := Un.ws))
  cases hpost with
  | null hN same =>
    obtain ⟨r24, -, -⟩ := kslot wslot hN.keep
    have hrepr : MpAt M2 p dp a :=
      { used := by rw [hN.keep.bytesT4 fun x h1 h2 => wst x (by simp [Layout.offUsed] at *; omega)
                    (by simp [Layout.offUsed] at *; omega)]; exact hM1.used
        alloc := by rw [hN.keep.bytesT4 fun x h1 h2 => wst x (by simp [Layout.offAlloc] at *; omega)
                    (by simp [Layout.offAlloc] at *; omega)]; exact hM1.alloc
        sign := by rw [hN.keep.bytesT4 fun x h1 h2 => wst x (by simp [Layout.offSign] at *; omega)
                    (by simp [Layout.offSign] at *; omega)]; exact hM1.sign
        dpv := by rw [hN.keep.bytesT8 fun x h1 h2 => wst x (by simp [Layout.offDp] at *; omega)
                    (by simp [Layout.offDp] at *; omega)]; exact hM1.dpv
        digits := fun i hi => by
          rw [bytesT4_of_getD (m := M1) (b := dp + Layout.sizeofDigit * i) fun k hk => by
            rw [show dp + Layout.sizeofDigit * i + k = dp + (4 * i + k) by simp [Layout.sizeofDigit]; omega]
            exact same _ (by omega)]
          exact hM1.digits i hi }
    refine Triple.lmap (fun c h => At.reshape (L' := backL v.s0 sp 0) (K' := v.keepR) h
        (by simp [backL, reallocAbi, Abi.keep, sKeepL]) (by simp [reallocAbi, Abi.keep, Abi.keepR, sKeepL]))
      (Triple.rmap (fun c hA => ⟨_, M2, hA.reshape (by simp [retL]) (by simp [retL, Abi.keep, Abi.keepR,
          sKeepL, hsv]), .mem hlt hN.heap hrepr (hfr1.trans (HFrm.ofKeep hN.keep (blkW_sub hP)))⟩)
        (null_step ra v.s0 v outp sp M2 (hN.keep.img wtext himg).mpGrow hP.ra_al hs r24))
  | ok hG copy =>
    have hfr := hG.fresh
    have hqlo := hfr.lo; have hqhi := hfr.hi
    obtain ⟨r24, r8, r0⟩ := kslot wslot hG.keep
    have himg2 := hG.keep.img wtext himg
    have hz : (BitVec.ofNat 64 q == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hfr.nz (by simpa using h')
    have hal2 : bytesT4 M2 (p + 4) = BitVec.ofNat 32 a.alloc := by
      rw [hG.keep.bytesT4 fun x h1 h2 => wst x (by omega) (by omega)]
      simpa [Layout.offAlloc] using hM1.alloc
    have hF3 : Frm ρ [R.aS] (writeLog M2 []) (writeLog (writeLog M2 []) (stLog p q size)) :=
      Frm.store (by simp only [LogIn, stLog, Iv.Sub, Un.lay, and_true]; omega)
    have himg3 := hF3.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) himg2
    generalize hM3 : writeLog (writeLog M2 []) (stLog p q size) = M3 at hF3 himg3
    have hram : Ram (q + a.alloc * 4) ((size - a.alloc) * 4) :=
      ⟨by omega, by omega, .inr (by unfold tohostAddr; omega)⟩
    have hpre : Memset.Pre M3 (q + a.alloc * 4) 0 ((size - a.alloc) * 4) :=
      { byte := by decide, code := himg3.memset, ram := hram
        code_off := .inr (by simp only [memsetBase, Memset.code_len]; omega) }
    refine Triple.lmap (fun c h => At.reshape (L' := backL v.s0 sp q) (K' := v.keepR) h
        (by simp [backL, reallocAbi, Abi.keep, sKeepL]) (by simp [reallocAbi, Abi.keep, Abi.keepR, sKeepL]))
      (Triple.seq (re_step v.s0 v outp sp p q size M2 himg2.mpGrow hs hz r8 r0)
        (Triple.seq (st_step v.s0 v outp sp p q a.alloc size (writeLog M2 []) himg2.mpGrow hst (by omega) hal2 hlt h31)
          (Triple.seq (hM3 ▸ memset_call v outp sp q a.alloc size M3 himg3.mpGrow)
            (Triple.seq (Fn.Memset.correct_zero 0x800012dc#64 (reallocAbi v sp) outp M3 _ _ (by decide) hpre) ?_))))
    intro c ⟨M4, hA4, hMP⟩
    -- `memset` changed only the new block's top; the struct stores only the struct
    have k4 : Keep (fun x => q + a.alloc * 4 ≤ x ∧ x < q + a.alloc * 4 + (size - a.alloc) * 4) M3 M4 :=
      fun x hx => hMP.frame x (by omega)
    have k3 : Keep (fun x => p ≤ x ∧ x < p + 24) M2 M3 := fun x hx => by
      rw [← hM3]; exact writeLog_out _ _ _ ⟨by simp only; omega, by simp only; omega, trivial⟩
    have k43 := k3.trans k4
    have r24' : bytesT8 M4 (sp - 32 + 24) = ra := by
      rw [k43.bytesT8 fun x h1 h2 hx => by omega]; exact r24
    refine Triple.rmap (fun c hA => ⟨0#64, M4, hA.reshape (by simp [retL]) (by simp [retL, Abi.keep, Abi.keepR,
        sKeepL, hsv]), ?_⟩)
      (Triple.lmap (fun c h => At.reshape (L' := [(2, BitVec.ofNat 64 (sp - 32)), (8, v.s0)]) (K' := v.keepR) h
          (by simp [reallocAbi, Abi.keep, sKeepL]) (by simp [reallocAbi, Abi.keep, Abi.keepR, sKeepL]))
        (end_step ra v.s0 v outp sp M4
          (k4.img (fun x h1 h2 hx => by unfold textBase textLen at h2; omega) himg3).mpGrow hP.ra_al hs r24'))
      c hA4
    -- the post
    have hfr' : Fresh H q (4 * size) := Nat.mul_comm size 4 ▸ hfr
    have hh2 : Heap M2 ((q, 4 * size) :: H) := Nat.mul_comm size 4 ▸ hG.heap
    have heap4 : Heap M4 ((q, 4 * size) :: H) := hh2.frame fun x hx => by
      have hnb : ¬ InBlk (q, 4 * size) x := fun hb => by
        rcases hx with hg | ⟨_, _, h3⟩
        · have := Global.lt hg; unfold InBlk at hb; simp only at hb; omega
        · exact h3 _ (List.mem_cons_self ..) hb
      have hns : ¬ (p ≤ x ∧ x < p + 24) := fun h => hP.soff.off_foot h.1 h.2 hx
      exact k43 x fun h => h.elim hns fun h' => hnb (by unfold InBlk; simp only; omega)
    have hu : bytesT4 M2 p = BitVec.ofNat 32 a.used := by
      rw [hG.keep.bytesT4 fun x h1 h2 => wst x (by omega) (by omega)]
      simpa [Layout.offUsed] using hM1.used
    have hsg : bytesT4 M2 (p + 8) = BitVec.ofNat 32 a.sign := by
      rw [hG.keep.bytesT4 fun x h1 h2 => wst x (by omega) (by omega)]
      simpa [Layout.offSign] using hM1.sign
    have hrepr : MpAt M4 p q (grown a size) := grown_at hP.shape hlt h31
      (fun x h1 h2 => by rw [k4 x (by omega), ← hM3]; rfl) hu hsg
      (fun i hi => by
        rw [k43.bytesT4 fun x h1 h2 hx => by omega,
          bytesT4_of_getD (m := M1) (b := dp + Layout.sizeofDigit * i) fun k hk => by
          rw [show q + 4 * i + k = q + (4 * i + k) by omega]
          exact (copy _ (by omega)).trans (by rw [show dp + (4 * i + k) = dp + Layout.sizeofDigit * i + k by
            simp [Layout.sizeofDigit]; omega])]
        exact hM1.digits i hi)
      (fun i h1 h2 => bytesT4_zero fun k hk => by
        rw [show q + 4 * i + k = q + a.alloc * 4 + (4 * (i - a.alloc) + k) by omega]
        exact hMP.fill _ (by omega))
    refine .ok hlt hfr' heap4 hrepr (grown_post hP.shape hlt)
      (((hfr1.trans (HFrm.ofKeep hG.keep (blkW_sub hP))).trans (HFrm.of_frm hF3.mono)).trans
        (HFrm.ofKeep k4 fun x hx => .inr (hfr'.foot (by unfold InBlk; simp only; omega))))

end

/-- **`mp_grow` on the machine**, all paths. -/
theorem correct : Api.MpGrow.Statement := by
  intro m v outp H sp p dp a size ra hP
  have hs := sfacts hP
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
  have eE : heapEnd = 0x87800000 := rfl
  have eD : depth = 512 := rfl
  have eF : MpGrow.F = 544 := rfl
  have hsv := hP.ctx.sp_v
  have h31 := hP.size_lt
  have hal : bytesT4 m (p + 4) = BitVec.ofNat 32 a.alloc := by simpa [Layout.offAlloc] using hP.repr.alloc
  have hal' := hP.shape.alloc_lt
  refine Triple.lmap (fun c h => At.reshape (L' := entryL ra v.s0 sp p (BitVec.ofNat 64 size)) (K' := v.keepR) h
      (by simp [entryL, Api.MpGrow.entryL, Abi.keep, hsv]) (by simp [Abi.keep, Abi.keepR, sKeepL])) ?_
  by_cases hle : size ≤ a.alloc
  · exact Triple.rmap (fun c hA => ⟨0#64, m, hA.reshape (by simp [retL])
        (by simp [retL, Abi.keep, Abi.keepR, sKeepL, hsv]), .keep hle rfl⟩)
      (keep_step ra v.s0 v outp sp p a.alloc size m hP.ctx.img.mpGrow hP.ra_al hP.st hal hal' hle)
  have hlt : a.alloc < size := by omega
  have hdp : bytesT8 m (p + 16) = BitVec.ofNat 64 dp := by simpa [Layout.offDp] using hP.repr.dpv
  have hF1 : Frm (Un.lay MpGrow.F sp p dp a) [R.stk] m (writeLog m (frameLog ra sp p size)) :=
    Frm.store (by simp only [LogIn, frameLog, Iv.Sub, Un.lay, eF, and_true]; omega)
  have himg1 : Img (writeLog m (frameLog ra sp p size)) :=
    hF1.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.ctx.img
  have hM1 : MpAt (writeLog m (frameLog ra sp p size)) p dp a :=
    hF1.keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.repr
  have himp1 : ImpureAt (writeLog m (frameLog ra sp p size)) :=
    ImpureAt.of_keep hF1 (fun x h1 h2 hx => by
      simp only [InAny, Iv.In, Un.lay, eF, or_false] at hx; unfold impurePtr at h2; omega) hP.ctx.impure
  have hheap1 : Heap (writeLog m (frameLog ra sp p size)) (digBlk dp a :: H) :=
    hP.heap.frame fun x hx => hF1 x fun hs' => by
      simp only [InAny, Iv.In, Un.lay, or_false] at hs'
      exact hP.ctx.off.off_foot hs'.1 hs'.2 hx
  have h24 : bytesT8 (writeLog m (frameLog ra sp p size)) (sp - 8) = ra :=
    bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog, OutLRange]; omega)
  have h8 : bytesT8 (writeLog m (frameLog ra sp p size)) (sp - 24) = BitVec.ofNat 64 p :=
    bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog, OutLRange]; omega)
  have h0 : bytesT8 (writeLog m (frameLog ra sp p size)) (sp - 32) = BitVec.ofNat 64 size :=
    bytesT8_log _ _ 2 _ _ rfl (by simp [frameLog, OutLRange])
  have hctx : Ctx (writeLog m (frameLog ra sp p size)) (reallocAbi v sp) (sp - 32) depth 0x800012a8#64 :=
    hP.ctx.ctx (k := 32) (by decide) (by simp only [MpGrow.F]; omega) rfl rfl himg1 himp1 (by decide)
  exact Triple.seq (pro_step ra v.s0 v outp sp p a.alloc dp size m hP.ctx.img.mpGrow hP.st hs hal hal' hlt h31 hdp)
    (Triple.seq (realloc_call ra v outp sp p dp size _ himg1.mpGrow)
      (Triple.seq (Fn.Alloc.realloc_correct hctx hheap1 (by omega) (by omega))
        (fun c ⟨q, M2, hA, hpost⟩ => after hP hlt hF1 hM1 h24 h8 h0 himg1 q M2 hpost c hA)))

/-- **`mp_grow` with `size < 0`.** -/
theorem correct_val : Api.MpGrow.ValStatement := by
  intro m v outp p size ra himg hra hs
  have hsp : BitVec.ofNat 64 v.sp.toNat = v.sp := by simp
  refine Triple.lmap (fun c h => At.reshape (L' := entryL ra v.s0 v.sp.toNat p size) (K' := v.keepR) h
      (by simp [entryL, Api.MpGrow.entryL, Abi.keep, hsp]) (by simp [Abi.keep, Abi.keepR, sKeepL]))
    (Triple.rmap (fun c h => At.reshape h (by simp [retL]) (by simp [retL, Abi.keep, Abi.keepR, sKeepL, hsp]))
      (val_step ra v.s0 v outp v.sp.toNat p size m himg.mpGrow hra hs))

end Tom.Machine.Fn.MpGrowR
