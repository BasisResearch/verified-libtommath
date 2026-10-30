import Tom.Machine.Api.MpClear

/-!
# `mp_clear` on the machine: the whole function

The segments of `Fn/MpClear.lean` around `free(a->dp)` (`Fn.Alloc.free_correct`,
`Api/Alloc.lean`). The regions are `Un`'s
with stack depth 544; the frame is `HFrm` (`Api/Heap.lean`): the frame stores
in `stk`, `free`'s writes in `stk` (its stack), `aD` (the freed block) and
`Foot H`, the struct stores in `aS`.
-/


namespace Tom.Machine.Fn.MpClear

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api
open Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
open Tom.Machine.Api.Un (R)

/-- The Abi `free` sees: our frame's `sp`. -/
def freeAbi (v : Abi) (sp : Nat) : Abi := { v with sp := BitVec.ofNat 64 (sp - 32) }

/-- The `free` call at `5030`, back at `5034`. -/
theorem free_call (ra : BitVec 64) (v : Abi) (outp : Array String) (sp dp : Nat) (M : Mem)
    (hc : CodeAt M mpClearBase mpClearCode) :
    Triple (At 0x80005030#64 (callL ra v.s0 sp dp) M v.keepR outp)
      (At freeEntry (freeL 0x80005034#64 dp) M (freeAbi v sp).keep outp) := by
  refine Triple.rmap (fun c h => ?_)
    (jal_at (pc := 0x80005030#64) (w := 0x131020ef#32) (imm := 0x2930#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 32)), (8, v.s0), (10, BitVec.ofNat 64 dp)])
      (hc.word (a := (0x80005030#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [callL]) (by simp [keysG]) (by simp [Abi.keepR, keysG, sKeepL]))
  have hpc : (0x80005030#64 : BitVec 64) + sign_extend (m := 64) (0x2930#21) = freeEntry := by decide
  have hra : Sail.BitVec.addInt (0x80005030#64 : BitVec 64) 4 = 0x80005034#64 := by decide
  rw [hpc, hra] at h
  exact At.reshape h (by simp [freeL]) (by simp [freeAbi, Abi.keep, Abi.keepR, sKeepL])

section
variable {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp pa adp : Nat}
  {a : MpInt} {ra : BitVec 64}

local notation "ρ" => Un.lay MpClear.F sp pa adp a

theorem sfacts (hP : MpClear.Pre m v H sp pa adp a ra) : SFacts sp :=
  have := hP.ctx.sp_lo; have := hP.ctx.sp_hi; have := hP.ctx.sp_al
  have eE : heapEnd = 0x87800000 := rfl
  have eD : depth = 512 := rfl
  { rs := ⟨by omega, by omega, .inr (by unfold tohostAddr; omega)⟩, sp_al := this, sp_ge := by omega
    code_off := .inr (by unfold mpClearBase; omega) }

/-- The stack region is off the allocator. -/
theorem stk_off (hP : MpClear.Pre m v H sp pa adp a ra) : OffHeap (ρ R.stk).base (ρ R.stk).len :=
  hP.ctx.off

/-- After `free`: reload, zero the struct, return. -/
theorem tail (hP : MpClear.Pre m v H sp pa adp a ra) {M1 : Mem}
    (hF1 : Frm ρ [R.stk] m M1) (h8 : bytesT8 M1 (sp - 24) = BitVec.ofNat 64 pa)
    (h24 : bytesT8 M1 (sp - 8) = ra) (himg : Img M1) (M2 : Mem)
    (hFP : FreePost M1 M2 H adp (4 * a.alloc) (sp - 32)) :
    Triple (At 0x80005034#64 [(1, 0x80005034#64)] M2 (freeAbi v sp).keep outp)
      (MpClear.Ret m v outp H sp pa adp a ra) := by
  have hs := sfacts hP
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
  have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  have eD : depth = 512 := rfl
  have eF : MpClear.F = 544 := rfl
  have hblk := Fn.Alloc.Heap.blk hP.heap (List.mem_cons_self ..)
  simp only at hblk
  -- `free`'s writes miss our frame slots and the text
  have hb' : heapStart ≤ adp ∧ adp + 4 * a.alloc ≤ heapEnd := ⟨by omega, hblk.2⟩
  have himg2 : Img M2 := hFP.keep.img (fun x h1 h2 => blkW_off hb' (OffHeap.text h1 h2)
    (.inl (by unfold textBase textLen at h2; omega))) himg
  have h8' : bytesT8 M2 (sp - 32 + 8) = BitVec.ofNat 64 pa := by
    rw [hFP.keep.bytesT8 fun x h1 h2 => blkW_off hb' (.inr (by omega)) (.inr (by omega)),
      show sp - 32 + 8 = sp - 24 by omega]; exact h8
  have h24' : bytesT8 M2 (sp - 32 + 24) = ra := by
    rw [hFP.keep.bytesT8 fun x h1 h2 => blkW_off hb' (.inr (by omega)) (.inr (by omega)),
      show sp - 32 + 24 = sp - 8 by omega]; exact h24
  have hpc : pa + 24 ≤ mpClearBase ∨ mpClearBase + 60 ≤ pa := by
    have h := hP.lay.disj (r := R.aS) (s := R.code)
    simp only [Iv.Disj, Disj, Un.lay, textIv, textBase, textLen] at h
    simp only [mpClearBase]; omega
  have hsv := hP.ctx.sp_v
  refine Triple.lmap (fun c h => At.reshape (L' := backL v.s0 sp) (K' := v.keepR) h
      (by simp [backL, freeAbi, Abi.keep, sKeepL]) (by simp [freeAbi, Abi.keep, Abi.keepR, sKeepL]))
    (Triple.seq (back_step ra v.s0 v outp sp pa M2 himg2.mpClear hs h8' h24')
      (Triple.rmap (fun c hA => ⟨_, hA.reshape (by simp [retL]) (by simp [retL, Abi.keep, Abi.keepR, sKeepL, hsv]), ?_⟩)
        (zero_step ra v.s0 v outp sp pa (writeLog M2 []) himg2.mpClear hP.ra_al hP.st hP.st_al hpc hs)))
  -- the post
  have hsoff := hP.soff
  have hout : ∀ x, ¬ (pa ≤ x ∧ x < pa + 24) → (writeLog (writeLog M2 []) (epiLog pa))[x]? = M2[x]? :=
    fun x hx => writeLog_out _ _ _
      ⟨by simp only; omega, by simp only; omega, by simp only; omega, trivial⟩
  refine { repr := cleared_at _ pa, heap := hFP.heap.frame fun x hx => hout x fun h => hsoff.off_foot h.1 h.2 hx
           frame := fun x hx => ?_ }
  simp only [InAny, Un.ws, Iv.In, Un.lay, not_or, eF] at hx
  obtain ⟨⟨hxs, hxa, hxd, -⟩, hxf⟩ := hx
  rw [hout x hxa, hFP.keep x ?_, hF1 x (by simp only [InAny, Iv.In, Un.lay, eF, or_false]; omega)]
  rintro (hf | hb | hk)
  · exact hxf (Foot.of_cons hf)
  · exact hxd hb
  · unfold Stk at hk; omega

end

/-- **`mp_clear` on the machine.** -/
theorem correct : Api.MpClear.Statement := by
  intro m v outp H sp pa adp a ra hP
  have hs := sfacts hP
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
  have eE : heapEnd = 0x87800000 := rfl
  have eS : heapStart = 0x80019d10 := rfl
  have eD : depth = 512 := rfl
  have hsv := hP.ctx.sp_v
  have hblk := Fn.Alloc.Heap.blk hP.heap (List.mem_cons_self ..)
  simp only at hblk
  have hdp : bytesT8 m (pa + 16) = BitVec.ofNat 64 adp := by simpa [Layout.offDp] using hP.repr.dpv
  have hz : (BitVec.ofNat 64 adp == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    simp at this; omega
  -- the frame stores
  have hF1 : Frm (Un.lay MpClear.F sp pa adp a) [R.stk] m (writeLog m (proLog ra sp pa)) :=
    Frm.store (by simp only [LogIn, proLog, Iv.Sub, Un.lay, MpClear.F, and_true]; omega)
  have himg1 : Img (writeLog m (proLog ra sp pa)) :=
    hF1.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.ctx.img
  have hoffs : ∀ x, ¬ Foot H x → ¬ InAny (Un.lay MpClear.F sp pa adp a) [R.stk] x → True := fun _ _ _ => trivial
  have hstk_foot : ∀ (K : List (Nat × Nat)) x, InAny (Un.lay MpClear.F sp pa adp a) [R.stk] x → ¬ Foot K x :=
    fun K x hx => by
      simp only [InAny, Iv.In, Un.lay, or_false] at hx
      exact (stk_off hP).off_foot hx.1 hx.2
  have himp1 : ImpureAt (writeLog m (proLog ra sp pa)) :=
    ImpureAt.of_keep hF1 (fun x h1 h2 hx => by
      simp only [InAny, Iv.In, Un.lay, MpClear.F, or_false] at hx; unfold impurePtr at h2; omega) hP.ctx.impure
  have hheap1 : Heap (writeLog m (proLog ra sp pa)) (digBlk adp a :: H) :=
    hP.heap.frame fun x hx => hF1 x fun hs' => hstk_foot _ x hs' hx
  have hctx : Ctx (writeLog m (proLog ra sp pa)) (freeAbi v sp) (sp - 32) depth 0x80005034#64 :=
    hP.ctx.ctx (k := 32) (by decide) (by simp only [MpClear.F]; omega) rfl rfl himg1 himp1 (by decide)
  have h8 : bytesT8 (writeLog m (proLog ra sp pa)) (sp - 24) = BitVec.ofNat 64 pa :=
    bytesT8_log _ _ 0 _ _ rfl (by simp [proLog, OutLRange]; omega)
  have h24 : bytesT8 (writeLog m (proLog ra sp pa)) (sp - 8) = ra :=
    bytesT8_log _ _ 1 _ _ rfl (by simp [proLog, OutLRange])
  refine Triple.lmap (fun c h => At.reshape (L' := entryL ra v.s0 sp pa) (K' := v.keepR) h
      (by simp [entryL, Api.MpClear.entryL, Abi.keep, hsv]) (by simp [Abi.keep, Abi.keepR, sKeepL]))
    (Triple.seq (pro_step ra v.s0 v outp sp pa adp m hP.ctx.img.mpClear hP.st hs hdp hz)
      (Triple.seq (free_call ra v outp sp adp _ himg1.mpClear)
        (Triple.seq (Fn.Alloc.free_correct hctx hheap1)
          (fun c ⟨M2, hA, hFP⟩ => tail hP hF1 h8 h24 himg1 M2 hFP c hA))))

/-- **`mp_clear` of a cleared `mp_int`.** -/
theorem correct_null : Api.MpClear.NullStatement := by
  intro m v outp pa ra hdp hp himg hra
  have hsp : BitVec.ofNat 64 v.sp.toNat = v.sp := by simp
  refine Triple.lmap (fun c h => At.reshape (L' := entryL ra v.s0 v.sp.toNat pa) (K' := v.keepR) h
      (by simp [entryL, Api.MpClear.entryL, Abi.keep, hsp]) (by simp [Abi.keep, Abi.keepR, sKeepL]))
    (Triple.rmap (fun c h => At.reshape h (by simp [retL]) (by simp [retL, Abi.keep, Abi.keepR, sKeepL, hsp]))
      (null_step ra v.s0 v outp v.sp.toNat pa m himg.mpClear hra hp hdp))

end Tom.Machine.Fn.MpClear
