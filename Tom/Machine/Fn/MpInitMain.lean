import Tom.Machine.Api.MpInit
import Tom.Machine.Fn.CallocMain

/-!
# `mp_init_size`, `mp_init` on the machine: the whole functions

The segments of `Fn/MpInit.lean` around `calloc(n, 4)`
(`Fn.Calloc.calloc_correct`). The regions are `MpInit.R`; the frame is `HFrm`: the frame stores
in `stk`, `calloc`'s writes in `stk` (its stack) and `Foot H`, the struct
stores in `aS`. `post_ok`/`post_mem` build the two `Post` branches once for
both functions.
-/


namespace Tom.Machine.Fn.MpInit

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api
open Tom.Machine.Api.Alloc Tom.Machine.Api.Heap
open Tom.Machine.Api.MpInit (R)

/-! ## The posts, for both functions -/

section
variable {m M1 M2 M3 : Mem} {v : Abi} {H : List (Nat × Nat)} {sp pa F n sp' q : Nat} {ra : BitVec 64}

local notation "ρ" => MpInit.lay F sp pa

theorem aS_off (hP : MpInit.Pre m v H sp pa F ra) {K : List (Nat × Nat)} {x : Nat}
    (hx : InAny ρ [R.aS] x) : ¬ Foot K x := by
  simp only [InAny, Iv.In, MpInit.lay, or_false] at hx
  exact hP.soff.off_foot hx.1 hx.2

theorem stk_off (hP : MpInit.Pre m v H sp pa F ra) {K : List (Nat × Nat)} {x : Nat}
    (hx : InAny ρ [R.stk] x) : ¬ Foot K x := by
  simp only [InAny, Iv.In, MpInit.lay, or_false] at hx
  exact hP.ctx.off.off_foot hx.1 hx.2

/-- The frame of the three phases. -/
theorem frame3 (hF1 : Frm ρ [R.stk] m M1) {W : Nat → Prop} (hk : Keep W M1 M2)
    (hW : ∀ x, W x → InAny ρ [R.stk] x ∨ Foot H x) (hF3 : Frm ρ [R.aS] M2 M3) :
    HFrm ρ MpInit.ws H m M3 := fun x hx => by
  simp only [InAny, MpInit.ws, not_or] at hx
  obtain ⟨⟨hs, ha, -⟩, hf⟩ := hx
  rw [hF3 x (by simp only [InAny, or_false]; exact ha), hk x (fun hw => (hW x hw).elim
    (fun h => hs (by simpa only [InAny, or_false] using h)) hf), hF1 x (by simp only [InAny, or_false]; exact hs)]

/-- **Non-null**: the fresh block, `a` live and zero. -/
theorem post_ok (hP : MpInit.Pre m v H sp pa F ra) (hF1 : Frm ρ [R.stk] m M1)
    (hW : ∀ x, callocW H sp' x → InAny ρ [R.stk] x ∨ Foot H x)
    (hG : Got M1 M2 H (callocW H sp') q (n * 4)) (hF3 : Frm ρ [R.aS] M2 M3)
    (hrepr : MpAt M3 pa q (MpInt.zeroN n)) : MpInit.Post m M3 H sp pa F n 0#64 := by
  have hfr := hG.fresh; have hh := hG.heap
  rw [Nat.mul_comm] at hfr hh
  have hh3 : Heap M3 ((q, 4 * n) :: H) := hh.frame fun x hx => hF3 x fun h => aS_off hP h hx
  exact .ok hfr hh3 ⟨hrepr, List.mem_cons_self .., hP.soff⟩ (frame3 hF1 hG.keep hW hF3)

/-- **Null**: the heap as it was, `dp = NULL`. -/
theorem post_mem (hP : MpInit.Pre m v H sp pa F ra) (hF1 : Frm ρ [R.stk] m M1)
    (hW : ∀ x, callocW H sp' x → InAny ρ [R.stk] x ∨ Foot H x)
    (hN : Null M1 M2 H (callocW H sp')) (hF3 : Frm ρ [R.aS] M2 M3)
    (hdp : bytesT8 M3 (pa + 16) = 0#64) : MpInit.Post m M3 H sp pa F n MpInit.memBV :=
  .mem (hN.heap.frame fun x hx => hF3 x fun h => aS_off hP h hx) hdp (frame3 hF1 hN.keep hW hF3)

end

/-! ## `mp_init_size` -/

/-- The Abi `calloc` sees: our frame's `sp`, `s0 = a`, `s1 = n`. -/
def callocAbi (v : Abi) (sp pa n : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 32), s0 := BitVec.ofNat 64 pa, s := { v.s with s1 := BitVec.ofNat 64 n } }

/-- The `calloc` call at `14c4`, back at `14c8`. -/
theorem calloc_call (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa n : Nat) (M : Mem)
    (hc : CodeAt M mpInitSizeBase mpInitSizeCode) :
    Triple (At 0x800014c4#64 (callL ra sp pa n) M v.keepR1 outp)
      (At callocEntry (callocL 0x800014c8#64 n 4) M (callocAbi v sp pa n).keep outp) := by
  refine Triple.rmap (fun c h => ?_)
    (jal_at (pc := 0x800014c4#64) (w := 0x2b8060ef#32) (imm := 0x62b8#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 32)), (8, BitVec.ofNat 64 pa), (9, BitVec.ofNat 64 n),
        (10, BitVec.ofNat 64 n), (11, 4#64)])
      (hc.word (a := (0x800014c4#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [callL]) (by simp [keysG]) (by simp [Abi.keepR1, keysG]))
  have hpc : (0x800014c4#64 : BitVec 64) + sign_extend (m := 64) (0x62b8#21) = callocEntry := by decide
  have hra : Sail.BitVec.addInt (0x800014c4#64 : BitVec 64) 4 = 0x800014c8#64 := by decide
  rw [hpc, hra] at h
  exact At.reshape h (by simp [callocL]) (by simp [callocAbi, Abi.keep, Abi.keepR1, sKeepL])

section
variable {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp pa : Nat} {ra : BitVec 64}

local notation "ρ" => MpInit.lay MpInit.Fsize sp pa

theorem sfacts (hP : MpInit.Pre m v H sp pa MpInit.Fsize ra) : SFacts sp :=
  have := hP.ctx.sp_lo; have := hP.ctx.sp_hi; have := hP.ctx.sp_al
  have eE : heapEnd = 0x87800000 := rfl
  have eD : callocDepth = 544 := rfl
  { rs := ⟨by omega, by omega, .inr (by unfold tohostAddr; omega)⟩, sp_al := this, sp_ge := by omega
    code_off := by unfold mpInitSizeBase; omega }

theorem stfacts {F : Nat} (hP : MpInit.Pre m v H sp pa F ra) : StFacts pa :=
  have h := hP.lay.disj (r := R.aS) (s := R.code)
  { rs := hP.st, al := hP.st_al
    code_off := by simp only [Iv.Disj, Disj, MpInit.lay, textIv] at h; exact h }

/-- After `calloc` returns `q` in `M2`: the struct stores, the epilogue. -/
theorem size_tail (hP : MpInit.Pre m v H sp pa MpInit.Fsize ra) (n : Nat) (hn : n < 2 ^ 31) {M1 : Mem}
    (hF1 : Frm ρ [R.stk] m M1) (h8 : bytesT8 M1 (sp - 24) = v.s.s1) (h24 : bytesT8 M1 (sp - 8) = ra)
    (h16 : bytesT8 M1 (sp - 16) = v.s0) (himg : Img M1) (q : Nat) (M2 : Mem)
    (hpost : CallocPost M1 M2 H (sp - 32) (n * 4) q) :
    Triple (At 0x800014c8#64 [(1, 0x800014c8#64), (10, BitVec.ofNat 64 q)] M2
        (callocAbi v sp pa n).keep outp)
      (MpInit.Ret m v outp H sp pa MpInit.Fsize n ra) := by
  have hs := sfacts hP
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
  have eE : heapEnd = 0x87800000 := rfl
  have eD : callocDepth = 544 := rfl
  have eF : MpInit.Fsize = 576 := rfl
  have hsv := hP.ctx.sp_v
  have hst := stfacts hP
  have hsd := hP.lay.disj (r := R.aS) (s := R.stk)
  simp only [Iv.Disj, Disj, MpInit.lay, eF] at hsd
  -- `calloc`'s writes lie in our stack and the footprint
  have hW : ∀ x, callocW H (sp - 32) x → InAny ρ [R.stk] x ∨ Foot H x := fun x hx => hx.elim .inr
    (fun hk => .inl (by unfold Stk at hk; simp only [InAny, Iv.In, MpInit.lay, eF, or_false]; omega))
  have hkeep : ∀ (M2 : Mem), Keep (callocW H (sp - 32)) M1 M2 → ∀ x, sp - 32 ≤ x → x < sp → M2[x]? = M1[x]? :=
    fun M2 hk x h1 h2 => hk x (callocW_off (.inr (by omega)) (.inr h1))
  have himg2 : ∀ (M2 : Mem), Keep (callocW H (sp - 32)) M1 M2 → Img M2 := fun M2 hk =>
    hk.img (fun x h1 h2 => callocW_off (OffHeap.text h1 h2) (.inl (by unfold textBase textLen at h2; omega))) himg
  -- the epilogue from `M3`, for both branches
  have fin : ∀ (r : BitVec 64) (M2 M3 : Mem), Keep (callocW H (sp - 32)) M1 M2 → Frm ρ [R.aS] M2 M3 →
      Img M3 → MpInit.Post m M3 H sp pa MpInit.Fsize n r →
      Triple (At 0x800014e0#64 (epiL sp pa n r) M3 v.keepR1 outp)
        (MpInit.Ret m v outp H sp pa MpInit.Fsize n ra) := by
    intro r M2 M3 hk hF3 himg3 hpost
    have hst3 : ∀ x, sp - 32 ≤ x → x < sp → M3[x]? = M1[x]? := fun x h1 h2 => by
      rw [hF3 x (by simp only [InAny, Iv.In, MpInit.lay, or_false]; omega), hkeep M2 hk x h1 h2]
    have r24 : bytesT8 M3 (sp - 32 + 24) = ra := by
      rw [bytesT8_congr fun x h1 h2 => hst3 x (by omega) (by omega), show sp - 32 + 24 = sp - 8 by omega]; exact h24
    have r16 : bytesT8 M3 (sp - 32 + 16) = v.s0 := by
      rw [bytesT8_congr fun x h1 h2 => hst3 x (by omega) (by omega), show sp - 32 + 16 = sp - 16 by omega]; exact h16
    have r8 : bytesT8 M3 (sp - 32 + 8) = v.s.s1 := by
      rw [bytesT8_congr fun x h1 h2 => hst3 x (by omega) (by omega), show sp - 32 + 8 = sp - 24 by omega]; exact h8
    exact Triple.rmap (fun c hA => ⟨r, _, hA.reshape (by simp) (by simp [Abi.keep, Abi.keepR1, sKeepL, hsv]),
        hpost⟩)
      (epi_step ra v.s0 v.s.s1 v outp sp pa n r M3 himg3.mpInitSize hP.ra_al hs r24 r16 r8)
  cases hpost with
  | null hN =>
    have hF3 : Frm ρ [R.aS] M2 (writeLog M2 [(pa + 16, 8, 0#64)]) :=
      Frm.store (by simp only [LogIn, Iv.Sub, MpInit.lay, and_true]; omega)
    refine Triple.lmap (fun c h => At.reshape (L' := backL sp pa n 0) (K' := v.keepR1) h
        (by simp [backL, callocAbi, Abi.keep, sKeepL]) (by simp [callocAbi, Abi.keep, Abi.keepR1, sKeepL]))
      (Triple.seq (null_step v outp sp pa n M2 (himg2 M2 hN.keep).mpInitSize hst)
        (fin _ M2 _ hN.keep hF3 (hF3.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) (himg2 M2 hN.keep))
          (post_mem hP hF1 hW hN hF3 (null_dp M2 pa))))
  | ok hG hz =>
    have hfr := hG.fresh
    have hnz : (BitVec.ofNat 64 q == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h
      have h' := congrArg BitVec.toNat h
      have hhi := hfr.hi
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hfr.nz (by simpa using h')
    have hF3 : Frm ρ [R.aS] M2 (writeLog M2 (okLog pa q n)) :=
      Frm.store (by simp only [LogIn, okLog, Iv.Sub, MpInit.lay, and_true]; omega)
    have hd : Disj q (4 * n) pa 24 := Nat.mul_comm n 4 ▸ hfr.off_heap hP.soff
    refine Triple.lmap (fun c h => At.reshape (L' := backL sp pa n q) (K' := v.keepR1) h
        (by simp [backL, callocAbi, Abi.keep, sKeepL]) (by simp [callocAbi, Abi.keep, Abi.keepR1, sKeepL]))
      (Triple.seq (ok_step v outp sp pa n q M2 (himg2 M2 hG.keep).mpInitSize hst hnz)
        (fin _ M2 _ hG.keep hF3 (hF3.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) (himg2 M2 hG.keep))
          (post_ok hP hF1 hW hG hF3 (ok_at hn hd fun i hi => hz i (by omega)))))

end

/-- **`mp_init_size` on the machine**, -/
theorem size_correct : Api.MpInit.SizeStatement := by
  intro m v outp H sp pa size ra hP h31
  have hs := sfacts hP
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
  have eE : heapEnd = 0x87800000 := rfl
  have eD : callocDepth = 544 := rfl
  have eF : MpInit.Fsize = 576 := rfl
  have hsv := hP.ctx.sp_v
  have hF1 : Frm (MpInit.lay MpInit.Fsize sp pa) [R.stk] m (writeLog m (frameLog ra v.s0 v.s.s1 sp)) :=
    Frm.store (by simp only [LogIn, frameLog, Iv.Sub, MpInit.lay, eF, and_true]; omega)
  have himg1 : Img (writeLog m (frameLog ra v.s0 v.s.s1 sp)) :=
    hF1.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.ctx.img
  have himp1 : ImpureAt (writeLog m (frameLog ra v.s0 v.s.s1 sp)) :=
    ImpureAt.of_keep hF1 (fun x h1 h2 hx => by
      simp only [InAny, Iv.In, MpInit.lay, eF, or_false] at hx; unfold impurePtr at h2; omega) hP.ctx.impure
  have hheap1 : Heap (writeLog m (frameLog ra v.s0 v.s.s1 sp)) H :=
    hP.heap.frame fun x hx => hF1 x fun hs' => stk_off hP hs' hx
  have h8 : bytesT8 (writeLog m (frameLog ra v.s0 v.s.s1 sp)) (sp - 24) = v.s.s1 :=
    bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog, OutLRange]; omega)
  have h24 : bytesT8 (writeLog m (frameLog ra v.s0 v.s.s1 sp)) (sp - 8) = ra :=
    bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog, OutLRange]; omega)
  have h16 : bytesT8 (writeLog m (frameLog ra v.s0 v.s.s1 sp)) (sp - 16) = v.s0 :=
    bytesT8_log _ _ 2 _ _ rfl (by simp [frameLog, OutLRange])
  -- from the call on, for `n` digits
  have rest : ∀ n, n < 2 ^ 31 →
      Triple (At 0x800014c4#64 (callL ra sp pa n) (writeLog m (frameLog ra v.s0 v.s.s1 sp)) v.keepR1 outp)
        (MpInit.Ret m v outp H sp pa MpInit.Fsize n ra) := fun n hn =>
    have hctx : Ctx (writeLog m (frameLog ra v.s0 v.s.s1 sp)) (callocAbi v sp pa n) (sp - 32) callocDepth
        0x800014c8#64 :=
      hP.ctx.ctx (k := 32) (by decide) (by simp only [MpInit.Fsize]; omega) rfl rfl himg1 himp1 (by decide)
    Triple.seq (calloc_call ra v outp sp pa n _ himg1.mpInitSize)
      (Triple.seq (Fn.Calloc.calloc_correct hctx hheap1 (by omega) (by decide))
        (fun c ⟨q, M2, hA, hpost⟩ => size_tail hP n hn hF1 h8 h24 h16 himg1 q M2 hpost c hA))
  refine Triple.lmap (fun c h => At.reshape (L' := sizeL ra v.s0 v.s.s1 sp pa (BitVec.ofNat 64 size))
      (K' := v.keepR1) h (by simp [sizeL, Api.MpInit.sizeL, Abi.keep, sKeepL, hsv])
      (by simp [Abi.keep, Abi.keepR1, sKeepL])) ?_
  by_cases h3 : 3 ≤ size
  · have e : initPrec size = size := by simp only [initPrec, minPrec_eq]; omega
    rw [e]
    exact Triple.seq (big_step ra v.s0 v.s.s1 v outp sp pa size m hP.ctx.img.mpInitSize hs h3 h31) (rest size h31)
  · have e : initPrec size = 3 := by simp only [initPrec, minPrec_eq]; omega
    rw [e]
    exact Triple.seq (small_step ra v.s0 v.s.s1 v outp sp pa size m hP.ctx.img.mpInitSize hs (by omega))
      (rest 3 (by decide))

/-- **`mp_init_size` with `size < 0`.** -/
theorem size_val : Api.MpInit.SizeValStatement := by
  intro m v outp pa size ra himg hra hs
  have hsp : BitVec.ofNat 64 v.sp.toNat = v.sp := by simp
  refine Triple.lmap (fun c h => At.reshape (L' := sizeL ra v.s0 v.s.s1 v.sp.toNat pa size) (K' := v.keepR1) h
      (by simp [sizeL, Api.MpInit.sizeL, Abi.keep, sKeepL, hsp]) (by simp [Abi.keep, Abi.keepR1, sKeepL]))
    (Triple.rmap (fun c h => At.reshape h (by simp) (by simp [Abi.keep, Abi.keepR1, sKeepL, hsp]))
      (val_step ra v.s0 v.s.s1 v outp v.sp.toNat pa size m himg.mpInitSize hra hs))

/-! ## `mp_init` -/

/-- The Abi `calloc` sees from `mp_init`: our frame's `sp`, `s0 = a`. -/
def icallocAbi (v : Abi) (sp pa : Nat) : Abi :=
  { v with sp := BitVec.ofNat 64 (sp - 16), s0 := BitVec.ofNat 64 pa }

/-- The `calloc` call at `1314`, back at `1318`. -/
theorem icalloc_call (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa : Nat) (M : Mem)
    (hc : CodeAt M mpInitBase mpInitCode) :
    Triple (At 0x80001314#64 (icallL ra sp pa) M v.keepR outp)
      (At callocEntry (callocL 0x80001318#64 32 4) M (icallocAbi v sp pa).keep outp) := by
  refine Triple.rmap (fun c h => ?_)
    (jal_at (pc := 0x80001314#64) (w := 0x468060ef#32) (imm := 0x6468#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 16)), (8, BitVec.ofNat 64 pa), (10, 32#64), (11, 4#64)])
      (hc.word (a := (0x80001314#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [icallL]) (by simp [keysG]) (by simp [Abi.keepR, keysG, sKeepL]))
  have hpc : (0x80001314#64 : BitVec 64) + sign_extend (m := 64) (0x6468#21) = callocEntry := by decide
  have hra : Sail.BitVec.addInt (0x80001314#64 : BitVec 64) 4 = 0x80001318#64 := by decide
  rw [hpc, hra] at h
  exact At.reshape h (by simp [callocL]) (by simp [icallocAbi, Abi.keep, Abi.keepR, sKeepL])

section
variable {m : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)} {sp pa : Nat} {ra : BitVec 64}

local notation "ρ" => MpInit.lay MpInit.Finit sp pa

theorem isfacts (hP : MpInit.Pre m v H sp pa MpInit.Finit ra) : ISFacts sp :=
  have := hP.ctx.sp_lo; have := hP.ctx.sp_hi; have := hP.ctx.sp_al
  have eE : heapEnd = 0x87800000 := rfl
  have eD : callocDepth = 544 := rfl
  { rs := ⟨by omega, by omega, .inr (by unfold tohostAddr; omega)⟩, sp_al := this, sp_ge := by omega
    code_off := by unfold mpInitBase; omega }

/-- After `calloc` returns `q` in `M2`: the struct stores, the epilogue. -/
theorem init_tail (hP : MpInit.Pre m v H sp pa MpInit.Finit ra) {M1 : Mem}
    (hF1 : Frm ρ [R.stk] m M1) (h8 : bytesT8 M1 (sp - 8) = ra) (h0 : bytesT8 M1 (sp - 16) = v.s0)
    (himg : Img M1) (q : Nat) (M2 : Mem) (hpost : CallocPost M1 M2 H (sp - 16) (32 * 4) q) :
    Triple (At 0x80001318#64 [(1, 0x80001318#64), (10, BitVec.ofNat 64 q)] M2
        (icallocAbi v sp pa).keep outp)
      (MpInit.Ret m v outp H sp pa MpInit.Finit defPrec ra) := by
  have hs := isfacts hP
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
  have eE : heapEnd = 0x87800000 := rfl
  have eD : callocDepth = 544 := rfl
  have eF : MpInit.Finit = 560 := rfl
  have hsv := hP.ctx.sp_v
  have hst : IStFacts pa := let h := stfacts hP; ⟨h.rs, h.al, h.code_off⟩
  have hsd := hP.lay.disj (r := R.aS) (s := R.stk)
  simp only [Iv.Disj, Disj, MpInit.lay, eF] at hsd
  have hW : ∀ x, callocW H (sp - 16) x → InAny ρ [R.stk] x ∨ Foot H x := fun x hx => hx.elim .inr
    (fun hk => .inl (by unfold Stk at hk; simp only [InAny, Iv.In, MpInit.lay, eF, or_false]; omega))
  have hkeep : ∀ (M2 : Mem), Keep (callocW H (sp - 16)) M1 M2 → ∀ x, sp - 16 ≤ x → x < sp → M2[x]? = M1[x]? :=
    fun M2 hk x h1 h2 => hk x (callocW_off (.inr (by omega)) (.inr h1))
  have himg2 : ∀ (M2 : Mem), Keep (callocW H (sp - 16)) M1 M2 → Img M2 := fun M2 hk =>
    hk.img (fun x h1 h2 => callocW_off (OffHeap.text h1 h2) (.inl (by unfold textBase textLen at h2; omega))) himg
  have fin : ∀ (r : BitVec 64) (M2 M3 : Mem), Keep (callocW H (sp - 16)) M1 M2 → Frm ρ [R.aS] M2 M3 →
      Img M3 → MpInit.Post m M3 H sp pa MpInit.Finit defPrec r →
      Triple (At 0x80001334#64 (iepiL sp pa r) M3 v.keepR outp)
        (MpInit.Ret m v outp H sp pa MpInit.Finit defPrec ra) := by
    intro r M2 M3 hk hF3 himg3 hpost
    have hst3 : ∀ x, sp - 16 ≤ x → x < sp → M3[x]? = M1[x]? := fun x h1 h2 => by
      rw [hF3 x (by simp only [InAny, Iv.In, MpInit.lay, or_false]; omega), hkeep M2 hk x h1 h2]
    have r8 : bytesT8 M3 (sp - 16 + 8) = ra := by
      rw [bytesT8_congr fun x h1 h2 => hst3 x (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]; exact h8
    have r0 : bytesT8 M3 (sp - 16) = v.s0 := by
      rw [bytesT8_congr fun x h1 h2 => hst3 x (by omega) (by omega)]; exact h0
    exact Triple.rmap (fun c hA => ⟨r, _, hA.reshape (by simp) (by simp [Abi.keep, Abi.keepR, sKeepL, hsv]),
        hpost⟩)
      (iepi_step ra v.s0 v outp sp pa r M3 himg3.mpInit hP.ra_al hs r8 r0)
  cases hpost with
  | null hN =>
    have hF3 : Frm ρ [R.aS] M2 (writeLog M2 [(pa + 16, 8, 0#64)]) :=
      Frm.store (by simp only [LogIn, Iv.Sub, MpInit.lay, and_true]; omega)
    refine Triple.lmap (fun c h => At.reshape (L' := ibackL sp pa 0) (K' := v.keepR) h
        (by simp [ibackL, icallocAbi, Abi.keep, sKeepL]) (by simp [icallocAbi, Abi.keep, Abi.keepR, sKeepL]))
      (Triple.seq (inull_step v outp sp pa M2 (himg2 M2 hN.keep).mpInit hst)
        (fin _ M2 _ hN.keep hF3 (hF3.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) (himg2 M2 hN.keep))
          (post_mem hP hF1 hW hN hF3 (null_dp M2 pa))))
  | ok hG hz =>
    have hfr := hG.fresh
    have hnz : (BitVec.ofNat 64 q == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h
      have h' := congrArg BitVec.toNat h
      have hhi := hfr.hi
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hfr.nz (by simpa using h')
    have hF3 : Frm ρ [R.aS] M2 (writeLog M2 (iokLog pa q)) :=
      Frm.store (by simp only [LogIn, iokLog, Iv.Sub, MpInit.lay, and_true]; omega)
    have hd : Disj q (4 * 32) pa 24 := hfr.off_heap hP.soff
    refine Triple.lmap (fun c h => At.reshape (L' := ibackL sp pa q) (K' := v.keepR) h
        (by simp [ibackL, icallocAbi, Abi.keep, sKeepL]) (by simp [icallocAbi, Abi.keep, Abi.keepR, sKeepL]))
      (Triple.seq (iok_step v outp sp pa q M2 (himg2 M2 hG.keep).mpInit hst hnz)
        (fin _ M2 _ hG.keep hF3 (hF3.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) (himg2 M2 hG.keep))
          (post_ok hP hF1 hW hG hF3 (iok_at hd fun i hi => hz i (by omega)))))

end

/-- **`mp_init` on the machine**, -/
theorem init_correct : Api.MpInit.Statement := by
  intro m v outp H sp pa ra hP
  have hs := isfacts hP
  have hsl := hP.ctx.sp_lo; have hsh := hP.ctx.sp_hi
  have eE : heapEnd = 0x87800000 := rfl
  have eD : callocDepth = 544 := rfl
  have eF : MpInit.Finit = 560 := rfl
  have hsv := hP.ctx.sp_v
  have hF1 : Frm (MpInit.lay MpInit.Finit sp pa) [R.stk] m (writeLog m (iframeLog ra v.s0 sp)) :=
    Frm.store (by simp only [LogIn, iframeLog, Iv.Sub, MpInit.lay, eF, and_true]; omega)
  have himg1 : Img (writeLog m (iframeLog ra v.s0 sp)) :=
    hF1.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.ctx.img
  have himp1 : ImpureAt (writeLog m (iframeLog ra v.s0 sp)) :=
    ImpureAt.of_keep hF1 (fun x h1 h2 hx => by
      simp only [InAny, Iv.In, MpInit.lay, eF, or_false] at hx; unfold impurePtr at h2; omega) hP.ctx.impure
  have hheap1 : Heap (writeLog m (iframeLog ra v.s0 sp)) H :=
    hP.heap.frame fun x hx => hF1 x fun hs' => stk_off hP hs' hx
  have h0 : bytesT8 (writeLog m (iframeLog ra v.s0 sp)) (sp - 16) = v.s0 :=
    bytesT8_log _ _ 0 _ _ rfl (by simp [iframeLog, OutLRange]; omega)
  have h8 : bytesT8 (writeLog m (iframeLog ra v.s0 sp)) (sp - 8) = ra :=
    bytesT8_log _ _ 1 _ _ rfl (by simp [iframeLog, OutLRange])
  have hctx : Ctx (writeLog m (iframeLog ra v.s0 sp)) (icallocAbi v sp pa) (sp - 16) callocDepth 0x80001318#64 :=
    hP.ctx.ctx (k := 16) (by decide) (by simp only [MpInit.Finit]; omega) rfl rfl himg1 himp1 (by decide)
  refine Triple.lmap (fun c h => At.reshape (L' := initL ra v.s0 sp pa) (K' := v.keepR) h
      (by simp [initL, Api.MpInit.initL, Abi.keep, hsv]) (by simp [Abi.keep, Abi.keepR, sKeepL]))
    (Triple.seq (ipro_step ra v.s0 v outp sp pa m hP.ctx.img.mpInit hs)
      (Triple.seq (icalloc_call ra v outp sp pa _ himg1.mpInit)
        (Triple.seq (Fn.Calloc.calloc_correct hctx hheap1 (by decide) (by decide))
          (fun c ⟨q, M2, hA, hpost⟩ => init_tail hP hF1 h8 h0 himg1 q M2 hpost c hA))))

end Tom.Machine.Fn.MpInit
