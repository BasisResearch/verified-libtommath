import Tom.Machine.Fn.CallocKit

/-!
# `calloc(n, sz)` on the machine: the whole function (`Api.Alloc.Calloc_Statement`)

The segments of `Fn/Calloc.lean` around three calls: `__muldi3`
(`Fn.Libgcc.Muldi3.correct`), `_malloc_r` (`Fn.Alloc.mallocR_correct`) and,
for capacities beyond 72 bytes, `memset` (`Fn.Memset.correct`). After a
non-NULL `_malloc_r`, `Heap.cap` gives the chunk's capacity `cap = sz - 8 ≥ n`
(the word `_calloc_r` computes from the header) and that zeroing the whole
`[p, p + cap)` keeps `Heap` with the requested block `(p, n)`: so the contract
holds with the requested size.
-/


namespace Tom.Machine.Fn.Calloc

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Vsa.Machine (Config)
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc

/-- `cap = 24`. -/
theorem path24 (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp q : Nat) (M2 : Mem)
    (P : PathCtx M2 ra sp q 24) (h8 : bytesT8 M2 (sp - 8) = ra) (h16 : bytesT8 M2 (sp - 16) = s0) :
    Triple (At 0x800077f0#64 (hL sp q 24) M2 v.keepR outp)
      (fun c => ∃ M3, At ra (retL ra s0 sp q) M3 v.keepR outp c ∧ Zeroed M2 M3 sp q 24) := by
  have P1 := P.q1; have P2 := P.q2; have P3 := P.qa; have := P.sp1
  have Z : Zeroed M2 (writeLog M2 (z3 q)) sp q 24 := by
    rw [z3_zs]; exact zeroed_zs rfl sp
  refine Triple.seq (h24_step v outp sp q 24 M2 P.hc (by decide)) ?_
  refine Triple.seq (z3_step v outp sp q q M2 P.hc P1 (by omega) (by omega)) ?_
  refine Triple.rmap (fun c h => ⟨_, h, Z⟩) ?_
  exact e_step ra s0 v outp sp q _ (P.code Z.keep) P.sp1 P.sp2 P.spa P.hra
    ((P.word Z.keep (by omega) (by omega)).trans h8) ((P.word Z.keep (by omega) (by omega)).trans h16)

/-- `cap = 40`. -/
theorem path40 (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp q : Nat) (M2 : Mem)
    (P : PathCtx M2 ra sp q 40) (h8 : bytesT8 M2 (sp - 8) = ra) (h16 : bytesT8 M2 (sp - 16) = s0) :
    Triple (At 0x800077f0#64 (hL sp q 40) M2 v.keepR outp)
      (fun c => ∃ M3, At ra (retL ra s0 sp q) M3 v.keepR outp c ∧ Zeroed M2 M3 sp q 40) := by
  have P1 := P.q1; have P2 := P.q2; have P3 := P.qa; have := P.sp1
  have Z : Zeroed M2 (writeLog (writeLog M2 (z2 q)) (z3 (q + 16))) sp q 40 := by
    rw [writeLog_append, z23_zs]; exact zeroed_zs rfl sp
  have W1 : Within M2 (writeLog M2 (z2 q)) sp q 40 :=
    within_log _ (by simp [z2]) (by simp [z2] <;> omega)
  refine Triple.seq (h40_step v outp sp q 40 M2 P.hc P1 (by omega) P3 (by decide) (by decide)) ?_
  refine Triple.seq (z3b_step v outp sp q _ (P.code W1) P1 (by omega) P3) ?_
  refine Triple.rmap (fun c h => ⟨_, h, Z⟩) ?_
  exact e_step ra s0 v outp sp q _ (P.code Z.keep) P.sp1 P.sp2 P.spa P.hra
    ((P.word Z.keep (by omega) (by omega)).trans h8) ((P.word Z.keep (by omega) (by omega)).trans h16)

/-- `cap = 56`. -/
theorem path56 (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp q : Nat) (M2 : Mem)
    (P : PathCtx M2 ra sp q 56) (h8 : bytesT8 M2 (sp - 8) = ra) (h16 : bytesT8 M2 (sp - 16) = s0) :
    Triple (At 0x800077f0#64 (hL sp q 56) M2 v.keepR outp)
      (fun c => ∃ M3, At ra (retL ra s0 sp q) M3 v.keepR outp c ∧ Zeroed M2 M3 sp q 56) := by
  have P1 := P.q1; have P2 := P.q2; have P3 := P.qa; have := P.sp1
  have Z : Zeroed M2 (writeLog (writeLog M2 (z4 q)) (z3 (q + 32))) sp q 56 := by
    rw [writeLog_append, z43_zs]; exact zeroed_zs rfl sp
  have W1 : Within M2 (writeLog M2 (z4 q)) sp q 56 :=
    within_log _ (by simp [z4]) (by simp [z4] <;> omega)
  refine Triple.seq (h56_step v outp sp q 56 M2 P.hc P1 (by omega) P3 (by decide) (by decide)
    (by decide)) ?_
  refine Triple.seq (z3_step v outp sp q (q + 32) _ (P.code W1) (by omega) (by omega) (by omega)) ?_
  refine Triple.rmap (fun c h => ⟨_, h, Z⟩) ?_
  exact e_step ra s0 v outp sp q _ (P.code Z.keep) P.sp1 P.sp2 P.spa P.hra
    ((P.word Z.keep (by omega) (by omega)).trans h8) ((P.word Z.keep (by omega) (by omega)).trans h16)

/-- `cap = 72`. -/
theorem path72 (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp q : Nat) (M2 : Mem)
    (P : PathCtx M2 ra sp q 72) (h8 : bytesT8 M2 (sp - 8) = ra) (h16 : bytesT8 M2 (sp - 16) = s0) :
    Triple (At 0x800077f0#64 (hL sp q 72) M2 v.keepR outp)
      (fun c => ∃ M3, At ra (retL ra s0 sp q) M3 v.keepR outp c ∧ Zeroed M2 M3 sp q 72) := by
  have P1 := P.q1; have P2 := P.q2; have P3 := P.qa; have := P.sp1
  have Z : Zeroed M2 (writeLog (writeLog (writeLog M2 (z4 q)) [(q + 32, 8, 0#64), (q + 40, 8, 0#64)])
      (z3 (q + 48))) sp q 72 := by
    rw [writeLog_append, writeLog_append, z423_zs]; exact zeroed_zs rfl sp
  have W1 : Within M2 (writeLog M2 (z4 q)) sp q 72 :=
    within_log _ (by simp [z4]) (by simp [z4] <;> omega)
  have W2 : Within M2 (writeLog (writeLog M2 (z4 q)) [(q + 32, 8, 0#64), (q + 40, 8, 0#64)]) sp q 72 := by
    rw [writeLog_append]
    exact within_log _ (by simp [z4]) (by simp [z4] <;> omega)
  refine Triple.seq (h72_step v outp sp q M2 P.hc P1 (by omega) P3) ?_
  refine Triple.seq (j72_step v outp sp q _ (P.code W1) P1 (by omega) P3) ?_
  refine Triple.seq (z3_step v outp sp q (q + 48) _ (P.code W2) (by omega) (by omega) (by omega)) ?_
  refine Triple.rmap (fun c h => ⟨_, h, Z⟩) ?_
  exact e_step ra s0 v outp sp q _ (P.code Z.keep) P.sp1 P.sp2 P.spa P.hra
    ((P.word Z.keep (by omega) (by omega)).trans h8) ((P.word Z.keep (by omega) (by omega)).trans h16)

/-- The registers `memset` sees: this frame's `sp`, `s0 = reent`. -/
def msAbi (v : Abi) (sp : Nat) : Abi := { v with sp := BitVec.ofNat 64 (sp - 32), s0 := reent }

/-- `cap > 72`: `memset(q, 0, cap)`. -/
theorem pathS (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp q K : Nat) (M2 : Mem)
    (P : PathCtx M2 ra sp q K) (hI : Img M2) (hK : 72 < K) (hKl : K < 2 ^ 32)
    (hcap : (bytesT8 M2 (q - 8) &&& 0xfffffffffffffffc#64) + 0xfffffffffffffff8#64 = BitVec.ofNat 64 K)
    (h8 : bytesT8 M2 (sp - 8) = ra) (h16 : bytesT8 M2 (sp - 16) = s0) :
    Triple (At 0x800077d4#64 (aL sp q) M2 ((8, reent) :: v.keepR) outp)
      (fun c => ∃ M3, At ra (retL ra s0 sp q) M3 v.keepR outp c ∧ Zeroed M2 M3 sp q K) := by
  have P1 := P.q1; have P2 := P.q2; have P3 := P.qa; have := P.sp1; have := P.sp2
  let Ms := writeLog M2 [(sp - 32, 8, BitVec.ofNat 64 q)]
  have hWs : ∀ x, ¬ (sp - 32 ≤ x ∧ x < sp - 24) → Ms[x]? = M2[x]? := fun x hx =>
    writeLog_out _ _ _ ⟨by simp only; omega, trivial⟩
  have hcs : CodeAt Ms callocRBase callocRCode :=
    P.code (fun x _ h2 => hWs x h2)
  have hms : CodeAt Ms memsetBase memsetCode := (img_of hI fun x hx => hWs x (by omega)).memset
  have hpre : Triple (At 0x800077d4#64 (aL sp q) M2 ((8, reent) :: v.keepR) outp)
      (At Memset.entry (Memset.entryL 0x80007848#64 q (BitVec.ofNat 64 0) K) Ms (msAbi v sp).keep outp) := by
    refine Triple.seq (h0_step v outp sp q K M2 P.hc P1 (by omega) hcap hK hKl) ?_
    refine Triple.seq (s_step v outp sp q K M2 P.hc P.sp1 P.sp2 P.spa) ?_
    refine Triple.rmap (fun c h => ?_) (jal_at (pc := 0x80007844#64) (w := 0x361010ef#32)
      (imm := 0x001b60#21) (L' := sL sp q K)
      (hcs.word (a := (0x80007844#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (fun p hp => hp) (by simp [sL, keysG]) (by simp [Abi.keepR, keysG, sKeepL]))
    have hpc : (0x80007844#64 : BitVec 64) + sign_extend (m := 64) (0x001b60#21) = Memset.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [Memset.entryL, sL, Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR, msAbi, sKeepL, sL]
  intro c hc
  obtain ⟨c1, s1, h1⟩ := hpre c hc
  have hram : Ram q K := ⟨by omega, by omega, Or.inr (by simp [tohostAddr]; omega)⟩
  obtain ⟨c2, s2, M, hA2, hpost⟩ := Memset.correct 0x80007848#64 (msAbi v sp) outp Ms q 0 K
    (by decide) ⟨by decide, hms, hram, Or.inr (by
      have : memsetCode.length = 55 := rfl
      simp only [memsetBase]; omega)⟩ c1 h1
  have hW : Within M2 M sp q K := fun x h1 h2 => by
    rw [hpost.frame x (by omega), hWs x h2]
  have hq : bytesT8 M (sp - 32) = BitVec.ofNat 64 q := by
    rw [hpost.word (by omega)]
    exact bytesT8_log [(sp - 32, 8, BitVec.ofNat 64 q)] M2 0 _ _ rfl trivial
  obtain ⟨c3, s3, hA3⟩ := t_step ra s0 v outp sp q M (P.code hW) P.sp1 P.sp2 P.spa P.hra hq
    ((P.word hW (by omega) (by omega)).trans h8) ((P.word hW (by omega) (by omega)).trans h16) c2
    (hA2.reshape (by simp [msAbi, Abi.keep]) (by simp [Abi.keep, Abi.keepR, msAbi, sKeepL]))
  exact ⟨c3, s1.trans (s2.trans s3), M, hA3,
    ⟨fun x h1 h2 => by
      have := hpost.fill (x - q) (by omega)
      rwa [Nat.add_sub_cancel' h1] at this, hW⟩⟩

/-! ## The whole function -/

theorem foot_lt {H : List (Nat × Nat)} {a : Nat} (h : Foot H a) : a < heapEnd := by
  rcases h with hg | ⟨_, h2, _⟩
  · have := Global.lt hg; have : heapStart < heapEnd := by decide
    omega
  · exact h2

theorem stk_mono {sp a : Nat} (h : Stk (sp - 32) depth a) (hsp : 32 ≤ sp) : Stk sp callocDepth a := by
  have e1 : depth = 512 := rfl
  have e2 : callocDepth = 544 := rfl
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, by omega⟩

theorem stk_top {sp a : Nat} (h1 : sp - 32 ≤ a) (h2 : a < sp) : Stk sp callocDepth a := by
  have e2 : callocDepth = 544 := rfl
  exact ⟨by omega, h2⟩

theorem mallocW_sub {H : List (Nat × Nat)} {sp a : Nat} (hsp : 32 ≤ sp)
    (h : Fn.Alloc.mallocW H (sp - 32) a) : callocW H sp a := by
  rcases h with h | h
  · exact .inl h
  · exact .inr (stk_mono h hsp)

/-- From a zeroing path's end to the contract's result. -/
theorem finish {m M1 M2 M3 : Mem} {v : Abi} {outp : Array String} {H : List (Nat × Nat)}
    {sp q N sz : Nat} {ra : BitVec 64} {c : Config} (hsv : v.sp = BitVec.ofNat 64 sp)
    (hsp1 : 0x87800220 ≤ sp)
    (hM1 : ∀ x, ¬ (sp - 16 ≤ x ∧ x < sp) → M1[x]? = m[x]?)
    (hgot : Got M1 M2 H (Fn.Alloc.mallocW H (sp - 32)) q N) (C : Fn.Alloc.Cap M2 H q N sz)
    (hA : At ra (retL ra v.s0 sp q) M3 v.keepR outp c) (Z : Zeroed M2 M3 sp q (sz - 8)) :
    CallocRet m v outp H sp N ra c := by
  have eE : heapEnd = 0x87800000 := rfl
  have hroom := C.room
  refine ⟨q, M3, hA.reshape (by simp [retL]) (by simp [retL, Abi.keep, Abi.keepR, hsv, sKeepL]),
    .ok ⟨hgot.fresh, C.keep M3 fun a hf hn => Z.keep a hn (by have := foot_lt hf; omega), ?_⟩
      fun i hi => Z.zero (q + i) (by omega) (by omega)⟩
  intro a ha
  have hW : ¬ (q ≤ a ∧ a < q + (sz - 8)) := fun h => ha (.inl (C.slack a h.1 h.2))
  have hS : ¬ (sp - 32 ≤ a ∧ a < sp - 24) := fun h => ha (Or.inr (stk_top h.1 (by omega)))
  rw [Z.keep a hW hS, hgot.keep a (fun h => ha (mallocW_sub (by omega) h)),
    hM1 a (fun h => ha (Or.inr (stk_top (by omega) h.2)))]

/-- **`calloc(n, sz)` on the machine.** -/
theorem calloc_correct : Calloc_Statement := by
  intro m v outp H sp n sz ra hC hH hn hsz c0 hA0
  have hspl := hC.sp_lo
  have eE : heapEnd = 0x87800000 := rfl
  have eD : callocDepth = 544 := rfl
  have hsp2 := hC.sp_hi
  have hal := hC.sp_al
  have hsp1 : 0x87800220 ≤ sp := by omega
  have I := hC.img
  have hN : n * sz < 2 ^ 64 := by
    have := Nat.mul_le_mul (Nat.le_of_lt_succ hn) (Nat.le_of_lt_succ hsz)
    omega
  -- `calloc` → `_calloc_r`, the prologue
  obtain ⟨c1, s1, hA1⟩ := w_step ra v.s0 v outp sp n sz m I.calloc (impure_word hC.impure) c0
    (hA0.reshape (by simp [wL, callocL, Abi.keep, hC.sp_v, hC.gp, gpV])
      (by simp [Abi.keep, Abi.keepR, sKeepL]))
  obtain ⟨c2, s2, hA2⟩ := p_step ra v.s0 v outp sp n sz m I.callocR hsp1 hsp2 hal hn hsz c1 hA1
  have hM1 : ∀ x, ¬ (sp - 16 ≤ x ∧ x < sp) → (writeLog m (pLog ra v.s0 sp))[x]? = m[x]? :=
    fun x hx => writeLog_out _ _ _ (by unfold pLog; exact ⟨by simp only; omega, by simp only; omega, trivial⟩)
  have I1 : Img (writeLog m (pLog ra v.s0 sp)) := img_of I fun x (hx : x < 0x80018880) => hM1 x (by omega)
  -- `__muldi3(n, sz)`
  obtain ⟨c3, s3, hA3⟩ := jal_at (pc := 0x800077c4#64) (w := 0x57d0f0ef#32) (imm := 0x00fd7c#21)
    (L' := [(2, BitVec.ofNat 64 (sp - 32)), (3, gpv), (8, reent), (10, BitVec.ofNat 64 n),
      (11, BitVec.ofNat 64 sz)])
    (I1.callocR.word (a := (0x800077c4#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
    (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
    (by simp [pL]) (by simp [keysG]) (by simp [Abi.keepR, keysG, sKeepL]) c2 hA2
  have hpc3 : (0x800077c4#64 : BitVec 64) + sign_extend (m := 64) (0x00fd7c#21) =
      Api.Libgcc.muldi3Entry := by decide
  rw [hpc3] at hA3
  obtain ⟨c4, s4, hA4⟩ := Fn.Libgcc.Muldi3.correct (v := msAbi v sp) (ra := 0x800077c8#64)
    (x := BitVec.ofNat 64 n) (y := BitVec.ofNat 64 sz) I1 (by decide) c3
    (hA3.reshape (by simp [pL, Sail.BitVec.addInt]) (by simp [Abi.keep, Abi.keepR, msAbi, sKeepL, pL]))
  rw [← BitVec.ofNat_mul] at hA4
  -- `_malloc_r(reent, n * sz)`
  obtain ⟨c5, s5, hA5⟩ := m_step v outp sp (n * sz) _ I1.callocR c4
    (hA4.reshape (by simp [qL, msAbi, Abi.keep]) (by simp [Abi.keep, Abi.keepR, msAbi, sKeepL]))
  obtain ⟨c6, s6, hA6⟩ := jal_at (pc := 0x800077d0#64) (w := 0x19c000ef#32) (imm := 0x00019c#21)
    (L' := [(2, BitVec.ofNat 64 (sp - 32)), (8, reent), (10, reent), (11, BitVec.ofNat 64 (n * sz))])
    (I1.callocR.word (a := (0x800077d0#64 : BitVec 64).toNat) (by decide)) (by decide) (by decide)
    (fun s h1 h2 h3 => decodeW s h1 h2 h3)
    ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
    (by simp [mL]) (by simp [keysG]) (by simp [Abi.keepR, keysG, sKeepL]) c5 hA5
  have hpc6 : (0x800077d0#64 : BitVec 64) + sign_extend (m := 64) (0x00019c#21) =
      Fn.Alloc.mallocREntry := by decide
  rw [hpc6] at hA6
  have hC1 : Ctx (writeLog m (pLog ra v.s0 sp)) (msAbi v sp) (sp - 32) depth 0x800077d4#64 :=
    { img := I1, impure := impure_of hC.impure fun x h1 h2 => hM1 x (by omega), gp := hC.gp
      sp_v := rfl, sp_al := by omega, sp_lo := by have : depth = 512 := rfl; omega, sp_hi := by omega
      ra_al := by decide }
  have hH1 : Heap (writeLog m (pLog ra v.s0 sp)) H :=
    Heap.frame hH fun a ha => hM1 a (by have := foot_lt ha; omega)
  obtain ⟨c7, s7, q, M2, hA7, hpost⟩ := Fn.Alloc.mallocR_correct hC1 hH1 hN c6
    (hA6.reshape (by simp [Fn.Alloc.mallocRL, mL, Sail.BitVec.addInt, Fn.Alloc.reent])
      (by simp [Abi.keep, Abi.keepR, msAbi, sKeepL, mL]))
  have hk2 : Keep (Fn.Alloc.mallocW H (sp - 32)) (writeLog m (pLog ra v.s0 sp)) M2 := by
    cases hpost with
    | null h => exact h.keep
    | ok h => exact h.keep
  have hoff : ∀ x, sp - 32 ≤ x → ¬ Fn.Alloc.mallocW H (sp - 32) x := fun x hx h => by
    rcases h with h | ⟨_, h2⟩
    · have := foot_lt h; omega
    · omega
  have h8 : bytesT8 M2 (sp - 8) = ra := by
    rw [hk2.word fun x h1 _ => hoff x (by omega)]
    exact bytesT8_log (pLog ra v.s0 sp) m 1 _ _ rfl trivial
  have h16 : bytesT8 M2 (sp - 16) = v.s0 := by
    rw [hk2.word fun x h1 _ => hoff x (by omega)]
    exact bytesT8_log (pLog ra v.s0 sp) m 0 _ _ rfl ⟨by simp only; omega, trivial⟩
  have eD2 : depth = 512 := rfl
  have I2 : Img M2 := img_of I1 fun x (hx : x < 0x80018880) => hk2 x (fun h => by
    rcases h with h | ⟨h1, _⟩
    · rcases h with hg | ⟨h1, _, _⟩
      · unfold Global at hg; omega
      · have : heapStart = 0x80019d10 := rfl; omega
    · omega)
  cases hpost with
  | null hnull =>
    obtain ⟨c8, s8, hA8⟩ := n_step ra v.s0 v outp sp M2 I2.callocR hsp1 hsp2 hal hC.ra_al h8 h16 c7
      (hA7.reshape (by simp [aL, msAbi, Abi.keep]) (by simp [Abi.keep, Abi.keepR, msAbi, sKeepL]))
    refine ⟨c8, s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans s8)))))), 0, M2,
      hA8.reshape (by simp [retL]) (by simp [retL, Abi.keep, Abi.keepR, hC.sp_v, sKeepL]),
      .null ⟨hnull.heap, fun a ha => ?_⟩⟩
    rw [hk2 a (fun h => ha (by
        rcases h with h | ⟨h1, h2⟩
        · exact .inl h
        · exact .inr ⟨by unfold depth at h1; omega, by omega⟩)),
      hM1 a (fun h => ha (.inr ⟨by omega, h.2⟩))]
  | ok hgot =>
    obtain ⟨sz', C⟩ := Fn.Alloc.Heap.cap hgot.heap
    have hcapw := cap_word (x := bytesT8 M2 (q - 8)) (by rw [bytesT8_wordOf]; exact C.hdr) C.min
    have hal16 := C.al; have hmin := C.min; have hlo := C.lo; have hhi := C.hi
    have hqa := hgot.fresh.al
    have eS : heapStart = 0x80019d10 := rfl
    have P : PathCtx M2 ra sp q (sz' - 8) :=
      ⟨I2.callocR, hsp1, hsp2, hal, hC.ra_al, by have : heapStart = 0x80019d10 := rfl; omega,
        by omega, hqa⟩
    have hA7' : At 0x800077d4#64 (aL sp q) M2 ((8, reent) :: v.keepR) outp c7 :=
      hA7.reshape (by simp [aL, msAbi, Abi.keep]) (by simp [Abi.keep, Abi.keepR, msAbi, sKeepL])
    have steps7 := s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7)))))
    have hhs : ∀ (K : Nat), K = sz' - 8 → K ≤ 72 →
        Triple (At 0x800077f0#64 (hL sp q K) M2 v.keepR outp)
          (fun c => ∃ M3, At ra (retL ra v.s0 sp q) M3 v.keepR outp c ∧ Zeroed M2 M3 sp q K) := by
      intro K hK hK72
      subst hK
      rcases (by omega : sz' - 8 = 24 ∨ sz' - 8 = 40 ∨ sz' - 8 = 56 ∨ sz' - 8 = 72) with e | e | e | e <;>
        rw [e] <;> rw [e] at P
      · exact path24 ra v.s0 v outp sp q M2 P h8 h16
      · exact path40 ra v.s0 v outp sp q M2 P h8 h16
      · exact path56 ra v.s0 v outp sp q M2 P h8 h16
      · exact path72 ra v.s0 v outp sp q M2 P h8 h16
    by_cases h72 : sz' - 8 ≤ 72
    · obtain ⟨c8, s8, hA8⟩ := h_step v outp sp q (sz' - 8) M2 I2.callocR (by omega) (by omega) hcapw h72 c7
        (hA7.reshape (by simp [aL, msAbi, Abi.keep]) (by simp [Abi.keep, Abi.keepR, msAbi, sKeepL]))
      obtain ⟨c9, s9, M3, hA9, Z⟩ := hhs (sz' - 8) rfl h72 c8 hA8
      exact ⟨c9, steps7.trans (s8.trans s9), finish hC.sp_v hsp1 hM1 hgot C hA9 Z⟩
    · obtain ⟨c9, s9, M3, hA9, Z⟩ := pathS ra v.s0 v outp sp q (sz' - 8) M2 P I2 (by omega)
        (by omega) hcapw h8 h16 c7 hA7'
      exact ⟨c9, steps7.trans s9, finish hC.sp_v hsp1 hM1 hgot C hA9 Z⟩

end Tom.Machine.Fn.Calloc
