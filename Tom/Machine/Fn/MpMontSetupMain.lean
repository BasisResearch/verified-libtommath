import Tom.Machine.Api.MpMontSetup
import Tom.Machine.Fn.Libgcc

/-!
# `mp_montgomery_setup` on the machine: the whole function

The segments of `Fn/MpMontSetup.lean` around six `__muldi3` calls
(`Fn.Libgcc.Muldi3.correctK`, with the keep-set `Abi.keepR2` plus our
locals); the value stored in `*rho` is `setupRho b` by `rho_lo`.
-/


namespace Tom.Machine.Fn.MpMontSetup

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Mont
open Tom.Machine.Api.MpMontSetup (R)

/-- The registers at a `__muldi3(x, y)` call. -/
def callR (sp b rp : Nat) (s2 x y : BitVec 64) : GRegs :=
  [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 rp), (18, s2), (10, x), (11, y)]

/-- A `__muldi3` call from its `jal` step. -/
theorem mul_from_jal {pc ret : BitVec 64} {imm : BitVec 21} {L : GRegs} {v : Abi} {outp : Array String}
    {sp b rp : Nat} {s2 x y : BitVec 64} {M : Mem} (himg : Img M)
    (hj : Triple (At pc L M v.keepR2 outp)
      (At (pc + sign_extend (m := 64) imm) ((1, Sail.BitVec.addInt pc 4) :: callR sp b rp s2 x y) M v.keepR2 outp))
    (hpc : pc + sign_extend (m := 64) imm = Api.Libgcc.muldi3Entry) (hret : Sail.BitVec.addInt pc 4 = ret)
    (hra : ret.toNat % 4 = 0) :
    Triple (At pc L M v.keepR2 outp) (At ret (backL sp b rp s2 (x * y)) M v.keepR2 outp) := by
  rw [hpc, hret] at hj
  refine Triple.seq hj (Triple.dimap (fun c h => h.reshape (L' := [(1, ret), (10, x), (11, y)])
      (K' := v.keepR2 ++ [(2, BitVec.ofNat 64 (sp - 48)), (8, BitVec.ofNat 64 b), (9, BitVec.ofNat 64 rp), (18, s2)])
      (by simp [callR]) (by simp [callR, Abi.keepR2]))
    (fun c h => h.reshape (by simp [backL, Abi.keepR2]) (by simp [Abi.keepR2]))
    (Fn.Libgcc.Muldi3.correctK himg hra (by
      unfold KeepOK; simp only [Abi.keepR2, List.cons_append, List.nil_append, keysG]; decide)))

/-- `jal __muldi3` at `pc` (a `jal_at` instance). -/
macro "mul_jal" pc:term:max w:term:max imm:term:max hc:term:max : term => `(
  jal_at (pc := $pc) (w := $w) (imm := $imm) (CodeAt.word $hc (a := ($pc : BitVec 64).toNat) (by decide)) (by decide)
    (by decide) (fun s h1 h2 h3 => decodeW s h1 h2 h3) ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩
    (by decide) (by simp [callR, mulL, mul1L, mul2L, xx1, xx2]) (by simp [keysG, callR]) (by simp [Abi.keepR2, keysG]))

theorem and_one (b : Nat) : (BitVec.ofNat 64 b &&& 1#64 == 0#64) = decide (b % 2 = 0) := by
  have : (BitVec.ofNat 64 b &&& 1#64) = BitVec.ofNat 64 (b % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, show 1 % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod]
    omega
  rw [this]
  by_cases h : b % 2 = 0
  · simp [h]
  · have : b % 2 = 1 := by omega
    simp [this]


section
variable {m : Mem} {v : Abi} {outp : Array String} {sp p dp rp : Nat} {n : MpInt} {ra : BitVec 64}

local notation "ρ" => Api.MpMontSetup.lay sp p dp rp n

theorem sfacts (hP : Api.MpMontSetup.Pre m v sp p dp rp n ra) : SFacts sp :=
  have hsc := hP.lay.disj (r := R.stk) (s := R.code)
  have hrs := hP.rs
  { rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
    code_off := by
      simp only [Iv.Disj, Disj, Api.MpMontSetup.lay, textIv, textBase, textLen] at hsc
      have := hrs.lo_ge; unfold mpMontgomerySetupBase; omega }

/-- A store to the `x` slot: in the stack region. -/
theorem xslot (hP : Api.MpMontSetup.Pre m v sp p dp rp n ra) (X : Mem) (y : BitVec 64) :
    Frm ρ [R.stk] X (writeLog X [(sp - 40, 8, y)]) := by
  have := hP.sp_ge
  exact Frm.store ⟨by simp only [Iv.Sub, Api.MpMontSetup.lay]; omega, trivial⟩

/-- The second and third steps' two products, from the store of `x` to the next product (`5c34` → `5c50`). -/
theorem mid1 (hP : Api.MpMontSetup.Pre m v sp p dp rp n ra) {X : Mem} (b : Nat) (himg : Img X) :
    Triple (At 0x80005c34#64 (backL sp b rp 2#64 (zz1 b)) X v.keepR2 outp)
      (At 0x80005c50#64 (backL sp b rp 2#64 (zz2 b)) (writeLog (writeLog X [(sp - 40, 8, xx1 b)]) []) v.keepR2 outp) := by
  have hs := sfacts hP
  have hsge := hP.sp_ge
  have hF := xslot hP X (xx1 b)
  have himg2 := hF.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) himg
  have hx : bytesT8 (writeLog X [(sp - 40, 8, xx1 b)]) (sp - 48 + 8) = xx1 b := by
    rw [show sp - 48 + 8 = sp - 40 by omega]; exact bytesT8_sd_self _ _ _
  refine Triple.seq (b1_step v outp sp b rp (zz1 b) X himg.mpMontgomerySetup hs) ?_
  refine Triple.seq (mul_from_jal (ret := 0x80005c44#64) (sp := sp) (b := b) (rp := rp) (s2 := 2#64) (x := BitVec.ofNat 64 b) (y := xx1 b)
      himg2 (mul_jal 0x80005c40#64 0x101110ef#32 0x11900#21 himg2.mpMontgomerySetup) (by decide) (by decide)
      (by decide)) ?_
  refine Triple.seq (a2_step v outp sp b rp _ (xx1 b) _ himg2.mpMontgomerySetup hs hx) ?_
  exact mul_from_jal (ret := 0x80005c50#64) (sp := sp) (b := b) (rp := rp) (s2 := 2#64) (x := sub2 (BitVec.ofNat 64 b * xx1 b))
    (y := xx1 b) himg2 (mul_jal 0x80005c4c#64 0x0f5110ef#32 0x118f4#21 himg2.mpMontgomerySetup) (by decide)
    (by decide) (by decide)

theorem mid2 (hP : Api.MpMontSetup.Pre m v sp p dp rp n ra) {X : Mem} (b : Nat) (himg : Img X) :
    Triple (At 0x80005c50#64 (backL sp b rp 2#64 (zz2 b)) X v.keepR2 outp)
      (At 0x80005c6c#64 (backL sp b rp 2#64 (zz3 b)) (writeLog (writeLog X [(sp - 40, 8, xx2 b)]) []) v.keepR2 outp) := by
  have hs := sfacts hP
  have hsge := hP.sp_ge
  have hF := xslot hP X (xx2 b)
  have himg2 := hF.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) himg
  have hx : bytesT8 (writeLog X [(sp - 40, 8, xx2 b)]) (sp - 48 + 8) = xx2 b := by
    rw [show sp - 48 + 8 = sp - 40 by omega]; exact bytesT8_sd_self _ _ _
  refine Triple.seq (b2_step v outp sp b rp (zz2 b) X himg.mpMontgomerySetup hs) ?_
  refine Triple.seq (mul_from_jal (ret := 0x80005c60#64) (sp := sp) (b := b) (rp := rp) (s2 := 2#64) (x := BitVec.ofNat 64 b) (y := xx2 b)
      himg2 (mul_jal 0x80005c5c#64 0x0e5110ef#32 0x118e4#21 himg2.mpMontgomerySetup) (by decide) (by decide)
      (by decide)) ?_
  refine Triple.seq (a3_step v outp sp b rp _ (xx2 b) _ himg2.mpMontgomerySetup hs hx) ?_
  exact mul_from_jal (ret := 0x80005c6c#64) (sp := sp) (b := b) (rp := rp) (s2 := 2#64) (x := sub2 (BitVec.ofNat 64 b * xx2 b))
    (y := xx2 b) himg2 (mul_jal 0x80005c68#64 0x0d9110ef#32 0x118d8#21 himg2.mpMontgomerySetup) (by decide)
    (by decide) (by decide)

/-- The prologue and the first step's two products (entry → `5c34`). -/
theorem head (hP : Api.MpMontSetup.Pre m v sp p dp rp n ra) {b : Nat} (hlf : LFacts m p dp b)
    (hd : dp + 4 ≤ sp - 48 ∨ sp ≤ dp) (ho : (BitVec.ofNat 64 b &&& 1#64 == 0#64) = false) :
    Triple (At entry (entryL ra v.s0 v.s.s1 v.s.s2 sp p rp) m v.keepR2 outp)
      (At 0x80005c34#64 (backL sp b rp 2#64 (zz1 b)) (writeLog (writeLog m (proLog ra v.s0 v.s.s1 v.s.s2 sp b)) [])
        v.keepR2 outp) := by
  have hs := sfacts hP
  have hsge := hP.sp_ge
  have hF1 : Frm ρ [R.stk] m (writeLog m (proLog ra v.s0 v.s.s1 v.s.s2 sp b)) := Frm.store (by
    simp only [LogIn, proLog, evenLog, proLog2, List.cons_append, List.nil_append, Iv.Sub, Api.MpMontSetup.lay,
      and_true]; omega)
  have himg1 := hF1.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
  refine Triple.seq (pro_step ra v.s0 v.s.s1 v.s.s2 v outp sp p dp b rp m hP.img.mpMontgomerySetup hs hlf hd ho) ?_
  refine Triple.seq (mul_from_jal (ret := 0x80005c24#64) (sp := sp) (b := b) (rp := rp) (s2 := v.s.s2)
      (x := BitVec.ofNat 64 b) (y := x0v b)
      himg1 (mul_jal 0x80005c20#64 0x121110ef#32 0x11920#21 himg1.mpMontgomerySetup) (by decide) (by decide)
      (by decide)) ?_
  have hx0 : bytesT8 (writeLog m (proLog ra v.s0 v.s.s1 v.s.s2 sp b)) (sp - 48 + 8) = x0v b := by
    rw [show sp - 48 + 8 = sp - 40 by omega]
    exact bytesT8_log _ _ 4 (sp - 40) (x0v b) rfl trivial
  have himg1' : Img (writeLog (writeLog m (proLog ra v.s0 v.s.s1 v.s.s2 sp b)) []) := by
    rw [writeLog_nil]; exact himg1
  refine Triple.seq (a1_step v outp sp b rp v.s.s2 _ (x0v b) _ himg1.mpMontgomerySetup hs hx0) ?_
  exact mul_from_jal (ret := 0x80005c34#64) (sp := sp) (b := b) (rp := rp) (s2 := 2#64) (x := sub2 (BitVec.ofNat 64 b * x0v b))
    (y := x0v b) himg1' (mul_jal 0x80005c30#64 0x111110ef#32 0x11910#21 himg1'.mpMontgomerySetup) (by decide)
    (by decide) (by decide)

/-- `*rho` and the epilogue (`5c6c` → return), the saved registers and frame given. -/
theorem tail (hP : Api.MpMontSetup.Pre m v sp p dp rp n ra) {b : Nat} (hb : n.digit 0 = b) (hb28 : b < 2 ^ 28)
    (hodd : ¬ n.digit 0 % 2 = 0) {Y : Mem} (himg : Img Y) (hF : Frm ρ [R.stk] m Y)
    (h16 : bytesT8 Y (sp - 48 + 16) = v.s.s2) (h24 : bytesT8 Y (sp - 48 + 24) = v.s.s1)
    (h40 : bytesT8 Y (sp - 48 + 40) = ra) (h32 : bytesT8 Y (sp - 48 + 32) = v.s0) :
    Triple (At 0x80005c6c#64 (backL sp b rp 2#64 (zz3 b)) Y v.keepR2 outp)
      (Api.MpMontSetup.Ret m v outp sp p dp rp n ra) := by
  have hs := sfacts hP
  have hsge := hP.sp_ge; have hsv := hP.sp_v
  have hrr := hP.rr
  have hsr := hP.lay.disj (r := R.stk) (s := R.rho)
  have hrc := hP.lay.disj (r := R.rho) (s := R.code)
  simp only [Iv.Disj, Disj, Api.MpMontSetup.lay, textIv, textBase, textLen] at hsr hrc
  have hrc' : rp + 4 ≤ mpMontgomerySetupBase ∨ mpMontgomerySetupBase + 192 ≤ rp := by
    unfold mpMontgomerySetupBase; omega
  have hF4 : Frm ρ [R.rho] Y (writeLog Y [(rp, 4, rhov (zz3 b))]) := Frm.store ⟨Iv.sub_self _, trivial⟩
  have himg4 := hF4.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) himg
  have back : ∀ a, sp - 32 ≤ a → a + 8 ≤ sp → bytesT8 (writeLog Y [(rp, 4, rhov (zz3 b))]) a = bytesT8 Y a :=
    fun a h1 h2 => bytesT8_past _ _ _ _ _ (by omega)
  have hpost : Api.MpMontSetup.Post m sp p dp rp n Layout.mpOkay (setupRho (n.digit 0))
      (writeLog Y [(rp, 4, rhov (zz3 b))]) :=
    { rho_v := by rw [rho_read, hb, rho_zz b hb28]
      setup := ⟨fun h => absurd h hodd, fun _ => ⟨rfl, rfl⟩⟩
      frame := (hF.trans hF4).mono }
  have hok : BitVec.ofInt 64 Layout.mpOkay = 0#64 := by decide
  refine Triple.seq (e1_step v outp sp b rp (zz3 b) Y himg.mpMontgomerySetup hrr hP.r_al hrc') ?_
  exact Triple.rmap (fun c hA => by
      rw [writeLog_nil] at hA
      exact ⟨Layout.mpOkay, _, _, hA.reshape (by simp [retL, hok])
        (by simp [retL, Abi.keep, Abi.keepR2, sKeepL, hsv]), hpost⟩)
    (e2_step ra v.s0 v.s.s1 v.s.s2 v outp sp b rp _ himg4.mpMontgomerySetup hP.ra_al hs
      (by rw [back _ (by omega) (by omega)]; exact h16) (by rw [back _ (by omega) (by omega)]; exact h24)
      (by rw [back _ (by omega) (by omega)]; exact h40) (by rw [back _ (by omega) (by omega)]; exact h32))

end

/-- The odd case. -/
theorem odd_run {m : Mem} {v : Abi} {outp : Array String} {sp p dp rp : Nat} {n : MpInt} {ra : BitVec 64}
    (hP : Api.MpMontSetup.Pre m v sp p dp rp n ra) (hlf : LFacts m p dp (n.digit 0))
    (hd : dp + 4 ≤ sp - 48 ∨ sp ≤ dp) (ho : (BitVec.ofNat 64 (n.digit 0) &&& 1#64 == 0#64) = false)
    (hev : ¬ n.digit 0 % 2 = 0) (hb28 : n.digit 0 < 2 ^ 28) :
    Triple (At entry (entryL ra v.s0 v.s.s1 v.s.s2 sp p rp) m v.keepR2 outp)
      (Api.MpMontSetup.Ret m v outp sp p dp rp n ra) := by
  have hl := hP.lay
  have hsge := hP.sp_ge
  have hF0 : ∀ (log : List WEntry), LogIn (Api.MpMontSetup.lay sp p dp rp n) R.stk log →
      Frm (Api.MpMontSetup.lay sp p dp rp n) [R.stk] m (writeLog m log) := fun log h => Frm.store h
  have hT := head (outp := outp) hP hlf hd ho
  have hF1 : Frm (Api.MpMontSetup.lay sp p dp rp n) [R.stk] m (writeLog m (proLog ra v.s0 v.s.s1 v.s.s2 sp (n.digit 0))) :=
    hF0 _ (by simp only [LogIn, proLog, evenLog, proLog2, List.cons_append, List.nil_append, Iv.Sub,
      Api.MpMontSetup.lay, and_true]; omega)
  have himg1 := hF1.keep hl (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
  have g16 : bytesT8 (writeLog m (proLog ra v.s0 v.s.s1 v.s.s2 sp (n.digit 0))) (sp - 32) = v.s.s2 :=
    bytesT8_log _ _ 3 (sp - 32) v.s.s2 rfl ⟨.inr (by simp only; omega), trivial⟩
  have g24 : bytesT8 (writeLog m (proLog ra v.s0 v.s.s1 v.s.s2 sp (n.digit 0))) (sp - 24) = v.s.s1 :=
    bytesT8_log _ _ 2 (sp - 24) v.s.s1 rfl ⟨.inr (by simp only; omega), .inr (by simp only; omega), trivial⟩
  have g40 : bytesT8 (writeLog m (proLog ra v.s0 v.s.s1 v.s.s2 sp (n.digit 0))) (sp - 8) = ra :=
    bytesT8_log _ _ 1 (sp - 8) ra rfl ⟨.inr (by simp only; omega), .inr (by simp only; omega), .inr (by simp only; omega), trivial⟩
  have g32 : bytesT8 (writeLog m (proLog ra v.s0 v.s.s1 v.s.s2 sp (n.digit 0))) (sp - 16) = v.s0 :=
    bytesT8_log _ _ 0 (sp - 16) v.s0 rfl ⟨.inl (by simp only; omega), .inr (by simp only; omega), .inr (by simp only; omega),
      .inr (by simp only; omega), trivial⟩
  generalize writeLog m (proLog ra v.s0 v.s.s1 v.s.s2 sp (n.digit 0)) = M0 at hT hF1 himg1 g16 g24 g40 g32
  have hFa := xslot hP (writeLog M0 []) (xx1 (n.digit 0))
  have hFb := xslot hP (writeLog (writeLog (writeLog M0 []) [(sp - 40, 8, xx1 (n.digit 0))]) []) (xx2 (n.digit 0))
  have himga := hFa.keep hl (Img.reads (r := R.code) (Iv.sub_self _)) himg1
  have himgb := hFb.keep hl (Img.reads (r := R.code) (Iv.sub_self _)) himga
  have back : ∀ a, sp - 32 ≤ a → a + 8 ≤ sp →
      bytesT8 (writeLog (writeLog (writeLog (writeLog (writeLog M0 []) [(sp - 40, 8, xx1 (n.digit 0))]) [])
        [(sp - 40, 8, xx2 (n.digit 0))]) []) a = bytesT8 M0 a := fun a h1 h2 => by
    rw [writeLog_nil, bytesT8_past _ _ _ _ _ (by omega), writeLog_nil, bytesT8_past _ _ _ _ _ (by omega),
      writeLog_nil]
  have himg1' : Img (writeLog M0 []) := by rw [writeLog_nil]; exact himg1
  have himga' : Img (writeLog (writeLog (writeLog M0 []) [(sp - 40, 8, xx1 (n.digit 0))]) []) := by
    rw [writeLog_nil]; exact himga
  have himgb' : Img (writeLog (writeLog (writeLog (writeLog (writeLog M0 []) [(sp - 40, 8, xx1 (n.digit 0))]) [])
      [(sp - 40, 8, xx2 (n.digit 0))]) []) := by rw [writeLog_nil]; exact himgb
  have hFall : Frm (Api.MpMontSetup.lay sp p dp rp n) [R.stk] m
      (writeLog (writeLog (writeLog (writeLog (writeLog M0 []) [(sp - 40, 8, xx1 (n.digit 0))]) [])
        [(sp - 40, 8, xx2 (n.digit 0))]) []) := by
    rw [writeLog_nil]; exact (hF1.trans (hFa.trans hFb)).mono
  exact Triple.seq hT (Triple.seq (mid1 hP _ himg1') (Triple.seq (mid2 hP _ himga')
    (tail hP rfl hb28 hev himgb' hFall
      (by rw [back _ (by omega) (by omega), show sp - 48 + 16 = sp - 32 by omega]; exact g16)
      (by rw [back _ (by omega) (by omega), show sp - 48 + 24 = sp - 24 by omega]; exact g24)
      (by rw [back _ (by omega) (by omega), show sp - 48 + 40 = sp - 8 by omega]; exact g40)
      (by rw [back _ (by omega) (by omega), show sp - 48 + 32 = sp - 16 by omega]; exact g32))))

/-- **`mp_montgomery_setup` on the machine.** -/
theorem correct : Api.MpMontSetup.Statement := by
  intro m v outp sp p dp rp n ra hP
  have hl := hP.lay
  have hrs := hP.rs
  have eT : textBase = 0x80000000 := rfl
  have hsc := hl.disj (r := R.stk) (s := R.code)
  have hst := hl.disj (r := R.stk) (s := R.nD)
  have hsr := hl.disj (r := R.stk) (s := R.rho)
  have hrc := hl.disj (r := R.rho) (s := R.code)
  simp only [Iv.Disj, Disj, Api.MpMontSetup.lay, textIv, textBase, textLen] at hsc hst hsr hrc
  have ha := hP.apos
  have hs : SFacts sp :=
    { rs := hP.rs, sp_al := hP.sp_al, sp_ge := hP.sp_ge
      code_off := by have := hrs.lo_ge; unfold mpMontgomerySetupBase; omega }
  have hb28 : n.digit 0 < 2 ^ 28 := hP.shape.digit_lt 0
  have hlf : LFacts m p dp (n.digit 0) :=
    { rp := by simpa [Layout.sizeofMpInt] using hP.gn.st
      rd := by have := hP.gn.ds; simp only [Layout.sizeofDigit] at this; exact ⟨this.lo_ge, by have := this.hi_le; omega,
        by have := this.off; omega⟩
      dpv := by simpa [Layout.offDp] using hP.repr.dpv
      bv := by
        have := hP.repr.digits 0 ha
        simp only [Layout.sizeofDigit, Nat.mul_zero, Nat.add_zero] at this
        rw [this, signExtend_ofNat32 _ (by omega)]
      b28 := hb28 }
  have hd : dp + 4 ≤ sp - 48 ∨ sp ≤ dp := by omega
  have hc := hP.img.mpMontgomerySetup
  have hsv := hP.sp_v
  have hra := hP.ra_al
  have hsge := hP.sp_ge
  have hrr := hP.rr
  refine Triple.lmap (fun c h => h.reshape (L' := entryL ra v.s0 v.s.s1 v.s.s2 sp p rp) (K' := v.keepR2)
      (by simp [entryL, Api.MpMontSetup.entryL, Abi.keep, sKeepL, hsv])
      (by simp [Abi.keep, Abi.keepR2, sKeepL])) ?_
  have hF0 : ∀ (log : List WEntry), LogIn (Api.MpMontSetup.lay sp p dp rp n) R.stk log →
      Frm (Api.MpMontSetup.lay sp p dp rp n) [R.stk] m (writeLog m log) := fun log h => Frm.store h
  by_cases hev : n.digit 0 % 2 = 0
  · -- even: `MP_VAL`
    have he : (BitVec.ofNat 64 (n.digit 0) &&& 1#64 == 0#64) = true := by rw [and_one]; simp [hev]
    have hF := hF0 (evenLog ra v.s0 sp) (by simp only [LogIn, evenLog, Iv.Sub, Api.MpMontSetup.lay, and_true]; omega)
    have h40 : bytesT8 (writeLog m (evenLog ra v.s0 sp)) (sp - 48 + 40) = ra := by
      rw [show sp - 48 + 40 = sp - 8 by omega]; exact bytesT8_log _ _ 1 _ _ rfl (by simp [evenLog, OutLRange])
    have h32 : bytesT8 (writeLog m (evenLog ra v.s0 sp)) (sp - 48 + 32) = v.s0 := by
      rw [show sp - 48 + 32 = sp - 16 by omega]; exact bytesT8_log _ _ 0 _ _ rfl (by simp [evenLog, OutLRange]; omega)
    have himg1 := hF.keep hl (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
    have hrho := hF.keep hl (Reads.w4 (r := R.rho) (a := rp) (v := bytesT4 m rp) (Iv.sub_self _)) rfl
    have hval : BitVec.ofInt 64 Layout.mpVal = 0xfffffffffffffffd#64 := by decide
    exact Triple.seq (even_step ra v.s0 v.s.s1 v.s.s2 v outp sp p dp _ rp m hc hs hlf hd he)
      (Triple.rmap (fun c hA => by
          rw [writeLog_nil] at hA
          have hpost : Api.MpMontSetup.Post m sp p dp rp n Layout.mpVal (bytesT4 m rp).toNat
              (writeLog m (evenLog ra v.s0 sp)) :=
            { rho_v := by rw [hrho]; simp
              setup := ⟨fun _ => rfl, fun h => absurd h (by omega)⟩
              frame := hF.mono }
          exact ⟨Layout.mpVal, _, _, hA.reshape (by simp [retL, hval])
            (by simp [retL, Abi.keep, Abi.keepR2, sKeepL, hsv]), hpost⟩)
        (even_ret ra v.s0 v.s.s1 v.s.s2 v outp sp _ himg1.mpMontgomerySetup hra hs h40 h32))
  -- odd
  have ho : (BitVec.ofNat 64 (n.digit 0) &&& 1#64 == 0#64) = false := by rw [and_one]; simp [hev]
  exact odd_run hP hlf hd ho hev hb28

end Tom.Machine.Fn.MpMontSetup
