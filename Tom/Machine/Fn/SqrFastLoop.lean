import Tom.Machine.Fn.SqrFast
import Tom.Machine.Fn.MulFastLoop

/-!
# `s_mp_sqr_fast` on the machine: the column loop, for any placement

The column head `70a8` holds `combaW (colS …) ix + 2 hp ix` (`hp`: the half
column, `combaPart … (combaIyS …)`, `Tom/Spec/Mul.lean`); `storeCol` adds the
square of `a[ix/2]` in even columns (`__muldi3`) and stores `W[ix]`;
`nextCol` sets up the next column, runs its half-column inner loop (`inner`,
a `__muldi3` call between two segments per term, `Kit/MulCall.lean`) and
doubles it into the carry; `loop` runs the columns over the array state on
`W` (`MulFast.WSt`). What the loop reads is supplied as plain facts (`SColH`).
-/

namespace Tom.Machine.Fn.SqrFast

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api.Libgcc
open Tom.Machine.Fn.MulFast (kF kFKeys DRead pS WSt ρW prod_lt')

/-- The half column of column `k`. -/
abbrev hp (da : Nat → Nat) (ua k : Nat) : Nat := pS da da (combaTx ua k) (combaTy ua k) (combaIyS ua k)

/-! ## The inner loop -/

section inner
variable {M : Mem} {v : Abi} {outp : Array String} {sp ua adp ix c tx ty iy : Nat} {da : Nat → Nat}

structure InH (M : Mem) (adp tx ty iy : Nat) (da : Nat → Nat) : Prop where
  rdA : ∀ iz, iz < iy → DRead M (adp + 4 * tx + 4 * iz) (da (tx + iz))
  rdB : ∀ iz, iz < iy → DRead M (adp + 4 * ty - 4 * iz) (da (ty - iz))
  hty : iy ≤ ty + 1
  bnd : pS da da tx ty iy < 2 ^ 64
  ha : adp + 4 * tx + 4 * iy ≤ 2 ^ 32
  hb : 4 ≤ adp
  img : Img M

theorem inner (h : InH M adp tx ty iy da) (hiy : 1 ≤ iy) :
    ∀ iz, iz < iy → Triple (At 0x80007120#64 (iH sp ua adp ix c tx ty iy iz (pS da da tx ty iz)) M (kF v) outp)
      (At 0x8000713c#64 (iH sp ua adp ix c tx ty iy iy (pS da da tx ty iy)) M (kF v) outp) := by
  have hc := h.img.sMpSqrFast
  have hty := h.hty; have hb := h.hb
  have hmono : ∀ n, n ≤ iy → pS da da tx ty n < 2 ^ 64 := fun n hn =>
    Nat.lt_of_le_of_lt (sumTo_mono _ hn) h.bnd
  have body : ∀ iz, iz < iy → ∀ (pc' : BitVec 64) (L' : GRegs),
      (Triple (At 0x80007134#64 (rI sp ua adp ix c tx ty iy iz (pS da da tx ty iz)
          (da (tx + iz) * da (ty - iz))) M (kF v) outp) (At pc' L' (writeLog M []) (kF v) outp)) →
      Triple (At 0x80007120#64 (iH sp ua adp ix c tx ty iy iz (pS da da tx ty iz)) M (kF v) outp)
        (At pc' L' M (kF v) outp) := by
    intro iz hiz pc' L' hlast
    have hx := h.rdA iz hiz; have hy := h.rdB iz hiz
    refine Triple.seq (l1_step v outp sp ua adp ix c tx ty iy iz _ _ _ M hc hx hy (by omega)) ?_
    refine Triple.seq (muldi3_call (pc := 0x80007130#64) (w := 0x410100ef#32) (imm := 0x010410#21)
      (Lk := kI sp ua adp ix c tx ty iy iz (pS da da tx ty iz))
      (L2 := rI sp ua adp ix c tx ty iy iz (pS da da tx ty iz) (da (tx + iz) * da (ty - iz)))
      h.img hc (by decide +kernel) (by decide) (by decide) (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide) (by decide)
      (fun p hp => hp) (by simp [kI, keysG]) (by simp [kF, keysG])
      (by unfold KeepOK
          rw [show keysG (kI sp ua adp ix c tx ty iy iz (pS da da tx ty iz) ++ kF v) =
            [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 3, 4] from rfl]; decide)
      (fun p hp => List.mem_cons_of_mem _ (by rw [ofNat_mul_ofNat]; exact hp))) ?_
    exact Triple.rmap (fun _ h => h) hlast
  refine Triple.countup (n := iy)
    (P := fun iz => At 0x80007120#64 (iH sp ua adp ix c tx ty iy iz (pS da da tx ty iz)) M (kF v) outp)
    (fun iz hi => body iz (by omega) _ _ ?_) ?_
  · have := l2_step v outp sp ua adp ix c tx ty iy iz (pS da da tx ty iz)
      (da (tx + iz) * da (ty - iz)) M hc (by have := hmono (iz + 1) (by omega); simp only [pS, sumTo] at this ⊢; omega)
      hi h.ha
    simp only [pS, sumTo] at this ⊢
    exact this
  · refine body (iy - 1) (by omega) _ _ ?_
    have := l2e_step v outp sp ua adp ix c tx ty iy (iy - 1) (pS da da tx ty (iy - 1))
      (da (tx + (iy - 1)) * da (ty - (iy - 1))) M hc
      (by have := hmono iy (Nat.le_refl _); rw [show iy = iy - 1 + 1 by omega] at this
          simp only [pS, sumTo] at this ⊢; omega) (by omega)
    have e : pS da da tx ty (iy - 1) + da (tx + (iy - 1)) * da (ty - (iy - 1)) = pS da da tx ty iy := by
      conv => rhs; rw [show iy = iy - 1 + 1 by omega]
      simp only [pS, sumTo]
    rwa [e] at this

end inner

/-! ## A column -/

section column
variable {M : Mem} {v : Abi} {outp : Array String} {sp ua adp : Nat} {da : Nat → Nat}

/-- What a column reads (memory `M`, unchanged by the column up to its store). -/
structure SColH (M : Mem) (sp ua adp : Nat) (da : Nat → Nat) : Prop where
  k : KS sp
  img : Img M
  rdA : ∀ i, i < ua → DRead M (adp + 4 * i) (da i)
  ua0 : bytesT8 M (sp - 2208) = BitVec.ofNat 64 ua
  ua1 : bytesT8 M (sp - 2200) = BitVec.ofNat 64 (ua - 1)
  ua24 : bytesT8 M (sp - 2184) = BitVec.ofNat 64 ua
  ua32 : bytesT8 M (sp - 2176) = BitVec.ofNat 64 (4 * (ua - 1))
  ua_pos : 1 ≤ ua
  ua_lt : ua < 256
  ha : adp + 4 * ua ≤ 2 ^ 32
  hb4 : 4 ≤ adp

/-- The next column's half column, `iy > 0`: the set-up at `7114` to the head. -/
theorem run_inner (h : SColH M sp ua adp da) (ix c tx ty iy : Nat) (j9 : BitVec 64)
    (htx : tx + iy ≤ ua) (hty : iy ≤ ty + 1) (hua : ty < ua) (hiy : 1 ≤ iy) (hix : ix < 2 * ua)
    (hw : c + 2 * pS da da tx ty iy < 2 ^ 64) :
    Triple (At 0x80007114#64 (iS sp ua adp ix c tx ty iy j9) M (kF v) outp)
      (fun cf => ∃ j0 j9 j10 j11 : BitVec 64,
        At 0x800070a8#64 (qH sp ua adp ix (c + 2 * pS da da tx ty iy) j0 j9 j10 j11) M (kF v) outp cf) := by
  have hl := h.ua_lt; have hb4 := h.hb4; have hha := h.ha
  have hin : InH M adp tx ty iy da :=
    { rdA := fun iz hiz => (h.rdA (tx + iz) (by omega)).cast (by omega)
      rdB := fun iz hiz => (h.rdA (ty - iz) (by omega)).cast (by omega)
      hty := hty, bnd := by omega, ha := by omega, hb := hb4, img := h.img }
  refine Triple.seq (i0_step v outp sp ua adp ix c tx ty iy j9 M h.img.sMpSqrFast (by omega)) ?_
  refine Triple.seq (inner (sp := sp) (ua := ua) (ix := ix) (c := c) (v := v) (outp := outp) hin hiy 0 (by omega)) ?_
  exact Triple.rmap (fun cf h => ⟨_, _, _, _, h⟩) (x_step v outp sp ua adp ix c tx ty iy _ M h.img.sMpSqrFast hw)

/-- The next column's set-up, from the store point of column `ix` (carry `s / 2^28`). -/
theorem nextCol (h : SColH M sp ua adp da) (ix s : Nat) (hix : ix + 1 < 2 * ua) (hs : s < 2 ^ 64)
    (hw : s / 268435456 + 2 * hp da ua (ix + 1) < 2 ^ 64) (j0 j9 j10 j11 : BitVec 64) :
    Triple (At 0x800070dc#64 (sP sp ua adp ix s j0 j9 j10 j11) M (kF v) outp)
      (fun cf => ∃ j0 j9 j10 j11 : BitVec 64,
        At 0x800070a8#64 (qH sp ua adp (ix + 1) (s / 268435456 + 2 * hp da ua (ix + 1)) j0 j9 j10 j11) M (kF v) outp cf) := by
  have hl := h.ua_lt; have hu1 := h.ua_pos
  have hc := h.img.sMpSqrFast
  by_cases hlt : ix + 1 < ua
  · have htx : combaTx ua (ix + 1) = 0 := by unfold combaTx combaTy; omega
    have hty : combaTy ua (ix + 1) = ix + 1 := by unfold combaTy; omega
    have hiy : combaIyS ua (ix + 1) = ix / 2 + 1 := by
      unfold combaIyS combaIy; rw [htx, hty]; omega
    simp only [hp, htx, hty, hiy] at hw ⊢
    exact Triple.seq (n1_step v outp sp ua adp ix s j0 j9 j10 j11 M hc h.k h.ua0 hlt (by omega) hs)
      (Triple.rmap (fun _ h => h) (run_inner h (ix + 1) _ 0 (ix + 1) (ix / 2 + 1) j9 (by omega) (by omega)
        (by omega) (by omega) (by omega) hw))
  · have htx : combaTx ua (ix + 1) = ix + 2 - ua := by unfold combaTx combaTy; omega
    have hty : combaTy ua (ix + 1) = ua - 1 := by unfold combaTy; omega
    have hiy : combaIyS ua (ix + 1) = (2 * ua - 1 - (ix + 1)) / 2 := by
      unfold combaIyS combaIy; rw [htx, hty]; omega
    simp only [hp, htx, hty, hiy] at hw ⊢
    refine Triple.seq (n2_step v outp sp ua adp ix s j0 j9 j10 j11 M hc h.k h.ua0 (by omega) hix (by omega) hs) ?_
    have hms : ∀ a4, (2 * ua - 1 - (ix + 1)) / 2 ≤ a4 → a4 < 2 ^ 31 →
        Triple (At 0x800071b8#64 ((14, BitVec.ofNat 64 a4) :: mL sp ua adp (ix + 1) (s / 268435456) j0 j9 j10 j11)
          (writeLog M []) (kF v) outp)
        (fun cf => ∃ j0 j9 j10 j11 : BitVec 64, At 0x800070a8#64 (qH sp ua adp (ix + 1)
          (s / 268435456 + 2 * pS da da (ix + 2 - ua) (ua - 1) ((2 * ua - 1 - (ix + 1)) / 2)) j0 j9 j10 j11) M
          (kF v) outp cf) := by
      intro a4 h4 h4'
      refine Triple.seq (ms_step v outp sp ua adp (ix + 1) _ a4 j0 j9 j10 j11 _ hc (by omega) hix) ?_
      refine Triple.seq (m3_step v outp sp ua adp (ix + 1) _ a4 _ j9 j10 j11 _ hc h4 (by omega) h4') ?_
      by_cases hz : (2 * ua - 1 - (ix + 1)) / 2 = 0
      · rw [hz]
        have e0 : s / 268435456 + 2 * pS da da (ix + 2 - ua) (ua - 1) 0 = s / 268435456 := by simp [pS, sumTo]
        rw [e0]
        have h5 := m5_step v outp sp ua adp (ix + 1) (s / 268435456) j9 j10 j11
          (writeLog (writeLog (writeLog M []) []) []) hc (by omega)
        exact Triple.rmap (fun cf h => ⟨_, _, _, _, h⟩) h5
      · refine Triple.seq (m6_step v outp sp ua adp (ix + 1) _ _ j9 j10 j11 _ hc h.k h.ua24 h.ua32 (by omega)
          (by omega) (by omega) hix (by omega)) ?_
        exact Triple.rmap (fun _ h => h) (run_inner h (ix + 1) _ (ix + 1 + 1 - ua) (ua - 1) _ j9 (by omega)
          (by omega) (by omega) (by omega) hix (by rwa [show ix + 1 + 1 - ua = ix + 2 - ua by omega]))
    by_cases h1 : ua - 1 < 2 * ua - 1 - (ix + 1)
    · exact Triple.seq (m1_step v outp sp ua adp (ix + 1) _ j0 j9 j10 j11 _ hc h.k h.ua1 h1 hu1 (by omega) hix)
        (Triple.rmap (fun _ h => h) (hms ua (by omega) (by omega)))
    · exact Triple.seq (m2_step v outp sp ua adp (ix + 1) _ j0 j9 j10 j11 _ hc h.k h.ua1 (by omega) hu1 (by omega)
        hix) (Triple.rmap (fun _ h => h) (hms _ (by omega) (by omega)))

end column

/-! ## The column loop -/

section loop
variable {m0 : Mem} {v : Abi} {outp : Array String} {sp ua adp : Nat} {da old : Nat → Nat}

/-- What the column loop needs, for every array state on `W`. -/
structure SLoopH (m0 : Mem) (sp ua adp : Nat) (da : Nat → Nat) : Prop where
  ch : ∀ M f, ArrFrm (ρW sp) () m0 M (sp - 2160) 512 f → SColH M sp ua adp da
  bnd : ∀ k, combaW (colS da ua) k + colS da ua k < 2 ^ 64
  pa_w : 2 * ua ≤ 512
  dlt : ∀ i, da i < radix

theorem colS_split (da : Nat → Nat) (ua k : Nat) :
    colS da ua k = 2 * hp da ua k + (if k % 2 = 0 then da (k / 2) * da (k / 2) else 0) := rfl

/-- Column `ix` up to its store: the square in even columns, then `W[ix]`. -/
theorem storeCol (h : SLoopH m0 sp ua adp da) (ix : Nat) (hix : ix < 2 * ua) (j0 j9 j10 j11 : BitVec 64) :
    Triple (WSt m0 v outp sp 0x800070a8#64
        (qH sp ua adp ix (combaW (colS da ua) ix + 2 * hp da ua ix) j0 j9 j10 j11) (ovl (combaD (colS da ua)) old ix))
      (WSt m0 v outp sp 0x800070dc#64
        (sP sp ua adp ix (combaW (colS da ua) ix + colS da ua ix) j0 j9 j10 j11)
        (ovl (combaD (colS da ua)) old (ix + 1))) := by
  intro cf ⟨M, hA, hat⟩
  have hC := h.ch M _ hA
  have hw := h.bnd ix
  have hpw := h.pa_w; have hl := hC.ua_lt
  have hA1 := hA.step (i := ix) (v := (combaW (colS da ua) ix + colS da ua ix) % 268435456)
    (by omega) (by omega) (MulFast.combaD_eq _ _)
  have hc := hC.img.sMpSqrFast
  refine Triple.rmap (fun cf h => ⟨_, hA1, h⟩) ?_ cf hat
  rw [colS_split] at hw ⊢
  by_cases he : ix % 2 = 0
  · simp only [he, if_true] at hw ⊢
    have hd := hC.rdA (ix / 2) (by omega)
    refine Triple.seq (e1_step v outp sp ua adp ix _ j0 j9 j10 j11 M hc he (by omega)) ?_
    refine Triple.seq (e2_step v outp sp ua adp ix _ j0 j9 j10 j11 _ hc) ?_
    refine Triple.seq (e3_step v outp sp ua adp ix _ _ j0 j9 j10 j11 _ hc (hd.cast (by omega))) ?_
    refine Triple.seq (muldi3_call (pc := 0x800070c4#64) (w := 0x47c100ef#32) (imm := 0x01047c#21)
      (Lk := qH sp ua adp ix (combaW (colS da ua) ix + 2 * hp da ua ix) j0 j9 j10 j11)
      (L2 := (10, BitVec.ofNat 64 (da (ix / 2) * da (ix / 2))) ::
        qH sp ua adp ix (combaW (colS da ua) ix + 2 * hp da ua ix) j0 j9 j10 j11)
      hC.img hc (by decide +kernel) (by decide) (by decide) (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide) (by decide)
      (fun p hp => hp) (by simp [qH, keysG]) (by simp [kF, keysG])
      (by unfold KeepOK
          rw [show keysG (qH sp ua adp ix (combaW (colS da ua) ix + 2 * hp da ua ix) j0 j9 j10 j11 ++ kF v) =
            [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 3, 4] from rfl]; decide)
      (fun p hp => List.mem_cons_of_mem _ (by rw [ofNat_mul_ofNat]; exact hp))) ?_
    have := se_step v outp sp ua adp ix (combaW (colS da ua) ix + 2 * hp da ua ix) (da (ix / 2) * da (ix / 2))
      j0 j9 j10 j11 M hc hC.k (by omega) (by omega)
    rwa [Nat.add_assoc] at this
  · simp only [he, if_false, Nat.add_zero] at hw ⊢
    exact so_step v outp sp ua adp ix _ j0 j9 j10 j11 M hc hC.k (by omega) (by omega) hw

/-- **The column loop**: from column `ix` to the store point of the last column, at `71ec`. -/
theorem loop (h : SLoopH m0 sp ua adp da) (hua : 1 ≤ ua) :
    ∀ ix, ix < 2 * ua → Triple (fun cf => ∃ j0 j9 j10 j11 : BitVec 64, WSt m0 v outp sp 0x800070a8#64
        (qH sp ua adp ix (combaW (colS da ua) ix + 2 * hp da ua ix) j0 j9 j10 j11)
        (ovl (combaD (colS da ua)) old ix) cf)
      (fun cf => ∃ j0 j9 j10 j11 : BitVec 64, WSt m0 v outp sp 0x800071ec#64
        (sP sp ua adp (2 * ua - 1) (combaW (colS da ua) (2 * ua - 1) + colS da ua (2 * ua - 1)) j0 j9 j10 j11)
        (ovl (combaD (colS da ua)) old (2 * ua)) cf) := by
  refine Triple.countup (fun ix hi => ?_) ?_
  · intro cf ⟨j0, j9, j10, j11, hs⟩
    refine Triple.seq (storeCol (v := v) (outp := outp) (old := old) h ix (by omega) j0 j9 j10 j11) ?_ cf hs
    intro cf ⟨M, hA, hat⟩
    have hC := h.ch M _ hA
    have hw := h.bnd ix
    have hw' := h.bnd (ix + 1)
    have e := MulFast.combaW_eq (colS da ua) ix
    have hle : 2 * hp da ua (ix + 1) ≤ colS da ua (ix + 1) := by rw [colS_split]; omega
    refine Triple.rmap (fun cf ⟨j0', j9', j10', j11', h⟩ => ⟨j0', j9', j10', j11', M, hA, by rw [e] at h; exact h⟩)
      (nextCol (v := v) (outp := outp) hC ix _ hi hw (by rw [e]; omega) j0 j9 j10 j11) cf hat
  · intro cf ⟨j0, j9, j10, j11, hs⟩
    have e : 2 * ua - 1 + 1 = 2 * ua := by omega
    refine Triple.seq (storeCol (v := v) (outp := outp) (old := old) h (2 * ua - 1) (by omega) j0 j9 j10 j11) ?_ cf hs
    intro cf ⟨M, hA, hat⟩
    have hC := h.ch M _ hA
    have hl := hC.ua_lt
    rw [e] at hA
    exact Triple.rmap (fun cf h' => ⟨j0, j9, j10, j11, M, hA, h'⟩)
      (d_step v outp sp ua adp (2 * ua - 1) _ j0 j9 j10 j11 M hC.img.sMpSqrFast (by omega) (by omega)) cf hat

end loop

end Tom.Machine.Fn.SqrFast
