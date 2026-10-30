import Tom.Machine.Fn.MulHighFast
import Tom.Machine.Api.MulHighFast
import Tom.Machine.Api.StdLib
import Tom.Machine.Kit.Buf

/-!
# `s_mp_mul_high_digs_fast` on the machine, in place (`c = a`): the whole function

The segments of `Tom.Machine.Fn.MulHighFast` and the contracts of `__muldi3`,
`memcpy` (`memcpyD`) and `mp_clamp` by `call_std` (`Kit/Meet.lean`,
`Api/StdLib.lean`). Regions: `Two`'s (`b` read, `a` written) with the stack cut
by `Kit/Buf.lean` into the spills `lo`, the column array `buf` (`W`, a digit
array once the prologue is done: `St.ramDig`) and the saves `hi`. The column
loop is `Triple.countup_from` over the store point `6ce4` (`EInv`): each column
runs from one of its heads (`runA`, `runB`, `runC`, `runD`) through the inner
loop (`inner`: `__muldi3` per term) to the store, `St.seqOvl` into `W`. After
the loop `memcpy` copies `W[digs, pa)` into `a`; both paths meet at `6d98`
(`fin`: re-abstract `a` by `St.setMp`, `mp_clamp`, the epilogue).
-/


namespace Tom.Machine.Fn.MulHighFast

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Seg Tom.Machine.Api Tom.Machine.Std
open Tom.Machine.Api.Two (R isW)
open Tom.Reduce

/-! ## The value -/

/-- The columns from `digs` on. -/
def cl (a b : MpInt) (dg : Nat) (k : Nat) : Nat := col a.digit b.digit a.used b.used (dg + k)

/-- `_W` after column `ix`'s terms. -/
def Sx (a b : MpInt) (dg ix : Nat) : Nat := combaW (cl a b dg) (ix - dg) + cl a b dg (ix - dg)

/-- `W` after the columns `digs .. ix - 1`, over its contents `old` (the
digits below `digs` are never written). -/
def gW (a b : MpInt) (dg : Nat) (old : Nat → Nat) (j : Nat) : Nat :=
  if j < dg then old j else combaD (cl a b dg) (j - dg)

/-- What `mp_clamp` is handed: `used = pa`, the digits of `highFastDigit`. -/
def cm (a b : MpInt) (dg : Nat) : MpInt :=
  MpInt.ofDigits (a.used + b.used) a.alloc a.sign (highFastDigit a b a dg)

theorem cm_digit {a b : MpInt} {dg : Nat} (hroom : a.used + b.used ≤ a.alloc) (hd : dg ≤ a.used + b.used) :
    (cm a b dg).digit = highFastDigit a b a dg := by
  funext j; rw [cm, MpInt.ofDigits_digit]; split
  · rfl
  · simp only [highFastDigit, show ¬ j < dg by omega, show ¬ j < a.used + b.used by omega, if_false]

theorem cm_shape {a b : MpInt} {dg : Nat} (ha : a.Shape) (hroom : a.used + b.used ≤ a.alloc)
    (hd : dg ≤ a.used + b.used) : (cm a b dg).Shape :=
  { len := MpInt.ofDigits_len _ _ _ _
    used_le := by simp only [cm, MpInt.ofDigits]; omega
    alloc_lt := by simp only [cm, MpInt.ofDigits]; exact ha.alloc_lt
    digit_lt := fun i => by rw [cm_digit hroom hd]; exact highFastDigit_lt ha dg i
    high_zero := fun i hi => by
      rw [cm_digit hroom hd]; simp only [cm, MpInt.ofDigits] at hi
      simp only [highFastDigit, show ¬ i < dg by omega, show ¬ i < a.used + b.used by omega, if_false] }

theorem cm_post {a b c' : MpInt} {dg : Nat} (hroom : a.used + b.used ≤ a.alloc) (hd : dg ≤ a.used + b.used)
    (h : ClampPost (cm a b dg) c') : MulHighFastPost a b a c' dg :=
  { alloc := by rw [h.alloc]; rfl
    len := by rw [h.digits]; exact MpInt.ofDigits_len _ _ _ _
    digit := by rw [h.digit, cm_digit hroom hd]
    used := by rw [h.used, cm_digit hroom hd]; rfl
    sign := by rw [h.sign]; rfl }

/-- The digits after `memcpy` are `highFastDigit`'s. -/
theorem cpy_digit {a b : MpInt} {dg : Nat} (ha : a.Shape) (old : Nat → Nat) (hroom : a.used + b.used ≤ a.alloc)
    (hd : dg ≤ a.used + b.used) (j : Nat) :
    (cm a b dg).digit j = cpy a.digit (ovl (gW a b dg old) old (a.used + b.used)) dg dg (a.used + b.used - dg) j := by
  rw [cm, MpInt.ofDigits_digit]
  by_cases hj : j < a.alloc
  · rw [if_pos hj]; simp only [cpy, highFastDigit, ovl, gW]
    by_cases h1 : j < dg
    · simp [h1, show ¬ dg ≤ j by omega]
    · by_cases h2 : j < a.used + b.used
      · simp only [h1, h2, if_false, if_true, show dg ≤ j by omega, show j < dg + (a.used + b.used - dg) by omega,
          show dg + (j - dg) = j by omega, and_self]
        rfl
      · simp only [h1, h2, if_false, show ¬ (dg ≤ j ∧ j < dg + (a.used + b.used - dg)) by omega]
        exact (ha.high_zero j (by omega)).symm
  · rw [if_neg hj]; simp only [cpy, show ¬ (dg ≤ j ∧ j < dg + (a.used + b.used - dg)) by omega, if_false]
    exact (ha.high_zero j (by omega)).symm

/-! ## The machine -/

abbrev ρw (sp pa adp pb bdp : Nat) (a b : MpInt) := Bf.lay (Two.lay 2192 sp pb bdp pa adp b a) R.stk 2192 32 2048

abbrev Wr : List (Bf R) := [.lo, .buf, .hi, .o .stk, .o .bS, .o .bD]

/-- The state over our regions. -/
abbrev SL (m : Mem) (sp pa adp pb bdp : Nat) (a b : MpInt) (κ : Bf R → Kind) (M : Mem) : Prop :=
  St (ρw sp pa adp pb bdp a b) (Bf.wr isW) Wr κ m M

def σm : Cd → Bf R := fun _ => .o .code

def σcp : Dc → Bf R
  | .D => .o .bD
  | .S => .buf
  | .code => .o .code

def σz : Ob → Bf R
  | .S => .o .bS
  | .D => .o .bD
  | .code => .o .code

theorem cd {m M : Mem} {sp pa adp pb bdp : Nat} {a b : MpInt} {κ : Bf R → Kind} (h : SL m sp pa adp pb bdp a b κ M)
    (hk : κ (.o .code) = .code := by rfl) : CodeAt M sMpMulHighDigsFastBase sMpMulHighDigsFastCode :=
  (h.img (.o .code) hk).sMpMulHighDigsFast

/-- At the store point `6ce4` with the sum `S`. -/
def EAt (m : Mem) (v : Abi) (outp : Array String) (sp pa adp pb bdp : Nat) (a b : MpInt) (κ : Bf R → Kind)
    (ix S : Nat) (cf : Vsa.Machine.Config) : Prop :=
  ∃ M j0 j8 j11, SL m sp pa adp pb bdp a b κ M ∧ At 0x80006ce4#64 (eL sp a.used b.used adp bdp ix S j0 j8 j11) M (kF v) outp cf

section column
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp dg : Nat} {a b : MpInt} {ra : BitVec 64}
  {κ : Bf R → Kind}

/-- The kinds a column reads. -/
structure KC (κ : Bf R → Kind) (pa adp pb bdp : Nat) (a b : MpInt) : Prop where
  ka : κ (.o .bD) = .mpD adp a.alloc a.digit
  kb : κ (.o .aD) = .mpD bdp b.alloc b.digit
  kc : κ (.o .code) = .code

theorem lfacts (hP : MulHighFast.Pre m sp pa adp pb bdp dg a b ra) (hK : KC κ pa adp pb bdp a b) {M : Mem}
    (h : SL m sp pa adp pb bdp a b κ M) {ix iz : Nat} (hix : ix < a.used + b.used) (hiz : iz < combaIy a.used b.used ix) :
    LFacts M adp bdp (combaTx b.used ix) (combaTy b.used ix) iz (a.digit (combaTx b.used ix + iz))
      (b.digit (combaTy b.used ix - iz)) := by
  have := hP.cond.ub_pos; have hu := hP.sa.used_le; have hv := hP.sb.used_le
  have ht : combaTx b.used ix + iz < a.used := by unfold combaIy at hiz; omega
  have hty : iz ≤ combaTy b.used ix ∧ combaTy b.used ix < b.used := by unfold combaIy combaTy at *; omega
  have da := h.dig (.o .bD) hK.ka; have db := h.dig (.o .aD) hK.kb
  have e1 : adp + 4 * combaTx b.used ix + 4 * iz = adp + 4 * (combaTx b.used ix + iz) := by omega
  have e2 : bdp + 4 * combaTy b.used ix - 4 * iz = bdp + 4 * (combaTy b.used ix - iz) := by omega
  have := hP.gb.ds.lo_ge
  exact { ra_ := by rw [e1]; exact Ram.sub da.ram (by omega) (by omega)
          rb := by rw [e2]; exact Ram.sub db.ram (by omega) (by omega)
          x_v := by rw [e1]; exact da.arr _ (by omega)
          y_v := by rw [e2]; exact db.arr _ (by omega)
          x_lt := Nat.lt_of_lt_of_le (hP.sa.digit_lt _) (by decide)
          y_lt := Nat.lt_of_lt_of_le (hP.sb.digit_lt _) (by decide)
          iz_le := hty.1, b4 := by omega }

/-- One term of the inner loop: the loads, `__muldi3`, then `k` at `6cdc`. -/
theorem term (hP : MulHighFast.Pre m sp pa adp pb bdp dg a b ra) (hK : KC κ pa adp pb bdp a b) {ix iz S : Nat}
    (hix : ix < a.used + b.used) (hiz : iz < combaIy a.used b.used ix) {Q : Vsa.Machine.Config → Prop}
    (k : ∀ M, SL m sp pa adp pb bdp a b κ M → Triple (At 0x80006cdc#64 (rI sp a.used b.used adp bdp ix
      (combaTx b.used ix) (combaTy b.used ix) (combaIy a.used b.used ix) iz S
      (a.digit (combaTx b.used ix + iz) * b.digit (combaTy b.used ix - iz))) M (kF v) outp) Q) :
    Triple (fun cf => ∃ M, SL m sp pa adp pb bdp a b κ M ∧ At 0x80006cc8#64 (iL sp a.used b.used adp bdp ix
      (combaTx b.used ix) (combaTy b.used ix) (combaIy a.used b.used ix) iz S) M (kF v) outp cf) Q := by
  intro cf ⟨M, h, hat⟩
  exact (St.seq0 (iLd_step v outp sp a.used b.used adp bdp ix (combaTx b.used ix) (combaTy b.used ix)
      (combaIy a.used b.used ix) iz S _ _ M (cd h hK.kc) (lfacts hP hK h hix hiz))
    (call_std muldi3 ⟨a.digit (combaTx b.used ix + iz), b.digit (combaTy b.used ix - iz)⟩ σm h (cd h hK.kc)
      0x069100ef#32 0x10868#21 0x80006cdc#64 trivial
      (fun _ M' _ h' => (k M' h').pre) (hk := fun r => by cases r; exact hK.kc.symm))) cf hat

/-- **The inner loop** of column `ix`, from term `iz` to the store point. -/
theorem inner (hP : MulHighFast.Pre m sp pa adp pb bdp dg a b ra) (hK : KC κ pa adp pb bdp a b) {ix w : Nat}
    (hix : ix < a.used + b.used) (hw : w < 2 ^ 36) :
    ∀ iz, iz < combaIy a.used b.used ix → Triple (fun cf => ∃ M, SL m sp pa adp pb bdp a b κ M ∧
      At 0x80006cc8#64 (iL sp a.used b.used adp bdp ix (combaTx b.used ix) (combaTy b.used ix)
        (combaIy a.used b.used ix) iz (w + combaPart a.digit b.digit b.used ix iz)) M (kF v) outp cf)
      (EAt m v outp sp pa adp pb bdp a b κ ix (w + colC a.digit b.digit a.used b.used ix)) := by
  have hub := hP.cond.ub_pos; have hmf := hP.cond.maxf; have hpw := hP.cond.pa_w
  have hroom := colC_room hP.sa.digit_lt hP.sb.digit_lt a.used b.used ix hub hmf
  have hle : ∀ n, n ≤ combaIy a.used b.used ix → w + combaPart a.digit b.digit b.used ix n < 2 ^ 64 := fun n hn => by
    have := combaPart_le a.digit b.digit a.used b.used ix n hn; omega
  have hga := hP.ga.ds.hi_le; have := hP.sa.used_le; have := hP.sb.used_le
  have hax : adp + 4 * combaTx b.used ix + 4 * combaIy a.used b.used ix ≤ 2 ^ 32 := by
    unfold combaIy combaTx combaTy at *; simp only [Layout.sizeofDigit] at hga; omega
  intro iz hiz
  refine Triple.countup_from (lo := 0) (n := combaIy a.used b.used ix) (P := fun iz cf => ∃ M,
    SL m sp pa adp pb bdp a b κ M ∧ At 0x80006cc8#64 (iL sp a.used b.used adp bdp ix (combaTx b.used ix)
      (combaTy b.used ix) (combaIy a.used b.used ix) iz (w + combaPart a.digit b.digit b.used ix iz)) M (kF v) outp cf)
    (fun iz _ hi => ?_) ?_ iz (Nat.zero_le _) hiz
  · refine term hP hK hix (by omega) fun M h => ?_
    have e : w + combaPart a.digit b.digit b.used ix (iz + 1) = w + combaPart a.digit b.digit b.used ix iz +
        a.digit (combaTx b.used ix + iz) * b.digit (combaTy b.used ix - iz) := by
      simp only [combaPart, sumTo]; omega
    exact Triple.rmap (fun cf hc => ⟨M, h, by rw [e]; exact hc⟩)
      (iAt_step v outp sp a.used b.used adp bdp ix (combaTx b.used ix) (combaTy b.used ix) (combaIy a.used b.used ix)
        iz _ _ M (cd h hK.kc) (by
        have := hle (iz + 1) (by omega); simp only [combaPart, sumTo] at this ⊢; omega) hi hax)
  · refine term hP hK hix (by omega) fun M h => ?_
    have hiy : combaIy a.used b.used ix - 1 + 1 = combaIy a.used b.used ix := by omega
    have e : w + colC a.digit b.digit a.used b.used ix = w + combaPart a.digit b.digit b.used ix
        (combaIy a.used b.used ix - 1) + a.digit (combaTx b.used ix + (combaIy a.used b.used ix - 1)) *
          b.digit (combaTy b.used ix - (combaIy a.used b.used ix - 1)) := by
      unfold colC; conv => lhs; rw [← hiy]
      simp only [combaPart, sumTo]; omega
    exact Triple.rmap (fun cf hc => ⟨M, _, _, _, h, by rw [e]; exact hc⟩)
      (iAf_step v outp sp a.used b.used adp bdp ix (combaTx b.used ix) (combaTy b.used ix) (combaIy a.used b.used ix)
        (combaIy a.used b.used ix - 1) _ _ M (cd h hK.kc) (by
        have := hle (combaIy a.used b.used ix) (Nat.le_refl _); rw [← hiy] at this
        simp only [combaPart, sumTo] at this ⊢; omega) hiy)

/-- From head D (`6cb8`, `iy > 0`). -/
theorem runD (hP : MulHighFast.Pre m sp pa adp pb bdp dg a b ra) (hK : KC κ pa adp pb bdp a b) {ix w : Nat}
    {j8 : BitVec 64} (hix : ix < a.used + b.used) (hw : w < 2 ^ 36) (hiy : 0 < combaIy a.used b.used ix) {M : Mem}
    (h : SL m sp pa adp pb bdp a b κ M) :
    Triple (At 0x80006cb8#64 (cL sp a.used b.used adp bdp ix w (combaTy b.used ix) (combaIy a.used b.used ix)
        (combaTx b.used ix) j8) M (kF v) outp)
      (EAt m v outp sp pa adp pb bdp a b κ ix (w + colC a.digit b.digit a.used b.used ix)) := by
  have := hP.cond.pa_w
  have h1 : combaIy a.used b.used ix < 2 ^ 30 := by unfold combaIy combaTx combaTy; omega
  have h2 : combaTy b.used ix < 2 ^ 30 := by unfold combaTy; omega
  refine St.seq0 (cD_step v outp sp a.used b.used adp bdp ix w (combaTy b.used ix) (combaIy a.used b.used ix)
    (combaTx b.used ix) j8 M (cd h hK.kc) h1 h2) ?_
  exact Triple.lmap (fun cf hc => ⟨M, h, by simpa only [combaPart, sumTo, Nat.add_zero] using hc⟩)
    (inner hP hK hix hw 0 hiy)

/-- From head C (`6cb4`). -/
theorem runC (hP : MulHighFast.Pre m sp pa adp pb bdp dg a b ra) (hK : KC κ pa adp pb bdp a b) {ix w : Nat}
    {j8 : BitVec 64} (hix : ix < a.used + b.used) (hw : w < 2 ^ 36) {M : Mem} (h : SL m sp pa adp pb bdp a b κ M) :
    Triple (At 0x80006cb4#64 (cL sp a.used b.used adp bdp ix w (combaTy b.used ix) (combaIy a.used b.used ix)
        (combaTx b.used ix) j8) M (kF v) outp)
      (EAt m v outp sp pa adp pb bdp a b κ ix (w + colC a.digit b.digit a.used b.used ix)) := by
  have := hP.cond.pa_w
  have h1 : combaIy a.used b.used ix < 2 ^ 30 := by unfold combaIy combaTx combaTy; omega
  have h2 : combaTy b.used ix < 2 ^ 30 := by unfold combaTy; omega
  rcases Nat.eq_zero_or_pos (combaIy a.used b.used ix) with h0 | h0
  · have e : colC a.digit b.digit a.used b.used ix = 0 := by unfold colC; rw [h0]; rfl
    rw [h0, e, Nat.add_zero]
    exact Triple.rmap (fun cf hc => ⟨M, _, _, _, h, hc⟩) (cCz_step v outp sp a.used b.used adp bdp ix w
      (combaTy b.used ix) (combaTx b.used ix) j8 M (cd h hK.kc))
  · refine St.seq0 (cCn_step v outp sp a.used b.used adp bdp ix w (combaTy b.used ix) (combaIy a.used b.used ix)
      (combaTx b.used ix) j8 M (cd h hK.kc) h0 h1 h2) ?_
    exact Triple.lmap (fun cf hc => ⟨M, h, by simpa only [combaPart, sumTo, Nat.add_zero] using hc⟩)
      (inner hP hK hix hw 0 h0)

/-- From head B (`6ca4`): `s0 = a->used - tx`. -/
theorem runB (hP : MulHighFast.Pre m sp pa adp pb bdp dg a b ra) (hK : KC κ pa adp pb bdp a b) {ix w : Nat}
    {j2 j8 : BitVec 64} (hix : ix < a.used + b.used) (hw : w < 2 ^ 36) {M : Mem} (h : SL m sp pa adp pb bdp a b κ M) :
    Triple (At 0x80006ca4#64 (bL sp a.used b.used adp bdp ix w (combaTy b.used ix) (a.used - combaTx b.used ix)
        (combaTx b.used ix) j2 j8) M (kF v) outp)
      (EAt m v outp sp pa adp pb bdp a b κ ix (w + colC a.digit b.digit a.used b.used ix)) := by
  have := hP.cond.pa_w
  have h2 : combaTy b.used ix < 2 ^ 30 := by unfold combaTy; omega
  by_cases hle : a.used - combaTx b.used ix ≤ combaTy b.used ix
  · have e : a.used - combaTx b.used ix = combaIy a.used b.used ix := by unfold combaIy; omega
    refine St.seq0 (cBt_step v outp sp a.used b.used adp bdp ix w (combaTy b.used ix) (a.used - combaTx b.used ix)
      (combaTx b.used ix) j2 j8 M (cd h hK.kc) h2 (by omega) hle) ?_
    rw [e]; exact runC hP hK hix hw h
  · have e : combaTy b.used ix + 1 = combaIy a.used b.used ix := by unfold combaIy; omega
    refine St.seq0 (cBf_step v outp sp a.used b.used adp bdp ix w (combaTy b.used ix) (a.used - combaTx b.used ix)
      (combaTx b.used ix) j2 j8 M (cd h hK.kc) h2 (by omega) (by omega)) ?_
    rw [e]; exact runC hP hK hix hw h

/-- From head A (`6c84`, `ix ≥ b->used`). -/
theorem runA (hP : MulHighFast.Pre m sp pa adp pb bdp dg a b ra) (hK : KC κ pa adp pb bdp a b) {ix w : Nat}
    {j0 j2 j3 j8 j11 : BitVec 64} (hix : ix < a.used + b.used) (hge : b.used ≤ ix) (hw : w < 2 ^ 36) {M : Mem}
    (h : SL m sp pa adp pb bdp a b κ M) :
    Triple (At 0x80006c84#64 (aL sp a.used b.used adp bdp ix w j0 j2 j3 j8 j11) M (kF v) outp)
      (EAt m v outp sp pa adp pb bdp a b κ ix (w + colC a.digit b.digit a.used b.used ix)) := by
  have := hP.cond.pa_w; have hub := hP.cond.ub_pos
  have hga := hP.ga.ds.hi_le; have := hP.sa.used_le; simp only [Layout.sizeofDigit] at hga
  refine St.seq0 (cA_step v outp sp a.used b.used adp bdp ix w j0 j2 j3 j8 j11 M (cd h hK.kc) (by omega) (by omega)
    hub hge hix (by omega)) ?_
  have e1 : b.used - 1 = combaTy b.used ix := by unfold combaTy; omega
  have e2 : ix + 1 - b.used = combaTx b.used ix := by unfold combaTx combaTy; omega
  have e3 : a.used + b.used - 1 - ix = a.used - combaTx b.used ix := by unfold combaTx combaTy; omega
  rw [e1, e2, e3]; exact runB hP hK hix hw h

end column

/-! ## The column loop -/

theorem EAt.eq {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp : Nat} {a b : MpInt}
    {κ : Bf R → Kind} {ix S S' : Nat} {cf : Vsa.Machine.Config} (e : S = S')
    (h : EAt m v outp sp pa adp pb bdp a b κ ix S cf) : EAt m v outp sp pa adp pb bdp a b κ ix S' cf := e ▸ h

section loop
variable {a b : MpInt} {dg : Nat}

theorem cl_room (ha : a.Shape) (hb : b.Shape) (hub : 1 ≤ b.used) (hm : min a.used b.used ≤ 256) (k : Nat) :
    cl a b dg k + 2 ^ 36 ≤ 2 ^ 64 := by
  have := colC_room ha.digit_lt hb.digit_lt a.used b.used (dg + k) hub hm
  rwa [colC_eq _ _ _ _ _ hub] at this

theorem w_lt (ha : a.Shape) (hb : b.Shape) (hub : 1 ≤ b.used) (hm : min a.used b.used ≤ 256) (k : Nat) :
    combaW (cl a b dg) k < 2 ^ 36 := combaW_lt (cl_room ha hb hub hm) k

theorem Sx_lt (ha : a.Shape) (hb : b.Shape) (hub : 1 ≤ b.used) (hm : min a.used b.used ≤ 256) (ix : Nat) :
    Sx a b dg ix < 2 ^ 64 := by
  have := w_lt (dg := dg) ha hb hub hm (ix - dg); have := cl_room (dg := dg) ha hb hub hm (ix - dg)
  unfold Sx; omega

theorem Sx_div {ix : Nat} (h : dg ≤ ix) : Sx a b dg ix / 268435456 = combaW (cl a b dg) (ix + 1 - dg) := by
  rw [show ix + 1 - dg = (ix - dg) + 1 by omega]; rfl

theorem Sx_mod {ix : Nat} (old : Nat → Nat) (h : dg ≤ ix) : Sx a b dg ix % 268435456 = gW a b dg old ix := by
  simp only [gW, if_neg (show ¬ ix < dg by omega)]; rfl

theorem Sx_succ (hub : 1 ≤ b.used) {ix : Nat} (h : dg ≤ ix) :
    combaW (cl a b dg) (ix + 1 - dg) + colC a.digit b.digit a.used b.used (ix + 1) = Sx a b dg (ix + 1) := by
  unfold Sx; rw [colC_eq _ _ _ _ _ hub]; simp only [cl, show dg + (ix + 1 - dg) = ix + 1 by omega]

theorem Sx_zero (hub : 1 ≤ b.used) : 0 + colC a.digit b.digit a.used b.used dg = Sx a b dg dg := by
  unfold Sx; rw [colC_eq _ _ _ _ _ hub]; simp [cl, combaW]

theorem ovl_gW (old : Nat → Nat) : ovl (gW a b dg old) old dg = old := by
  funext j; simp only [ovl, gW]; split <;> simp_all

end loop

/-- The saves (`hi`). -/
abbrev mH (m : Mem) (ra s0 : BitVec 64) (v : Abi) (sp : Nat) : Mem :=
  writeLog (writeLog (writeLog m (log1 v sp)) (log2a ra s0 v sp)) (log2b v sp)

/-- The spills (`lo`). -/
abbrev mL (m : Mem) (sp pa dg : Nat) (a b : MpInt) : Mem :=
  writeLog (writeLog m (log3 sp pa dg a.used b.used)) (log4 sp dg)

/-- The kinds in the loop: `W` over `old` with the columns below `ix`. -/
abbrev κW (m : Mem) (ra s0 : BitVec 64) (v : Abi) (sp pa adp pb bdp dg : Nat) (a b : MpInt) (old : Nat → Nat)
    (ix : Nat) : Bf R → Kind :=
  Bf.kind (Two.kind pb bdp pa adp b a) (mL m sp pa dg a b) (mH m ra s0 v sp)
    (.mpD (sp - 2160) 512 (ovl (gW a b dg old) old ix))

/-- **The loop invariant**: at the store point of column `ix` with its sum. -/
def EInv (m : Mem) (v : Abi) (outp : Array String) (ra s0 : BitVec 64) (sp pa adp pb bdp dg : Nat) (a b : MpInt)
    (old : Nat → Nat) (ix : Nat) : Vsa.Machine.Config → Prop :=
  EAt m v outp sp pa adp pb bdp a b (κW m ra s0 v sp pa adp pb bdp dg a b old ix) ix (Sx a b dg ix)

section run
variable {m : Mem} {v : Abi} {outp : Array String} {sp pa adp pb bdp dg : Nat} {a b : MpInt} {ra s0 : BitVec 64}

/-- From `6d98` (both paths): `olduse ≤ pa`, re-abstract `a`, `mp_clamp(a)`, the epilogue. -/
theorem fin (hP : MulHighFast.Pre m sp pa adp pb bdp dg a b ra) (hk : KF sp) {M ml : Mem} {kb : Kind}
    {f : Nat → Nat} {u : Abi}
    (h : SL m sp pa adp pb bdp a b (Kind.set (Bf.kind (Two.kind pb bdp pa adp b { a with used := a.used + b.used })
      ml (mH m ra s0 v sp) kb) (.o .bD) (.mpD adp a.alloc f)) M)
    (hf : ∀ j, j < a.alloc → (cm a b dg).digit j = f j) (hsp : u.sp = BitVec.ofNat 64 (sp - 2192))
    (h1 : u.s.s1 = BitVec.ofNat 64 a.used) (hl8 : bytesT8 ml (sp - 2192 + 8) = BitVec.ofNat 64 pa)
    (hl24 : bytesT8 ml (sp - 2192 + 24) = BitVec.ofNat 64 (a.used + b.used)) :
    Triple (At 0x80006d98#64 ((10, BitVec.ofNat 64 (adp + 4 * (a.used + b.used))) :: abiL u) M (kF v) outp)
      (MulHighFast.Ret m v outp sp pa adp pb bdp dg a b ra s0) := by
  obtain ⟨usp, ugp, utp, us0, us⟩ := u
  simp only at hsp h1; subst hsp
  have := hP.sp_ge; have := hP.cond.pa_w; have hra := hP.ra_al; have hroom := hP.room; have hdg := hP.cond.dg_le
  have hrd : ∀ o, o + 8 ≤ 32 → bytesT8 M (sp - 2192 + o) = bytesT8 ml (sp - 2192 + o) := fun o ho =>
    h.frz .lo rfl (by iv_omega)
  refine St.seq0 (t3z_step v outp ⟨_, ugp, utp, us0, us⟩ sp _ a.used (a.used + b.used) M (cd h) rfl h1 hk
    (by rw [hrd 24 (by decide)]; exact hl24) (by omega) (by omega)) ?_
  refine St.seq0 (t4_step v outp ⟨_, ugp, utp, us0, us⟩ sp pa M (cd h) rfl hk (by rw [hrd 8 (by decide)]; exact hl8)) ?_
  have h2 := h.setMp (.o .bS) (.o .bD) rfl rfl (cm a b dg) rfl rfl rfl rfl hf
  refine call_std clamp ⟨pa, adp, cm a b dg⟩ σz h2 (cd h2) 0xa24fe0ef#32 0x1fe224#21 0x80006db8#64
    (cm_shape hP.sa hroom hdg) (fun c' M' hcl h3 => ?_) (hsub := fun r => by cases r <;> exact Iv.sub_self _)
  exact (Triple.rmap (fun cf hc => ⟨c', _, hc.sub rfl rfl,
      { repr := (h3.hdr (.o .bS) rfl).mpAt (by rw [hcl.alloc, hcl.digit]; exact h3.dig (.o .bD) rfl)
        fast := cm_post hroom hdg hcl
        frame := h3.unbuf (by decide) (by simp [Two.lay]) }⟩)
    (t5_step ra s0 v outp sp M' (cd h3) (by facts h3))).pre

/-- A column's step: the store `W[ix]`, the next column from its head. -/
theorem step (hP : MulHighFast.Pre m sp pa adp pb bdp dg a b ra) (hk : KF sp) (old : Nat → Nat) (ix : Nat)
    (hix1 : dg ≤ ix) (hix2 : ix + 1 < a.used + b.used) :
    Triple (EInv m v outp ra s0 sp pa adp pb bdp dg a b old ix) (EInv m v outp ra s0 sp pa adp pb bdp dg a b old (ix + 1)) := by
  intro cf ⟨M, j0, j8, j11, h, hat⟩
  have hub := hP.cond.ub_pos; have hpw := hP.cond.pa_w; have hmf := hP.cond.maxf
  have hS := Sx_lt (dg := dg) hP.sa hP.sb hub hmf ix
  have hw := w_lt (dg := dg) hP.sa hP.sb hub hmf (ix + 1 - dg)
  have hK : KC (κW m ra s0 v sp pa adp pb bdp dg a b old (ix + 1)) pa adp pb bdp a b := ⟨rfl, rfl, rfl⟩
  have hv : Sx a b dg ix % 268435456 < 2 ^ 32 := by omega
  have conv : ∀ M', SL m sp pa adp pb bdp a b (Kind.set (κW m ra s0 v sp pa adp pb bdp dg a b old ix) .buf
      (.mpD (sp - 2160) 512 (ovl (gW a b dg old) old (ix + 1)))) M' →
      SL m sp pa adp pb bdp a b (κW m ra s0 v sp pa adp pb bdp dg a b old (ix + 1)) M' :=
    fun M' h' => h'.congrK (by intro r; rcases r with _ | _ | _ | r <;> rfl)
  by_cases hb : b.used ≤ ix + 1
  · refine (h.seqOvl .buf rfl (eA_step v outp sp a.used b.used adp bdp ix (Sx a b dg ix) j0 j8 j11 M (cd h)
      ⟨hk, by omega⟩ hS hix2 (by omega) hb) (by omega) hv (Sx_mod old hix1) fun M' h' => ?_) cf hat
    rw [Sx_div hix1]
    exact Triple.rmap (fun cf hc => EAt.eq (Sx_succ hub hix1) hc) (runA hP hK hix2 hb hw (conv M' h'))
  by_cases ha : a.used ≤ ix + 1
  · refine (h.seqOvl .buf rfl (eB_step v outp sp a.used b.used adp bdp ix (Sx a b dg ix) j0 j8 j11 M (cd h)
      ⟨hk, by omega⟩ hS hix2 (by omega) (by omega) ha) (by omega) hv (Sx_mod old hix1) fun M' h' => ?_) cf hat
    rw [Sx_div hix1]
    have r := runC (v := v) (outp := outp) hP hK (ix := ix + 1) (j8 := j8) hix2 hw (conv M' h')
    have e1 : combaTy b.used (ix + 1) = ix + 1 := by unfold combaTy; omega
    have e3 : combaTx b.used (ix + 1) = 0 := by unfold combaTx combaTy; omega
    have e2 : combaIy a.used b.used (ix + 1) = a.used := by unfold combaIy; rw [e3, e1]; omega
    rw [e2, e1, e3] at r
    exact Triple.rmap (fun cf hc => EAt.eq (Sx_succ hub hix1) hc) r
  · refine (h.seqOvl .buf rfl (eC_step v outp sp a.used b.used adp bdp ix (Sx a b dg ix) j0 j8 j11 M (cd h)
      ⟨hk, by omega⟩ hS hix2 (by omega) (by omega) (by omega)) (by omega) hv (Sx_mod old hix1) fun M' h' => ?_) cf hat
    rw [Sx_div hix1]
    have e1 : combaTy b.used (ix + 1) = ix + 1 := by unfold combaTy; omega
    have e3 : combaTx b.used (ix + 1) = 0 := by unfold combaTx combaTy; omega
    have e2 : combaIy a.used b.used (ix + 1) = ix + 2 := by unfold combaIy; rw [e3, e1]; omega
    have r := runD (v := v) (outp := outp) hP hK (ix := ix + 1) (j8 := j8) hix2 hw (by omega) (conv M' h')
    rw [e2, e1, e3] at r
    exact Triple.rmap (fun cf hc => EAt.eq (Sx_succ hub hix1) hc) r

/-- The last column's store, `c->used := pa`, `memcpy`, then `fin`. -/
theorem last (hP : MulHighFast.Pre m sp pa adp pb bdp dg a b ra) (hk : KF sp) (old : Nat → Nat)
    (hlt : dg < a.used + b.used) :
    Triple (EInv m v outp ra s0 sp pa adp pb bdp dg a b old (a.used + b.used - 1))
      (MulHighFast.Ret m v outp sp pa adp pb bdp dg a b ra s0) := by
  intro cf ⟨M, j0, j8, j11, h, hat⟩
  have hub := hP.cond.ub_pos; have hpw := hP.cond.pa_w; have hmf := hP.cond.maxf; have hroom := hP.room
  have := hP.sp_ge; have := hP.sa.used_le; have hga := hP.ga.ds.hi_le; simp only [Layout.sizeofDigit] at hga
  have hix : dg ≤ a.used + b.used - 1 := by omega
  have hS := Sx_lt (dg := dg) hP.sa hP.sb hub hmf (a.used + b.used - 1)
  refine (h.seqOvl .buf rfl (eX_step v outp sp a.used b.used adp bdp (a.used + b.used - 1)
    (Sx a b dg (a.used + b.used - 1)) j0 j8 j11 M (cd h) ⟨hk, by omega⟩ hS (by omega) (by omega)) (by omega)
    (by omega) (Sx_mod old hix) fun M1 h1 => ?_) cf hat
  rw [show a.used + b.used - 1 + 1 = a.used + b.used by omega] at h1
  refine St.seq0 (t1a_step v outp sp a.used b.used adp bdp _ _ dg pa adp a.used j0 j8 j11 M1 (cd h1) (by facts h1)
    (by omega) hlt) ?_
  refine h1.seqU (.o .bS) rfl (t1b_step v outp sp a.used b.used adp bdp _ _ dg pa adp a.used j8 j11 M1 (cd h1)
    (by facts h1) (by omega) hlt (by omega)) (by omega) fun M2 h2 => ?_
  refine call_std memcpyD ⟨adp, a.alloc, a.digit, dg, sp - 2160, 512, ovl (gW a b dg old) old (a.used + b.used), dg,
    a.used + b.used - dg⟩ σcp h2 (cd h2) 0x6f8020ef#32 0x26f8#21 0x80006d8c#64
    ⟨show dg + (a.used + b.used - dg) ≤ a.alloc by omega, show dg + (a.used + b.used - dg) ≤ 512 by omega⟩
    fun _ M3 _ h3 => ?_
  refine St.seq0 (t2_step v outp (Abi.ofL (((1, 0x80006d8c#64) :: dropRa (mcL sp a.used b.used adp bdp
    (a.used + b.used - 1) (Sx a b dg (a.used + b.used - 1)) dg adp a.used j8 j11)) ++ kF v)) adp dg (a.used + b.used)
    M3 (cd h3) rfl hlt (by omega) (by omega)) ?_
  exact fin hP hk (ml := mL m sp pa dg a b) (kb := .mpD (sp - 2160) 512 (ovl (gW a b dg old) old (a.used + b.used)))
    (h3.congrK (by intro r; rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> rfl))
    (fun j _ => cpy_digit hP.sa old hroom hP.cond.dg_le j) rfl rfl (by rd_log) (by rd_log)

end run

/-- The frame off the text. -/
theorem kf_of {m : Mem} {sp pa adp pb bdp dg : Nat} {a b : MpInt} {ra : BitVec 64}
    (hP : MulHighFast.Pre m sp pa adp pb bdp dg a b ra) : KF sp := by
  have hd := hP.lay (Api.Two.R.stk) (Api.Two.R.code) (by decide)
  have := hP.sp_ge
  simp only [Iv.Disj, Disj, Two.lay, textIv, textBase, textLen] at hd
  exact ⟨hP.rs, hP.sp_al, this, by simp only [sMpMulHighDigsFastBase]; omega⟩

/-- **`s_mp_mul_high_digs_fast(a, b, a, digs)` on the machine** (`c = a`). -/
theorem correct : Api.MulHighFast.StatementInPlace := by
  intro m v outp sp pa adp pb bdp dg a b ra s0 hP
  have hk := kf_of hP
  have h0 := St.twoB (f := 2192) (a := 32) (B := 2048) hP.rb hP.gb hP.ra_ hP.ga hP.rs hP.img hP.lay (by decide)
    (by decide)
  have := hP.sp_ge; have := hP.sp_al; have hpw := hP.cond.pa_w; have hdg := hP.cond.dg_le; have hub := hP.cond.ub_pos
  have := hP.sa.used_le; have := hP.sb.used_le; have := hP.sa.alloc_lt; have hroom := hP.room
  have hga := hP.ga.ds.hi_le; simp only [Layout.sizeofDigit] at hga
  refine Triple.lmap (fun cf h => h.sub (L' := entL ra s0 v sp pa pb pa dg) (K' := kF v) rfl rfl) ?_
  refine h0.seqW .hi rfl (p1_step ra s0 v outp sp pa pb pa dg m (cd h0) hk (by omega)) fun M1 h1 => ?_
  refine St.seq0 (p1b_step ra s0 v outp sp pa pb pa dg a.used b.used a.alloc M1 (cd h1) (by facts h1)) ?_
  refine h1.seqW .hi rfl (p2a_step ra s0 v outp sp pa pb pa dg a.used b.used a.alloc M1 (cd h1) hk) fun M2 h2 => ?_
  refine h2.seqW .hi rfl (p2b_step ra s0 v outp sp pa pb pa dg a.used b.used a.alloc M2 (cd h2) hk) fun M3 h3 => ?_
  refine h3.seqW .lo rfl (p3_step ra s0 v outp sp pa pb pa dg a.used b.used a.alloc M3 (cd h3) hk (by omega)
    (by omega) (by omega) hroom) fun M4 h4 => ?_
  rcases Nat.lt_or_ge dg (a.used + b.used) with hlt | hge
  · refine h4.seqW .lo rfl (p4f_step v outp sp pa pb a.used b.used dg M4 (cd h4) (by facts h4) (by omega)
      (by omega) hlt) fun M5 h5 => ?_
    have h6 : SL m sp pa adp pb bdp a b (Bf.kind (Two.kind pb bdp pa adp b a) (mL m sp pa dg a b)
        (mH m ra s0 v sp) .ram) M5 := h5.congrK (by intro r; rcases r with _ | _ | _ | r <;> rfl)
    have h7 := h6.ramDig .buf rfl (dp := sp - 2160) (n := 512) (by iv_omega) rfl (by omega)
    have h8 : SL m sp pa adp pb bdp a b (κW m ra s0 v sp pa adp pb bdp dg a b (rdD M5 (sp - 2160)) dg) M5 :=
      h7.congrK (by
        intro r; rcases r with _ | _ | _ | r
        · rfl
        · show Kind.mpD _ _ _ = Kind.mpD _ _ _; rw [ovl_gW]
        · rfl
        · rfl)
    have hK : KC (κW m ra s0 v sp pa adp pb bdp dg a b (rdD M5 (sp - 2160)) dg) pa adp pb bdp a b := ⟨rfl, rfl, rfl⟩
    have loop := Triple.countup_from (lo := dg) (n := a.used + b.used)
      (P := EInv m v outp ra s0 sp pa adp pb bdp dg a b (rdD M5 (sp - 2160)))
      (fun ix h1 h2 => step hP hk _ ix h1 h2) (last hP hk _ hlt) dg (Nat.le_refl _) hlt
    by_cases hdb : dg < b.used
    · refine St.seq0 (p5t_step v outp sp pa pb a.used b.used adp bdp dg M5 (cd h8) (by facts h8) (by omega)
        (by omega) hdb) ?_
      have r := runB (v := v) (outp := outp) hP hK (ix := dg) (w := 0) (j2 := v.s.s2) (j8 := v.s.s8) hlt (by decide) h8
      have e1 : combaTy b.used dg = dg := by unfold combaTy; omega
      have e3 : combaTx b.used dg = 0 := by unfold combaTx combaTy; omega
      rw [e1, e3, Nat.sub_zero] at r
      exact Triple.seq (Triple.rmap (fun cf hc => EAt.eq (Sx_zero hub) hc) r) loop
    · refine St.seq0 (p5f_step v outp sp pa pb a.used b.used adp bdp dg M5 (cd h8) (by facts h8) (by omega)
        (by omega) (by omega)) ?_
      exact Triple.seq (Triple.rmap (fun cf hc => EAt.eq (Sx_zero hub) hc)
        (runA (v := v) (outp := outp) hP hK hlt (by omega) (by decide) h8)) loop
  · have he : dg = a.used + b.used := by omega
    refine h4.seqW .lo rfl (p4t_step v outp sp pa pb a.used b.used dg M4 (cd h4) (by facts h4) (by omega)
      (by omega) hge) fun M5 h5 => ?_
    refine h5.seqW .lo rfl (z1_step v outp sp pa pb a.used b.used dg pa adp a.used M5 (cd h5) (by facts h5))
      fun M6 h6 => ?_
    refine h6.seqU (.o .bS) rfl (z2_step v outp sp pa pb a.used b.used dg pa adp a.used M6 (cd h6) (by facts h6) he
      (by omega) (by omega)) (by omega) fun M7 h7 => ?_
    refine St.seq0 (z3_step v outp (zu v sp pb a.used b.used a.used) (adp + 4 * (a.used + b.used)) M7 (cd h7)) ?_
    refine fin hP hk (ml := writeLog (mL m sp pa dg a b) [(sp - 2192 + 24, 8, BitVec.ofNat 64 dg)]) (kb := .ram)
      (f := a.digit) (h7.congrK (by intro r; rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> rfl))
      (fun j _ => ?_) rfl rfl (by rd_log) (by rw [he]; rd_log)
    rw [cm_digit hroom hdg]; simp only [highFastDigit]; split
    · rfl
    · rw [if_neg (by omega)]; exact (hP.sa.high_zero j (by omega)).symm

end Tom.Machine.Fn.MulHighFast
