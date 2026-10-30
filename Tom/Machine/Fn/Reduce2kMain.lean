import Tom.Machine.Fn.Reduce2k
import Tom.Machine.Api.Reduce2k
import Tom.Machine.Fn.CountBitsMain
import Tom.Machine.Api.Bin
import Tom.Machine.Kit.Jal

/-!
# `mp_reduce_is_2k` on the machine: the whole function

`used ≤ 1`: one chain each. Otherwise the frame, the `mp_count_bits` call
(`jal_at`, then `CountBits.correct`, which leaves memory unchanged), and the
bit loop from `ix = 28` by induction on `iy - ix`, with `iw = ix / 28`,
`iz = 2^(ix % 28)` and the bits `[28, ix)` known to be set. The frame is
the two stores of the prologue (`Frm.store`).
-/


namespace Tom.Machine.Fn.Reduce2k

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api
open Tom.Machine.Api.Un (R isR)

theorem and_pow (d k : Nat) :
    BitVec.ofNat 64 d &&& BitVec.ofNat 64 (2 ^ k) = BitVec.ofNat 64 (if d.testBit k then 2 ^ k else 0) := by
  rw [← BitVec.ofNat_and]; congr 1
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases h : d.testBit k
  · simp only [h, ↓reduceIte, Nat.testBit_two_pow]
    by_cases hj : k = j
    · subst hj; simp [h]
    · simp [hj]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit]
    by_cases hj : k = j
    · subst hj; simp [h]
    · simp [hj]

/-- The callee-saved registers `mp_count_bits` sees. -/
def cbAbi (v : Abi) (sp pa : Nat) : Abi := { v with sp := BitVec.ofNat 64 (sp - 16), s0 := BitVec.ofNat 64 pa }

/-- `mp_count_bits(a)` at `1d3c`, back at `1d40`. -/
theorem cb_call (ra : BitVec 64) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (M : Mem)
    (hc : CodeAt M mpReduceIs2kBase mpReduceIs2kCode) (hP : Api.CountBits.Pre M pa adp a 0x80001d40#64) :
    Triple (At 0x80001d3c#64 (callL ra sp pa) M v.keepR outp)
      (At 0x80001d40#64 (aftL sp pa (countBits a)) M v.keepR outp) := by
  refine Triple.seq (jal_at (pc := 0x80001d3c#64) (w := 0x3b4030ef#32) (imm := 0x033b4#21)
      (L' := [(2, BitVec.ofNat 64 (sp - 16)), (8, BitVec.ofNat 64 pa), (10, BitVec.ofNat 64 pa)])
      (hc.word (a := (0x80001d3c#64 : BitVec 64).toNat) (by decide +kernel)) (by decide) (by decide)
      (fun s h1 h2 h3 => decodeW s h1 h2 h3)
      ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩ (by decide)
      (by simp [callL]) (by simp [keysG]) (by simp [Abi.keepR, keysG, sKeepL])) ?_
  refine Triple.dimap (fun c h => ?_) (fun c h => h.reshape ?_ ?_)
    (@CountBits.correct M (cbAbi v sp pa) outp pa adp a _ hP)
  · have hpc : (0x80001d3c#64 : BitVec 64) + sign_extend (m := 64) (0x033b4#21) = Api.CountBits.entry := by
      decide
    rw [hpc] at h
    refine h.reshape ?_ ?_
    · simp [CountBits.entryL, Sail.BitVec.addInt]
    · simp [Abi.keep, Abi.keepR, cbAbi, sKeepL]
  · simp [aftL, Abi.keep, cbAbi, sKeepL]
  · simp [Abi.keep, Abi.keepR, cbAbi, sKeepL]

/-- Bit `j` of `a` from the digits. -/
abbrev Bit (a : MpInt) (j : Nat) : Prop := (a.digit (j / 28)).testBit (j % 28) = true

/-- The bit loop from `ix`. -/
theorem loop (ra s0 : BitVec 64) (v : Abi) (outp : Array String) (sp pa adp : Nat) (a : MpInt) (M : Mem)
    (hc : CodeAt M mpReduceIs2kBase mpReduceIs2kCode) (hr : RFacts M ra s0 sp) (hA : MpAt M pa adp a)
    (hs : a.Shape) (hg : MpGeom pa adp a.alloc) (hb : 28 * a.used < 2 ^ 31) (hra : ra.toNat % 4 = 0)
    (hu2 : 2 ≤ a.used) :
    ∀ k ix, ix + k = countBits a → 28 ≤ ix → ix < countBits a → (∀ j, 28 ≤ j → j < ix → Bit a j) →
      Triple (At 0x80001d58#64 (headL sp pa (countBits a) adp ix (ix / 28) (2 ^ (ix % 28))) M v.keepR outp)
        (At ra (retL ra s0 sp (BitVec.ofNat 64 (isReduce2k a))) M v.keepR outp) := by
  have hcb := countBits_le hs
  simp only [Layout.digitBits] at hcb
  have hd := hg.ds
  simp only [Layout.sizeofDigit] at hd
  have hul := hs.used_le
  have hiso : ∀ (P : Prop) [Decidable P], (P ↔ ∀ ix, ix < countBits a → 28 ≤ ix → Bit a ix) →
      isReduce2k a = if P then 1 else 0 := fun P _ h => by
    unfold isReduce2k
    simp only [show a.used ≠ 0 by omega, show a.used ≠ 1 by omega, ↓reduceIte, Layout.digitBits]
    by_cases hp : P
    · simp only [hp, ↓reduceIte]
      exact ite_eq_left_iff.2 (fun hh => absurd (h.1 hp) hh)
    · simp only [hp, ↓reduceIte]
      exact ite_eq_right_iff.2 (fun hh => absurd (h.2 hh) hp)
  intro k
  induction k with
  | zero => intro ix h1 _ h3; omega
  | succ k ih =>
    intro ix h1 h2 h3 h4
    have hiw : ix / 28 < a.used := by omega
    have hdl := hs.digit_lt (ix / 28)
    simp only [radix, Layout.digitBits] at hdl
    have hk : ix % 28 < 28 := Nat.mod_lt _ (by decide)
    have hz : 2 ^ (ix % 28) ≤ 2 ^ 27 := Nat.pow_le_pow_right (by decide) (by omega)
    have hf : DFacts M adp (countBits a) ix (ix / 28) (2 ^ (ix % 28)) (a.digit (ix / 28)) :=
      { rd := ⟨by have := hd.lo_ge; omega, by have := hd.hi_le; omega, by have := hd.off; omega⟩
        d_v := by simpa [Layout.sizeofDigit] using hA.digits (ix / 28) (by omega)
        d_lt := by omega
        iy_lt := by omega
        ix_lt := h3
        iw_lt := by omega
        iz_le := hz }
    have hand := and_pow (a.digit (ix / 28)) (ix % 28)
    by_cases hbit : (a.digit (ix / 28)).testBit (ix % 28) = true
    · simp only [hbit, ↓reduceIte] at hand
      have h4' : ∀ j, 28 ≤ j → j < ix + 1 → Bit a j := fun j hj1 hj2 => by
        rcases Nat.lt_or_ge j ix with hj | hj
        · exact h4 j hj1 hj
        · rw [show j = ix by omega]; exact hbit
      have hpos : 0 < 2 ^ (ix % 28) := Nat.pow_pos (by decide)
      by_cases hlast : ix + 1 = countBits a
      · rw [hiso True ⟨fun _ j hj1 hj2 => h4' j hj2 (by omega), fun _ => trivial⟩]
        simp only [↓reduceIte]
        by_cases h27 : ix % 28 < 27
        · exact yes_step ra s0 v outp sp pa M hc hr hra _ adp ix _ _ _ hf hand hpos
            (by rw [← Nat.pow_succ']; exact Nat.pow_lt_pow_right (by decide) (by omega)) hlast
        · exact yesW_step ra s0 v outp sp pa M hc hr hra _ adp ix _ _ _ hf hand
            (by rw [show ix % 28 = 27 by omega]) hlast
      · by_cases h27 : ix % 28 < 27
        · refine Triple.seq (next_step v outp sp pa M hc _ adp ix _ _ _ hf hand hpos
            (by rw [← Nat.pow_succ']; exact Nat.pow_lt_pow_right (by decide) (by omega)) hlast) ?_
          have e1 : (ix + 1) / 28 = ix / 28 := by omega
          have e2 : 2 * 2 ^ (ix % 28) = 2 ^ ((ix + 1) % 28) := by
            rw [← Nat.pow_succ', show (ix + 1) % 28 = ix % 28 + 1 by omega]
          rw [← e1, e2]
          exact ih (ix + 1) (by omega) (by omega) (by omega) h4'
        · refine Triple.seq (nextW_step v outp sp pa M hc _ adp ix _ _ _ hf hand
            (by rw [show ix % 28 = 27 by omega]) hlast) ?_
          have e1 : (ix + 1) / 28 = ix / 28 + 1 := by omega
          have e2 : 2 ^ ((ix + 1) % 28) = 1 := by rw [show (ix + 1) % 28 = 0 by omega]
          have := ih (ix + 1) (by omega) (by omega) (by omega) h4'
          rw [e1, e2] at this
          exact this
    · simp only [hbit, Bool.false_eq_true, ↓reduceIte] at hand
      rw [hiso False ⟨False.elim, fun h => hbit (h ix h3 h2)⟩]
      simp only [↓reduceIte]
      exact no_step ra s0 v outp sp pa M hc hr hra _ adp ix _ _ _ hf hand

/-- **`mp_reduce_is_2k` on the machine.** -/
theorem correct : Api.Reduce2k.Statement := by
  intro m v outp sp pa adp a ra s0 hP
  have hc := hP.img.mpReduceIs2k
  have hra := hP.ra_al
  have hal := hP.va.alloc_lt; have hul := hP.va.used_le
  have hb := hP.bits
  simp only [Layout.digitBits] at hb
  have hu : UFacts m pa a.used := UFacts.of hP.ra_ hP.ga hP.va.toShape
  by_cases h0 : a.used = 0
  · have e : isReduce2k a = 0 := by simp [isReduce2k, h0]
    rw [h0] at hu
    exact Triple.rmap (fun cf h => ⟨m, by rw [e]; exact h, Frm.refl _ m⟩) (zero_step ra s0 v outp sp pa m hc hra hu)
  by_cases h1 : a.used = 1
  · have e : isReduce2k a = 1 := by simp [isReduce2k, h1]
    rw [h1] at hu
    exact Triple.rmap (fun cf h => ⟨m, by rw [e]; exact h, Frm.refl _ m⟩) (one_step ra s0 v outp sp pa m hc hra hu)
  -- the frame and the call
  have hsc := hP.lay.sub (r := R.stk) (s := R.code) (Iv.sub_self _) (Bin.sub_text (b := mpReduceIs2kBase) (k := 160))
  simp only [Iv.Disj, Disj, Un.lay] at hsc
  have hsg := hP.sp_ge
  have hff : FFacts sp := { rs := hP.rs, sp_al := hP.sp_al, sp_ge := hsg, code_off := by omega }
  have hF : Frm (Un.lay 16 sp pa adp a) [R.stk] m (writeLog m (frameLog ra s0 sp)) :=
    Frm.store (by simp only [LogIn, frameLog, Iv.Sub, Un.lay, and_true]; omega)
  have hrs := hP.rs
  have hr : RFacts (writeLog m (frameLog ra s0 sp)) ra s0 sp :=
    { rs := hP.rs, sp_ge := hsg
      s0_v := bytesT8_log _ _ 0 _ _ rfl (by simp [frameLog, OutLRange])
      ra_v := bytesT8_log _ _ 1 _ _ rfl (by simp [frameLog, OutLRange]) }
  have hI := hF.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img
  have hA := hF.keep hP.lay (MpAt.reads (rs := R.aS) (rd := R.aD) (Iv.sub_self _) (Iv.sub_self _)) hP.ra_
  refine Triple.seq (call_step ra s0 v outp sp pa m hc a.used hu (by omega) hff) ?_
  generalize writeLog m (frameLog ra s0 sp) = M at hF hr hI hA ⊢
  have hcb : Api.CountBits.Pre M pa adp a 0x80001d40#64 :=
    { ra_ := hA, va := hP.va, ga := hP.ga, bits := hP.bits, ra_al := by decide, img := hI }
  refine Triple.seq (cb_call ra v outp sp pa adp a M hI.mpReduceIs2k hcb) ?_
  refine Triple.rmap (fun cf h => ⟨M, h, hF.mono⟩) ?_
  have hle := countBits_le hP.va.toShape
  simp only [Layout.digitBits] at hle
  by_cases hy : countBits a ≤ 28
  · have e : isReduce2k a = 1 := by
      simp only [isReduce2k, h0, h1, ↓reduceIte, Layout.digitBits]
      exact ite_eq_left_iff.2 (fun hh => absurd (fun ix h1 h2 => absurd h1 (by omega)) hh)
    rw [e]
    exact short_step ra s0 v outp sp pa M hI.mpReduceIs2k hr hra _ hy (by omega)
  · have hd := hP.ga.st
    refine Triple.seq (enter_step v outp sp pa M hI.mpReduceIs2k _ adp (by omega) (by omega)
      (by simpa [Layout.sizeofMpInt] using hd) (by simpa [Layout.offDp] using hA.dpv)) ?_
    exact loop ra s0 v outp sp pa adp a M hI.mpReduceIs2k hr hA hP.va.toShape hP.ga hb hra (by omega)
      (countBits a - 28) 28 (by omega) (Nat.le_refl _) (by omega) (fun j h1 h2 => by omega)

end Tom.Machine.Fn.Reduce2k
