import Tom.Machine.Fn.CntLsb
import Tom.Machine.Api.CntLsb

/-!
# `mp_cnt_lsb` on the machine: the whole function

Zero: one chain. Otherwise the digit loop by induction on `used - x` (the
digits below `x` zero; for a valid `a` a nonzero digit comes before
`used`), then the parity test and the nibble loop by induction on `q`
(`lsbInner_step`), each nibble read from `.rodata` (`lnz_word`). No store:
memory is unchanged.
-/

namespace Tom.Machine.Fn.CntLsb

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code

/-- The nibble loop. -/
theorem inner (ra : BitVec 64) (v : Abi) (outp : Array String) (m : Mem)
    (hc : CodeAt m mpCntLsbBase mpCntLsbCode) (hro : RoAt m) (hra : ra.toNat % 4 = 0) :
    ∀ n q r, q ≤ n → q ≠ 0 → q < 2 ^ 31 → r + lsbInner q + 4 < 2 ^ 31 →
      Triple (At 0x800050a0#64 (innerL ra r q) m v.keep outp)
        (At ra (retL ra (BitVec.ofNat 64 (r + lsbInner q))) m v.keep outp) := by
  intro n
  induction n with
  | zero => intro q r h1 h2; omega
  | succ n ih =>
    intro q r h1 h2 h3 h4
    have hk := Nat.mod_lt q (show 16 > 0 by decide)
    have hf : LFacts m q r :=
      { l_v := lnz_word hro _ hk, l_le := lnzTab_le _ hk, q_lt := h3, r_lt := by omega }
    by_cases h0 : q % 16 = 0
    · rw [lsbInner_step h0 h2] at h4 ⊢
      refine Triple.seq (in_step ra v outp m hc r q hf h0) ?_
      rw [h0, show lnzTab 0 = 4 from rfl, show r + (4 + lsbInner (q / 16)) = r + 4 + lsbInner (q / 16) by omega]
      exact ih (q / 16) (r + 4) (by omega) (by omega) (by omega) (by omega)
    · rw [lsbInner_stop h0]
      exact out_step ra v outp m hc hra r q hf h0

/-- The digit loop from index `x`. -/
theorem outer (ra : BitVec 64) (v : Abi) (outp : Array String) (pa adp : Nat) (a : MpInt) (m : Mem)
    (hP : Api.CntLsb.Pre m pa adp a ra) (hu : 0 < a.used) :
    ∀ k x, x + k = a.used → x < a.used → (∀ j, j < x → a.digit j = 0) →
      Triple (At 0x80005078#64 (headL ra adp a.used x) m v.keep outp)
        (At ra (retL ra (BitVec.ofNat 64 (cntLsb a))) m v.keep outp) := by
  have hc := hP.img.mpCntLsb
  have hra := hP.ra_al
  have hd := hP.ga.ds
  simp only [Layout.sizeofDigit] at hd
  have hul := hP.va.used_le; have hb := hP.bits
  simp only [Layout.digitBits] at hb
  have htop := hP.va.top hu
  intro k
  induction k with
  | zero => intro x h1 h3; omega
  | succ k ih =>
    intro x h1 h3 h4
    have hdl := hP.va.digit_lt x
    simp only [radix, Layout.digitBits] at hdl
    have hf : DFacts m adp a.used x (a.digit x) :=
      { rd := ⟨by have := hd.lo_ge; omega, by have := hd.hi_le; omega, by have := hd.off; omega⟩
        arr := by have := hd.hi_le; omega
        d_v := by simpa [Layout.sizeofDigit] using hP.ra_.digits x (by omega)
        d_lt := by omega
        x_lt := h3
        r_lt := hb }
    by_cases hz : a.digit x = 0
    · have hx : x + 1 ≠ a.used := fun h => htop (by rw [← h, Nat.add_sub_cancel]; exact hz)
      rw [hz] at hf
      refine Triple.seq (skip_step ra v outp m hc adp a.used x hf hx) ?_
      exact ih (x + 1) (by omega) (by omega) fun j hj => by
        rcases Nat.lt_or_ge j x with h | h
        · exact h4 j h
        · rw [show j = x by omega]; exact hz
    · have hfz := firstNz_eq a.digit x h4 hz a.used h3
      have e : cntLsb a = 28 * x + (if a.digit x % 2 = 1 then 0 else lsbInner (a.digit x)) := by
        simp only [cntLsb, show a.used ≠ 0 by omega, ↓reduceIte, hfz, Layout.digitBits]
      rw [e]
      refine Triple.seq (found_step ra v outp m hc adp a.used x _ hf hz) ?_
      by_cases hodd : a.digit x % 2 = 1
      · simp only [hodd, ↓reduceIte, Nat.add_zero]
        exact odd_step ra v outp m hc hra _ _ hodd
      · simp only [hodd, ↓reduceIte]
        have hlt := lsbInner_lt 7 (a.digit x) hz (by omega)
        refine Triple.seq (even_step ra v outp m hc _ _ (by omega)) ?_
        exact inner ra v outp m hc hP.img.rodata hra _ _ _ (Nat.le_refl _) hz (by omega) (by omega)

/-- **`mp_cnt_lsb` on the machine.** -/
theorem correct : Api.CntLsb.Statement := by
  intro m v outp pa adp a ra hP
  have hc := hP.img.mpCntLsb
  have hal := hP.va.alloc_lt; have hul := hP.va.used_le
  have hu : UFacts m pa a.used := UFacts.of hP.ra_ hP.ga hP.va.toShape
  show Triple _ (At ra (retL ra (BitVec.ofNat 64 (cntLsb a))) m v.keep outp)
  by_cases h0 : a.used = 0
  · rw [show cntLsb a = 0 by simp [cntLsb, h0]]
    rw [h0] at hu
    exact zero_step ra v outp m hc pa hP.ra_al hu
  refine Triple.seq (enter_step ra v outp m hc pa adp a.used hu (by omega)
    (by simpa [Layout.offDp] using hP.ra_.dpv)) ?_
  exact outer ra v outp pa adp a m hP (by omega) a.used 0 (by omega) (by omega) (fun j hj => by omega)

end Tom.Machine.Fn.CntLsb
