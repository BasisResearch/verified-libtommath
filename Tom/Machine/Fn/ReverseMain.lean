import Tom.Machine.Fn.Reverse
import Tom.Machine.Api.Reverse
import Tom.Machine.Api.Bin
import Tom.Machine.Kit.MemStore

/-!
# `s_mp_reverse` on the machine: the whole function

`len = 1`: one chain. Otherwise the loop from `k = 0` by induction on
`len - 2k`, the array holding `revPart l len k` (`Tom/Spec/ByteRev.lean`)
at the head; each iteration's two byte stores are read back by
`getElem?_applyW_sb`, the frame by `Frm.store`, the code by `Frm.keep`.
-/

namespace Tom.Machine.Fn.Reverse

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api
open Tom.Machine.Api.Reverse (R)

theorem sbData_zext (b : BitVec 8) : sbData (zero_extend (m := 64) b) = b := by
  apply BitVec.eq_of_toNat_eq
  simp [sbData, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, Nat.mod_eq_of_lt b.isLt]

/-- A byte after the two stores of `swapLog`. -/
theorem getD_swap (M : Mem) (s n k x : Nat) :
    ((writeLog M (swapLog M s n k))[x]?).getD 0 =
      if x = s + (n - 1 - k) then (M[s + k]?).getD 0
      else if x = s + k then (M[s + (n - 1 - k)]?).getD 0 else (M[x]?).getD 0 := by
  rw [show writeLog M (swapLog M s n k) =
      applyW (applyW M (s + k, 1, zero_extend (m := 64) ((M[s + (n - 1 - k)]?).getD 0)))
        (s + (n - 1 - k), 1, zero_extend (m := 64) ((M[s + k]?).getD 0)) from rfl]
  rw [getElem?_applyW_sb, getElem?_applyW_sb]
  by_cases h1 : x = s + (n - 1 - k)
  · simp only [h1, ↓reduceIte, Option.getD_some, sbData_zext]
  · by_cases h2 : x = s + k
    · simp only [h2, ↓reduceIte, sbData_zext]
      split <;> rfl
    · simp only [h1, h2, ↓reduceIte]

section
variable {m : Mem} {s : Nat} {l : List (BitVec 8)} {ra : BitVec 64}

local notation "ρ" => Reverse.lay s l.length

/-- The loop state at `ix = k`. -/
structure Inv (m : Mem) (s : Nat) (l : List (BitVec 8)) (k : Nat) (M : Mem) : Prop where
  frame : Frm (Reverse.lay s l.length) [R.arr] m M
  bytes : ∀ i, i < l.length → (M[s + i]?).getD 0 = revPart (fun j => l.getD j 0) l.length k i

theorem loop (v : Abi) (outp : Array String) (hP : Reverse.Pre m s l ra) :
    ∀ d k M, l.length ≤ 2 * k + d → k < l.length - 1 - k → Inv m s l k M →
      Triple (At 0x8000453c#64 (headL ra s l.length k) M v.keep outp) (Reverse.Ret m v outp s l ra) := by
  have hcode := hP.lay.sub (r := R.arr) (s := R.code) (Iv.sub_self _) (Bin.sub_text (b := sMpReverseBase) (k := 60))
  simp only [Iv.Disj, Disj, Reverse.lay] at hcode
  have hf : AFacts s l.length := { rs := hP.rs, n_pos := hP.n_pos, code_off := by omega }
  intro d
  induction d with
  | zero => intro k M h1 h2; omega
  | succ d ih =>
    intro k M h1 h2 hI
    have hc := (hI.frame.keep hP.lay (Img.reads (r := R.code) (Iv.sub_self _)) hP.img).sMpReverse
    have hF : Frm ρ [R.arr] M (writeLog M (swapLog M s l.length k)) :=
      Frm.store (by simp only [LogIn, swapLog, Iv.Sub, Reverse.lay, and_true]; omega)
    have hb : ∀ i, i < l.length → ((writeLog M (swapLog M s l.length k))[s + i]?).getD 0 =
        revPart (fun j => l.getD j 0) l.length (k + 1) i := by
      intro i hi
      rw [getD_swap, revPart_step _ _ _ _ h2, hI.bytes k (by omega), hI.bytes (l.length - 1 - k) (by omega)]
      have e1 : revPart (fun j => l.getD j 0) l.length k k = l.getD k 0 := by
        unfold revPart; split <;> first | rfl | omega
      have e2 : revPart (fun j => l.getD j 0) l.length k (l.length - 1 - k) = l.getD (l.length - 1 - k) 0 := by
        unfold revPart; split <;> first | rfl | omega
      rw [e1, e2]
      by_cases h3 : i = l.length - 1 - k
      · simp only [h3, ↓reduceIte]
      · by_cases h4 : i = k
        · simp only [show ¬ s + k = s + (l.length - 1 - k) by omega,
          show ¬ k = l.length - 1 - k by omega, h4, ↓reduceIte]
        · simp only [show ¬ s + i = s + (l.length - 1 - k) by omega, show ¬ s + i = s + k by omega, h3, h4,
            ↓reduceIte]
          exact hI.bytes i hi
    by_cases hk1 : k + 1 < l.length - 1 - (k + 1)
    · refine Triple.seq (next_step ra v outp s l.length hf M hc k h2 hk1) ?_
      exact ih (k + 1) _ (by omega) hk1 ⟨(hI.frame.trans hF).mono, hb⟩
    · refine Triple.rmap (fun cf h => ⟨_, h, ?_, (hI.frame.trans hF).mono⟩)
        (exit_step ra v outp s l.length hf M hc hP.ra_al k h2 hk1)
      intro i hi
      rw [List.length_reverse] at hi
      rw [hb i hi, revPart_done _ _ _ _ hk1 hi, reverse_getD _ _ _ hi]

end

/-- **`s_mp_reverse` on the machine.** -/
theorem correct : Api.Reverse.Statement := by
  intro m v outp s l ra hP
  have hcode := hP.lay.sub (r := R.arr) (s := R.code) (Iv.sub_self _) (Bin.sub_text (b := sMpReverseBase) (k := 60))
  simp only [Iv.Disj, Disj, Reverse.lay] at hcode
  have hf : AFacts s l.length := { rs := hP.rs, n_pos := hP.n_pos, code_off := by omega }
  have hc := hP.img.sMpReverse
  by_cases h1 : l.length = 1
  · refine Triple.rmap (fun cf h => ⟨m, h, ?_, Frm.refl _ m⟩) (one_step ra v outp s l.length hf m hc hP.ra_al h1)
    intro i hi
    rw [List.length_reverse] at hi
    rw [reverse_getD _ _ _ hi, hP.bytes i hi, show l.length - 1 - i = i by omega]
  refine Triple.seq (enter_step ra v outp s l.length hf m hc (by have := hP.n_pos; omega)) ?_
  exact loop v outp hP l.length 0 m (by omega) (by have := hP.n_pos; omega)
    ⟨Frm.refl _ m, fun i hi => by rw [revPart_zero _ _ _ hi]; exact hP.bytes i hi⟩

end Tom.Machine.Fn.Reverse
