import Tom.Machine.Kit.Frame

/-!
# In-place array loops from the top down

`Kit/Frame.lean`'s `ovl g old i` is the overlay of a loop that counts up
(`g` below `i`). A loop that counts down from `u - 1` to `0` (`mp_div_2`,
`mp_rshd`, …) has written `[x, u)` when it is at `x`: `ovlD g old x u`.
`ArrFrm.stepD`/`ASt.storeD` are its store rule: one `sw` of `g x` at
element `x` takes `ovlD g old (x + 1) u` to `ovlD g old x u`.
-/

namespace Tom.Machine

open Vsa.Sim

/-- `g` on `[x, u)`, `old` elsewhere. -/
def ovlD (g old : Nat → Nat) (x u : Nat) : Nat → Nat := fun j => if x ≤ j ∧ j < u then g j else old j

theorem ovlD_top (g old : Nat → Nat) (u : Nat) : ovlD g old u u = old := by
  funext j; simp only [ovlD]; rw [if_neg (by omega)]

theorem ovlD_zero (g old : Nat → Nat) (u : Nat) : ovlD g old 0 u = ovl g old u := by
  funext j; simp only [ovlD, ovl, Nat.zero_le, true_and]

variable {ι : Type} {ρ : ι → Iv}

/-- **The top-down overlay law**, one store: `g x` at element `x`. -/
theorem ArrFrm.stepD [DecidableEq ι] {w : ι} {m0 M : Mem} {b n x u v : Nat} {g old : Nat → Nat}
    (h : ArrFrm ρ w m0 M b n (ovlD g old (x + 1) u)) (hx : x < n) (hxu : x < u) (hv : v < 2 ^ 32)
    (hgv : v = g x) :
    ArrFrm ρ w m0 (writeLog M [(b + 4 * x, 4, BitVec.ofNat 64 v)]) b n (ovlD g old x u) :=
  { rgn := h.rgn
    fr := Frm.step h.fr (Frm.sw (w := w) (by have := h.rgn; unfold Iv.Sub at *; simp only at *; omega))
      (by simp [SubN])
    arr := (h.arr.set x v hv).congr fun j _ => by
      simp only [ovlD]
      by_cases hj : j = x
      · subst hj; simp [hgv, hxu]
      · rw [if_neg hj]
        by_cases hl : x + 1 ≤ j ∧ j < u
        · rw [if_pos hl, if_pos (by omega)]
        · rw [if_neg hl, if_neg (by omega)] }

open Vsa.Logic in
/-- A segment that stores `g x` into element `x` of a top-down loop. -/
theorem ASt.storeD [DecidableEq ι] {w : ι} {m0 : Mem} {b n x u v : Nat} {keep : GRegs}
    {outp : Array String} {pc pc' : BitVec 64} {L L' : GRegs} {g old : Nat → Nat}
    (h : ∀ M, ArrFrm ρ w m0 M b n (ovlD g old (x + 1) u) → Triple (At pc L M keep outp)
      (At pc' L' (writeLog M [(b + 4 * x, 4, BitVec.ofNat 64 v)]) keep outp))
    (hx : x < n) (hxu : x < u) (hgv : v = g x) (hv : v < 2 ^ 32) :
    Triple (ASt ρ w m0 b n keep outp pc L (ovlD g old (x + 1) u))
      (ASt ρ w m0 b n keep outp pc' L' (ovlD g old x u)) :=
  fun c ⟨M, hI, hc⟩ => Triple.rmap (fun _ h => ⟨_, hI.stepD hx hxu hv hgv, h⟩) (h M hI) c hc

end Tom.Machine
