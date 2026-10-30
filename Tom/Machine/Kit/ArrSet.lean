import Tom.Machine.Kit.Frame

/-!
# In-place array loops in any order

`ArrFrm.step`/`ASt.store` (`Kit/Frame.lean`) fix the overlay `ovl g old i`
of a loop counting up. `ArrFrm.set`/`ASt.set` store `v` at any element `k`
and take the new contents `f'` as `f` updated at `k` (`hf`): a loop counting
down (`mp_lshd`) states its own overlay.
-/

namespace Tom.Machine

open Vsa.Sim

variable {ι : Type} {ρ : ι → Iv}

/-- One store of `v` at element `k`. -/
theorem ArrFrm.set [DecidableEq ι] {w : ι} {m0 M : Mem} {b n k v : Nat} {f f' : Nat → Nat}
    (h : ArrFrm ρ w m0 M b n f) (hk : k < n) (hv : v < 2 ^ 32)
    (hf : ∀ j, j < n → f' j = if j = k then v else f j) :
    ArrFrm ρ w m0 (writeLog M [(b + 4 * k, 4, BitVec.ofNat 64 v)]) b n f' :=
  { rgn := h.rgn
    fr := Frm.step h.fr (Frm.sw (w := w) (by have := h.rgn; unfold Iv.Sub at *; simp only at *; omega))
      (by simp [SubN])
    arr := (h.arr.set k v hv).congr fun j hj => (hf j hj).symm }

open Vsa.Logic in
/-- A segment that stores `v` into element `k`. -/
theorem ASt.set [DecidableEq ι] {w : ι} {m0 : Mem} {b n k v : Nat} {keep : GRegs} {outp : Array String}
    {pc pc' : BitVec 64} {L L' : GRegs} {f f' : Nat → Nat}
    (h : ∀ M, ArrFrm ρ w m0 M b n f → Triple (At pc L M keep outp)
      (At pc' L' (writeLog M [(b + 4 * k, 4, BitVec.ofNat 64 v)]) keep outp))
    (hk : k < n) (hv : v < 2 ^ 32) (hf : ∀ j, j < n → f' j = if j = k then v else f j) :
    Triple (ASt ρ w m0 b n keep outp pc L f) (ASt ρ w m0 b n keep outp pc' L' f') :=
  fun c ⟨M, hI, hc⟩ => Triple.rmap (fun _ h => ⟨_, hI.set hk hv hf, h⟩) (h M hI) c hc

end Tom.Machine
