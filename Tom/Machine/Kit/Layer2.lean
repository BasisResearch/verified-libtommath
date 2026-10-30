import Tom.Machine.Kit.DOut
import Tom.Machine.Api.StdHeap

/-!
# Two re-placed sites over a layout

A function whose destination `x` (a contract region, re-placed by growing in-place callees) and a
heap temporary `q` (an allocation site) both move lays them as two layers over its entry layout,
`Iv.upd (Iv.upd ρ xD ⟨xq, …⟩) qD ⟨q, …⟩` (`mp_reduce`, `experiments/asm/mred.asm.json`). These
equations move a state's layout to a cut's when a call put a third layer on (`upd_qq`: `q` again,
`upd_xs`: `x` under `q`'s layer), when the entry has none (`upd_ins`), or when an allocation is
restated (`upd_k`); `pl_next`: the destination's placement after a call re-placed it with another
block behind it (`Place.trans`); `stk_sub`: a callee's stack below the own frame.
-/

namespace Tom.Machine

open Tom.Machine Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std

variable {ι : Type} [DecidableEq ι]

theorem upd_ins {ρ : ι → Iv} {s t : ι} {K J J' : Iv} (h : ρ s = K) (hJ : J = J') :
    ∀ r, Iv.upd ρ t J r = Iv.upd (Iv.upd ρ s K) t J' r := fun r => by
  subst hJ; unfold Iv.upd
  by_cases h1 : r = t
  · simp [h1]
  · by_cases h2 : r = s
    · subst h2; simp [h1, h]
    · simp [h1, h2]

theorem upd_k {ρ : ι → Iv} {s t : ι} {K K' J J' : Iv} (hK : K = K') (hJ : J = J') :
    ∀ r, Iv.upd (Iv.upd ρ s K) t J r = Iv.upd (Iv.upd ρ s K') t J' r := fun r => by subst hK hJ; rfl

theorem upd_qq {ρ : ι → Iv} {s t : ι} {K K' J J' J'' : Iv} (hK : K = K') (hJ : J' = J'') :
    ∀ r, Iv.upd (Iv.upd (Iv.upd ρ s K) t J) t J' r = Iv.upd (Iv.upd ρ s K') t J'' r := fun r => by
  subst hK hJ; unfold Iv.upd; split <;> rfl

theorem upd_xs {ρ : ι → Iv} {s t : ι} {K J J' K' K'' : Iv} (hst : s ≠ t) (hK : K' = K'') (hJ : J = J') :
    ∀ r, Iv.upd (Iv.upd (Iv.upd ρ s K) t J) s K' r = Iv.upd (Iv.upd ρ s K'') t J' r := fun r => by
  subst hK hJ; unfold Iv.upd
  by_cases h1 : r = s
  · subst h1; simp [hst]
  · simp [h1]

/-- The destination's placement after a call re-placed it (its block in front of another). -/
theorem pl_next {dp : Nat} {a : MpInt} {H : List (Nat × Nat)} {J K : Iv} {e : Nat × Nat}
    (h1 : Place ((dp, 4 * a.alloc) :: H) ⟨dp, 4 * a.alloc⟩ J) (h2 : Place ((J.base, J.len) :: e :: H) J K) :
    Place ((dp, 4 * a.alloc) :: H) ⟨dp, 4 * a.alloc⟩ K :=
  Place.trans (I0 := ⟨dp, 4 * a.alloc⟩) h1 (fun _ h => List.mem_cons_of_mem _ h) h2

/-- A callee's stack below the frame: `StkRes` at `sp - k`. -/
theorem stk_sub {sp F F' k : Nat} (h : StkRes sp F) (hF : F' + k ≤ F) (hk : k % 16 = 0) : StkRes (sp - k) F' := by
  have := h.lo; have := h.al; have := h.hi
  exact ⟨by omega, by omega, by omega⟩

end Tom.Machine
