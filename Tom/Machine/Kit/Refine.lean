import Tom.Machine.Kit.Frame

/-!
# Callee layouts by refinement

`Sound.pull` renames a callee's regions into the caller's when every two
names the callee keeps apart go to two names the caller keeps apart. A
caller that passes a pointer into its own stack frame (`mp_add_d` calling
`mp_sub_d` on a stack copy of `a`) needs a finer layout of its own: its
stack name split into pieces (the callee's stack, the copy, the rest of the
frame). `Sound.refine` builds that finer layout's soundness from the coarse
one: pieces of one coarse name are kept apart by their own placement
(`hsame`, symbolic arithmetic on the pieces), pieces of distinct coarse
names by the coarse layout (closed: `decide`).
-/

namespace Tom.Machine

section
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

/-- **Sound by refinement**: `σ`'s names sit inside `ρ`'s via `g`; two
`Sep` names of `σ` whose images are not `Sep` in `ρ` are disjoint by `hsame`. -/
theorem Sound.refine {ρ : ι → Iv} {isW : ι → Bool} {σ : κ → Iv} {isW' : κ → Bool} (g : κ → ι)
    (hS : Sound ρ isW) (hsub : ∀ k, (σ k).Sub (ρ (g k)))
    (hsame : ∀ k l, Sep isW' k l = true → Sep isW (g k) (g l) = false → (σ k).Disj (σ l)) :
    Sound σ isW' := by
  intro k l h
  cases hs : Sep isW (g k) (g l)
  · exact hsame k l h hs
  · have hd := hS _ _ hs
    have h1 := hsub k; have h2 := hsub l
    unfold Iv.Disj Tom.Machine.Disj Iv.Sub at *; omega

end

end Tom.Machine
