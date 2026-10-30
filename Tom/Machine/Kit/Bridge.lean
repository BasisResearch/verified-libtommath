import Tom.Machine.Kit.Run

/-!
# One contract restated over another's region names

Two contracts of the same machine function with the same regions in two types, related by a
renaming `f : R' → R` with equal layouts and kinds (`cases r <;> rfl`): the entry hypotheses go from
the first to the second (`Entry.pull`) and the allocating post back (`HPost.rename`). Before, each
bridge in `Fn/GrowH.lean` re-proved both (soundness, bundle, offsets; the post's seven fields).
-/

namespace Tom.Machine

open Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

section
variable {R R' : Type} [DecidableEq R] [DecidableEq R'] {lay : R → Iv} {lay' : R' → Iv}

/-- **The entry hypotheses along a renaming**: soundness, the witness bundle and the offsets. -/
theorem Entry.pull {isW : R → Bool} {isW' : R' → Bool} {kind : R → Kind} {kind' : R' → Kind} {m : Mem}
    {H : List (Nat × Nat)} (f : R' → R) (all : List R') (hall : ∀ r, r ∈ all) (hl : ∀ r, lay' r = lay (f r))
    (hk : ∀ r, kind' r = kind (f r)) (hS : Sound lay isW) (hB : Bundle lay kind m) (hoff : ∀ r, Off (lay r) H)
    (hsep : SepPres isW isW' f all = true := by decide) :
    Sound lay' isW' ∧ Bundle lay' kind' m ∧ ∀ r, Off (lay' r) H :=
  ⟨Sound.pull f all hall hS (fun r => by rw [hl]; exact Iv.sub_self _) hsep,
   Bundle.pull f hB (fun r => by rw [hl]; exact Iv.sub_self _) hk (fun r => by rw [hl, hk]; exact (hB _).1),
   fun r => by rw [hl]; exact hoff _⟩

/-- **An allocating post along a renaming** (the written names' images written, every written name
an image). -/
theorem HPost.rename {ws : List R} {ws' : List R'} {site : R} {site' : R'} {out : R → Kind} {out' : R' → Kind}
    {J : Iv} {hin hout : List (Nat × Nat)} {m M : Mem} (f : R' → R) (hl : ∀ r, lay' r = lay (f r))
    (hs : f site' = site) (ho : ∀ r, out' r = out (f r)) (h1 : ∀ r ∈ ws', f r ∈ ws)
    (h2 : ∀ r ∈ ws, r ≠ site → ∃ r' ∈ ws', r' ≠ site' ∧ f r' = r)
    (h : HPost lay' ws' site' out' J hin hout m M) : HPost lay ws site out J hin hout m M := by
  subst hs
  refine { wit := fun r hr hne => ?_, wsite := ?_, place := ?_, frame := ?_, heap := h.heap, foot := ?_, off := h.off }
  · obtain ⟨r', hr', hne', rfl⟩ := h2 r hr hne
    rw [← hl, ← ho]; exact h.wit r' hr' hne'
  · rw [← ho]; exact h.wsite
  · rw [← hl]; exact h.place
  · intro x hx
    exact h.frame x fun hx' => hx (by
      rcases hx' with hx' | hx'
      · obtain ⟨w, hw, hxw⟩ := hx'.exists
        exact .inl (InAny.of_mem (h1 w hw) (by rw [← hl]; exact hxw))
      · exact .inr hx')
  · intro a ha; rw [← hl]; exact h.foot a ha

end

end Tom.Machine
