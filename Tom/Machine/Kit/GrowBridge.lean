import Tom.Machine.Kit.Bridge

/-!
# A growing contract read as values, once

The growing contracts (`Api/MpAddG*.lean`, `Api/MpSubG.lean`, …) end in
`∃ x : Option (q, x'), …` with the branch posts over the grown input (`AddG`, `SubG`); their
callers' named premises (`Api/MpAddH*.lean`, `Api/MpSubH.lean`) state the same
call with result `(ok, q, x')` and the value: shaped, live, placed, grown only, on `MP_OKAY`
valid with value `V`. `GrowPost.val` turns the first post into the second for any such pair:
the regions along a renaming `f` (`HPost.rename`; `fun r => r` for the same region type), the
result by `gX dp c0` (`none` ↦ `(false, dp, c0)`: the destination at its old block as the code
left it; `some (q, x')` ↦ `(true, q, x')`), the value from a `.spec` of the branch posts (`hv`),
and the caller's `Out` from the generic `VOut` (`hQ`, the same six fields). The equations
between the two contracts' `out`/`site'`/`hout`/`rets` hold case by case by `rfl` (`grow_rfl`).
-/

namespace Tom.Machine

open Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- A grow6-style result as `(ok, q, x')`. -/
def gX (dp : Nat) (c0 : MpInt) : Option (Nat × MpInt) → Bool × Nat × MpInt
  | none => (false, dp, c0)
  | some (q, x) => (true, q, x)

/-- What an `…H` contract's `Out` says of the destination (`y = (ok, q, x')`). -/
structure VOut (H : List (Nat × Nat)) (I : Iv) (n0 : Nat) (V : Int) (J : Iv) (y : Bool × Nat × MpInt) : Prop where
  shape : y.2.2.Shape
  pos : 0 < y.2.2.alloc
  place : Place H I J
  grow : n0 ≤ y.2.2.alloc
  valid : y.1 = true → y.2.2.Valid
  val : y.1 = true → y.2.2.val = V

/-- The two contracts' result maps agree case by case. -/
macro "grow_rfl" : tactic => `(tactic| (intro x; rcases x with _ | ⟨_, _⟩ <;> (try (intro r; cases r)) <;> rfl))

/-- **A growing contract's post read as values** (see the module doc). -/
theorem GrowPost.val {R R' : Type} [DecidableEq R] [DecidableEq R'] {lay : R → Iv} {lay' : R' → Iv}
    {ws : List R} {ws' : List R'} {s : R} {s' : R'}
    {outH : Bool × Nat × MpInt → R → Kind} {outG : Option (Nat × MpInt) → R' → Kind}
    {siteH : Bool × Nat × MpInt → Iv} {siteG : Option (Nat × MpInt) → Iv}
    {houtH : Bool × Nat × MpInt → List (Nat × Nat)} {houtG : Option (Nat × MpInt) → List (Nat × Nat)}
    {retsH : Bool × Nat × MpInt → Vsa.Sim.GRegs} {retsG : Option (Nat × MpInt) → Vsa.Sim.GRegs}
    {QH : Bool × Nat × MpInt → Prop} {QG : Option (Nat × MpInt) → Prop}
    {hin : List (Nat × Nat)} {m : Mem} {ra : BitVec 64} {K : Vsa.Sim.GRegs} {o : Array String}
    {cf : Vsa.Machine.Config} {n0 : Nat} {V : Int}
    (f : R' → R) (dp : Nat) (c0 : MpInt) (h0 : c0.Shape ∧ 0 < c0.alloc ∧ n0 ≤ c0.alloc) (hn0 : 0 < n0)
    (hv : ∀ q x, QG (some (q, x)) → x.Valid ∧ x.val = V ∧ n0 ≤ x.alloc)
    (hQ : ∀ y, VOut hin (lay s) n0 V (siteH y) y → QH y)
    (h : ∃ x M, At ra (retsG x) M K o cf ∧ QG x ∧ HPost lay' ws' s' (outG x) (siteG x) hin (houtG x) m M)
    (hl : ∀ r, lay' r = lay (f r) := by intro r; cases r <;> rfl) (hs : f s' = s := by rfl)
    (ho : ∀ x r, outG x r = outH (gX dp c0 x) (f r) := by grow_rfl)
    (hsite : ∀ x, siteG x = siteH (gX dp c0 x) := by grow_rfl)
    (hhout : ∀ x, houtG x = houtH (gX dp c0 x) := by grow_rfl)
    (hrets : ∀ x, retsG x = retsH (gX dp c0 x) := by grow_rfl)
    (h1 : ∀ r ∈ ws', f r ∈ ws := by decide)
    (h2 : ∀ r ∈ ws, r ≠ s → ∃ r' ∈ ws', r' ≠ s' ∧ f r' = r := by decide) :
    ∃ x M, At ra (retsH x) M K o cf ∧ QH x ∧ HPost lay ws s (outH x) (siteH x) hin (houtH x) m M := by
  obtain ⟨x, M, hat, hq, hp⟩ := h
  have hp' := hp.rename f hl hs (ho x) h1 h2
  rw [hsite, hhout] at hp'
  refine ⟨gX dp c0 x, M, hrets x ▸ hat, hQ _ ?_, hp'⟩
  have hpl := hp'.place
  rcases x with _ | ⟨q, y⟩
  · exact ⟨h0.1, h0.2.1, hpl, h0.2.2, fun h => absurd h Bool.false_ne_true, fun h => absurd h Bool.false_ne_true⟩
  · obtain ⟨hvv, hvl, hg⟩ := hv q y hq
    exact ⟨hvv.toShape, by simp only [gX]; omega, hpl, hg, fun _ => hvv, fun _ => hvl⟩

end Tom.Machine
