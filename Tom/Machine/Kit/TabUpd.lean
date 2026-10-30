import Tom.Machine.Kit.TabState

/-!
# A region beside the table re-placed

`Kit/TabState.lean` states a cut's layout as `tLay G ρ T rI` (the table's and `res`'s digit arrays
placed over a base layout `ρ`). A call that places another region `s` (`mp_init(&mu)`, a setup
growing `mu`) leaves `Iv.upd (tLay G ρ T rI) s J`: the same table over the base layout with `s` at
`J` (`tLay_upd`), so the next call on a table entry finds `tLay` on top again.
-/

namespace Tom.Machine

section
variable {ι : Type} [DecidableEq ι]

/-- **A region off the table re-placed**: into the base layout. -/
theorem tLay_upd (G : TabSig ι) (ρ : ι → Iv) (T : Nat → Option (Nat × MpInt)) (rI : Option (Nat × MpInt))
    {s : ι} (hs : G.famD s = none) (hs' : s ≠ G.rD) (J : Iv) :
    ∀ r, Iv.upd (tLay G ρ T rI) s J r = tLay G (Iv.upd ρ s J) T rI r := by
  intro r
  unfold Iv.upd tLay
  by_cases e : r = s
  · subst e; simp [hs, hs']
  · cases h : G.famD r <;> simp [e]

/-- **The region re-placed again** (a growing call on it): the base layout's last placement wins. -/
theorem tLay_upd2 (G : TabSig ι) (ρ : ι → Iv) (T : Nat → Option (Nat × MpInt)) (rI : Option (Nat × MpInt))
    {s : ι} (hs : G.famD s = none) (hs' : s ≠ G.rD) (J0 J : Iv) :
    ∀ r, Iv.upd (tLay G (Iv.upd ρ s J0) T rI) s J r = tLay G (Iv.upd ρ s J) T rI r := by
  intro r
  rw [tLay_upd G _ T rI hs hs' J r]
  unfold tLay
  cases G.famD r
  · simp only [Iv.upd]; split <;> simp_all
  · rfl

/-- **The region given back** (`mp_clear` of it, its placement `Iv.nil` the base layout's). -/
theorem tLay_back (G : TabSig ι) (ρ : ι → Iv) (T : Nat → Option (Nat × MpInt)) (rI : Option (Nat × MpInt))
    {s : ι} (hs : G.famD s = none) (hs' : s ≠ G.rD) (J0 J : Iv) (hJ : ρ s = J) :
    ∀ r, Iv.upd (tLay G (Iv.upd ρ s J0) T rI) s J r = tLay G ρ T rI r := by
  intro r
  rw [tLay_upd2 G ρ T rI hs hs' J0 J r]
  unfold tLay
  cases G.famD r
  · simp only [Iv.upd]; split <;> simp_all
  · rfl

end

section
variable {ι : Type} [DecidableEq ι] {κR : Type}

/-- **A call off the table** (its written regions none of the table's or `res`'s): its kinds go under
`tKind`, so the table's kinds stay `tKind`'s for the next call on an entry. -/
theorem pushH_tKind {G : TabSig ι} {σ : κR → ι} {ws : List κR} {κ : ι → Kind} {κc : κR → Kind}
    {b pr : Nat} {T : Nat → Option (Nat × MpInt)} {rS rI : Option (Nat × MpInt)}
    (hoff : ∀ k ∈ ws, G.famS (σ k) = none ∧ G.famD (σ k) = none ∧ σ k ≠ G.rS ∧ σ k ≠ G.rD) :
    ∀ r, Kind.pushH σ ws (tKind G κ b pr T rS rI) κc r = tKind G (Kind.pushH σ ws κ κc) b pr T rS rI r := by
  intro r
  unfold Kind.pushH
  cases hf : ws.find? (fun k => decide (σ k = r)) with
  | some k =>
    have hk := List.mem_of_find?_eq_some hf
    have hr : σ k = r := by have := List.find?_some hf; simpa using this
    obtain ⟨h1, h2, h3, h4⟩ := hoff k hk
    rw [hr] at h1 h2 h3 h4
    show κc k = tKind G _ b pr T rS rI r
    rw [tKind_other h1 h2 h4 h3]; simp only [hf]
  | none =>
    show tKind G κ b pr T rS rI r = tKind G _ b pr T rS rI r
    unfold tKind
    cases G.famS r <;> cases G.famD r <;> simp only [hf]

end

/-- **Entry `x`'s block to the front** (a growing call on `M[x]`), the table behind it with `x` dead. -/
theorem heap_out (one : Bool) (Q : Nat → Nat) (V : Nat → MpInt) {lo hi x : Nat} (rB R : List (Nat × Nat))
    (h1 : lo ≤ x) (h2 : x < hi) :
    (rB ++ (tabBlks (tabV one Q V lo hi) lo (hi - lo) ++ R)).Perm
      ((Q x, 4 * (V x).alloc) :: (rB ++ (tabBlks (tset (tabV one Q V lo hi) x none) lo (hi - lo) ++ R))) := by
  have := tab_front rB R (tabV one Q V lo hi) lo (hi - lo) x h1 (by omega)
  rw [tabV_live h1 h2] at this; exact this

/-- **Entry `x`'s new block back** (the call re-placed it at `q`, value `v`). -/
theorem heap_back (one : Bool) (Q : Nat → Nat) (V : Nat → MpInt) {lo hi x : Nat} (rB R : List (Nat × Nat))
    (q : Nat) (v : MpInt) (h1 : lo ≤ x) (h2 : x < hi) :
    ((q, 4 * v.alloc) :: (rB ++ (tabBlks (tset (tabV one Q V lo hi) x none) lo (hi - lo) ++ R))).Perm
      (rB ++ (tabBlks (tabV one (qset Q x q) (vset V x v) lo hi) lo (hi - lo) ++ R)) := by
  have := tab_back rB R (tabV one Q V lo hi) lo (hi - lo) x h1 (by omega) (some (q, v))
  rw [tabV_set one Q V q v (.inr ⟨h1, h2⟩)] at this; exact this

theorem qset_eq (Q : Nat → Nat) (x q : Nat) : qset Q x q x = q := by simp [qset]
theorem vset_eq (V : Nat → MpInt) (x : Nat) (v : MpInt) : vset V x v x = v := by simp [vset]
-- `vset_ne`, `qset_qset`, `vset_vset`: in `Kit/TabState.lean`.

/-- Entry `x` killed: its block and value before do not matter. -/
theorem tset_tabV_set (one : Bool) (Q : Nat → Nat) (V : Nat → MpInt) (lo hi x q : Nat) (v : MpInt) :
    tset (tabV one (qset Q x q) (vset V x v) lo hi) x none = tset (tabV one Q V lo hi) x none := by
  funext j; simp only [tset, tabV, qset, vset]; split <;> simp_all

/-- The values' allocations positive after one is re-set to a positive one. -/
theorem vset_pos {V : Nat → MpInt} {x : Nat} {v : MpInt} (hV : ∀ j, 0 < (V j).alloc) (hv : 0 < v.alloc) :
    ∀ j, 0 < (vset V x v j).alloc := fun j => by
  unfold vset; split
  · exact hv
  · exact hV j

/-! ## After `mp_exch(&res, Y)`: `Y`'s old block given back, then the table's (the result's block in front) -/

section
variable {ι : Type} [DecidableEq ι]

/-- **Another region given back under a placed one** (`mp_clear(&res)` holding `Y`'s old value, `mu`
still placed): the two placements commute into the base layout. -/
theorem tLay_upd_swap (G : TabSig ι) (ρ : ι → Iv) (T : Nat → Option (Nat × MpInt)) (rI : Option (Nat × MpInt))
    {a b : ι} (hb : G.famD b = none) (hb' : b ≠ G.rD) (hab : a ≠ b) (A B : Iv) :
    ∀ r, Iv.upd (tLay G (Iv.upd ρ a A) T rI) b B r = tLay G (Iv.upd (Iv.upd ρ b B) a A) T rI r := by
  intro r
  rw [tLay_upd G _ T rI hb hb' B r]
  have e : Iv.upd (Iv.upd ρ a A) b B = Iv.upd (Iv.upd ρ b B) a A := by
    funext x; simp only [Iv.upd]; split <;> split <;> simp_all
  rw [e]

end

/-- `Y`'s old block (the last before the caller's) to the front. -/
theorem heap_y_front (a b c d : Nat × Nat) (T H : List (Nat × Nat)) :
    (a :: b :: (T ++ c :: d :: H)).Perm (d :: a :: b :: (T ++ c :: H)) := by
  have := List.perm_middle (l₁ := a :: b :: (T ++ [c])) (a := d) (l₂ := H)
  simpa using this

/-- `M[1]`'s block to the front behind the result's `c`. -/
theorem heap_m1c (Q : Nat → Nat) (V : Nat → MpInt) {lo hi k : Nat} (e c : Nat × Nat) (R : List (Nat × Nat))
    (h1 : 1 < lo) :
    (c :: (tabBlks (tabV true Q V lo hi) lo k ++ (e :: R))).Perm
      (e :: c :: (tabBlks (tabV false Q V lo hi) lo k ++ R)) :=
  ((heap_m1 Q V e R h1).cons c).trans (List.Perm.swap e c _)

/-- The table's first block to the front behind the result's `c`. -/
theorem heap_frontc (one : Bool) (Q : Nat → Nat) (V : Nat → MpInt) {lo hi : Nat} (c : Nat × Nat)
    (R : List (Nat × Nat)) (h : lo < hi) :
    (c :: (tabBlks (tabV one Q V lo hi) lo (hi - lo) ++ R)).Perm
      ((Q lo, 4 * (V lo).alloc) :: c :: (tabBlks (tabV one Q V (lo + 1) hi) (lo + 1) (hi - (lo + 1)) ++ R)) := by
  rw [heap_front one Q V R h]; exact List.Perm.swap _ _ _

end Tom.Machine
