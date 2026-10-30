import Tom.Machine.Kit.Run

/-!
# A table of `mp_int`s in the own frame

`s_mp_exptmod(_fast)`'s `mp_int M[256]` is a family of regions indexed by a number: the structs
`M[j]` (24 bytes each in the own frame) and their digit arrays (heap blocks placed by
`mp_init_size(&M[j], …)` at run time, `2^(w-1)` of them for a window size `w` read from the
exponent). The region types of such a function have one constructor per family with the index as
its argument; the callees see one member at a time (σ maps a callee region to `tS x`), the
generator's decisions on names stay closed (`Sep` of two different constructors reduces).

* `Iv.spread`, `St.spread`, `HP.spread`: the table's frame piece (a hole of `24 n` bytes, laid out
  by `Split` like any frame piece) given to the family members `f j`, `j < n`, one 24-byte slot
  each; the hole is laid at `Iv.nil` from then on (at the entry, before any store into it).
* `tabBlks`: the heap blocks of the live entries `[lo, hi)` of a table `T : Nat → Option (Nat × MpInt)`
  (block address and value), and the permutations a call on one entry needs (`tabBlks_front`,
  `tabBlks_snoc`, `tabBlks_set`).
-/

namespace Tom.Machine

open Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

section
variable {ι : Type} {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind}

/-- The hole `h` emptied, the family member `r` (`fam r = some j`, `j < n`) at `b + 24 j`. -/
def Iv.spread [DecidableEq ι] (ρ : ι → Iv) (h : ι) (fam : ι → Option Nat) (b n : Nat) : ι → Iv := fun r =>
  match fam r with
  | some j => if j < n then ⟨b + 24 * j, 24⟩ else ρ r
  | none => if r = h then Iv.nil else ρ r

/-- What `spread` needs of the family and the hole. -/
structure SpreadOk (ρ : ι → Iv) (isW : ι → Bool) (κ : ι → Kind) (h : ι) (fam : ι → Option Nat)
    (b n : Nat) : Prop where
  inj : ∀ r r' j, fam r = some j → fam r' = some j → r = r'
  hole : fam h = none
  hlay : ρ h = ⟨b, 24 * n⟩
  hw : isW h = true
  fw : ∀ r j, fam r = some j → j < n → isW r = true
  fk : ∀ r j, fam r = some j → j < n → κ r = .ram
  lo : ∀ r, 0x80000000 ≤ (ρ r).base

theorem SpreadOk.slot_sub (hs : SpreadOk ρ isW κ h fam b n) {j : Nat} (hj : j < n) :
    Iv.Sub ⟨b + 24 * j, 24⟩ (ρ h) := by
  rw [hs.hlay]; unfold Iv.Sub; dsimp only; omega

theorem Iv.nil_disj {I : Iv} (h : 0x80000000 ≤ I.base) : Iv.nil.Disj I := by
  unfold Iv.Disj Tom.Machine.Disj Iv.nil; dsimp only; omega

variable [DecidableEq ι]

theorem Iv.spread_none {h : ι} {fam : ι → Option Nat} {b n : Nat} {r : ι} (hr : fam r = none) (hrh : r ≠ h) :
    Iv.spread ρ h fam b n r = ρ r := by
  simp [Iv.spread, hr, hrh]

theorem Iv.spread_hole {h : ι} {fam : ι → Option Nat} {b n : Nat} (hh : fam h = none) :
    Iv.spread ρ h fam b n h = Iv.nil := by
  simp [Iv.spread, hh]

/-- Every interval of the spread layout: a slot, the emptied hole, or the old interval. -/
theorem spread_cases (hs : SpreadOk ρ isW κ h fam b n) (r : ι) :
    (∃ j, fam r = some j ∧ j < n ∧ Iv.spread ρ h fam b n r = ⟨b + 24 * j, 24⟩) ∨
    (r = h ∧ Iv.spread ρ h fam b n r = Iv.nil) ∨
    (r ≠ h ∧ (∀ j, fam r = some j → n ≤ j) ∧ Iv.spread ρ h fam b n r = ρ r) := by
  cases hf : fam r with
  | some j =>
    by_cases hj : j < n
    · exact .inl ⟨j, rfl, hj, by simp [Iv.spread, hf, hj]⟩
    · have h1 : r ≠ h := fun e => by subst e; rw [hs.hole] at hf; cases hf
      have h2 : ∀ j', some j = some j' → n ≤ j' := fun j' e => by cases e; omega
      have h3 : Iv.spread ρ h fam b n r = ρ r := by simp [Iv.spread, hf, hj]
      exact .inr (.inr ⟨h1, h2, h3⟩)
  | none =>
    by_cases hr : r = h
    · exact .inr (.inl ⟨hr, by subst hr; simp [Iv.spread, hf]⟩)
    · have h2 : ∀ j', (none : Option Nat) = some j' → n ≤ j' := fun _ e => by cases e
      have h3 : Iv.spread ρ h fam b n r = ρ r := by simp [Iv.spread, hf, hr]
      exact .inr (.inr ⟨hr, h2, h3⟩)

theorem spread_lo (hs : SpreadOk ρ isW κ h fam b n) (r : ι) : 0x80000000 ≤ (Iv.spread ρ h fam b n r).base := by
  rcases spread_cases hs r with ⟨j, _, hj, e⟩ | ⟨_, e⟩ | ⟨_, _, e⟩ <;> rw [e]
  · have := hs.lo h; rw [hs.hlay] at this; dsimp only at this ⊢; omega
  · decide
  · exact hs.lo r

theorem spread_sound (hs : SpreadOk ρ isW κ h fam b n) (hS : Sound ρ isW) : Sound (Iv.spread ρ h fam b n) isW := by
  intro r t hrt
  have hne : r ≠ t := fun e => by subst e; simp [Sep] at hrt
  have hslo : 0x80000000 ≤ b := by have := hs.lo h; rw [hs.hlay] at this; exact this
  rcases spread_cases hs r with ⟨j, hfr, hj, er⟩ | ⟨hr, er⟩ | ⟨hr, _, er⟩
  · rw [er]
    rcases spread_cases hs t with ⟨j', hft, hj', et⟩ | ⟨ht, et⟩ | ⟨ht, _, et⟩
    · rw [et]
      have hjj : j ≠ j' := fun e => hne (hs.inj r t j hfr (e ▸ hft))
      unfold Iv.Disj Tom.Machine.Disj; dsimp only; omega
    · rw [et]; exact Disj.symm (Iv.nil_disj (by dsimp only; omega))
    · rw [et]; exact hS.sub (hs.slot_sub hj) (Iv.sub_self _) (by simp [Sep, hs.hw, Ne.symm ht])
  · rw [er]; exact Iv.nil_disj (spread_lo hs t)
  · rw [er]
    rcases spread_cases hs t with ⟨j', hft, hj', et⟩ | ⟨ht, et⟩ | ⟨ht, _, et⟩
    · rw [et]
      exact Disj.symm (hS.sub (hs.slot_sub hj') (Iv.sub_self _) (by simp [Sep, hs.hw, Ne.symm hr]))
    · rw [et]; exact Disj.symm (Iv.nil_disj (hs.lo r))
    · rw [et]; exact hS r t hrt

theorem spread_ne_hole (hs : SpreadOk ρ isW κ h fam b n) {r : ι} {j : Nat} (hf : fam r = some j) : r ≠ h :=
  fun e => by subst e; rw [hs.hole] at hf; cases hf

/-- **Spread the table's hole** in the state (at a checkpoint, before any store into it). -/
theorem St.spread (hs : SpreadOk ρ isW κ h fam b n) (hram : Ram (ρ h).base (ρ h).len)
    (hSt : St ρ isW W κ m m) : St (Iv.spread ρ h fam b n) isW W (Kind.set κ h .ram) m m := by
  refine ⟨spread_sound hs hSt.sound, fun r => ?_, Frm.refl _ _⟩
  rcases spread_cases hs r with ⟨j, hf, hj, e⟩ | ⟨hr, e⟩ | ⟨hr, _, e⟩
  · have hrh := spread_ne_hole hs hf
    rw [e]; simp only [Kind.set, hrh, hs.fk r j hf hj, if_false]
    have hsub := hs.slot_sub hj
    exact ⟨trivial, Ram.sub hram hsub.1 hsub.2⟩
  · subst hr; rw [e]; simp only [Kind.set, if_true]; exact ⟨trivial, Ram.nil⟩
  · rw [e]; simp only [Kind.set, hr, if_false]; exact hSt.wit r

/-- **Spread the table's hole** in the heap checkpoint. -/
theorem HP.spread {H0 H : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m : Mem} (hs : SpreadOk ρ isW κ h fam b n)
    (hp : HP ρ isW H0 H Wr0 m0 m) : HP (Iv.spread ρ h fam b n) isW H0 H Wr0 m0 m where
  heap := hp.heap
  frm0 := hp.frm0
  foot := hp.foot
  cov r hr a ha := by
    rcases spread_cases hs r with ⟨j, hf, hj, e⟩ | ⟨_, e⟩ | ⟨_, _, e⟩ <;> rw [e] at ha
    · have hsub := hs.slot_sub hj
      exact hp.cov h hs.hw a (by unfold Iv.Sub Iv.In at *; dsimp only at ha hsub; omega)
    · unfold Iv.In Iv.nil at ha; dsimp only at ha; omega
    · exact hp.cov r hr a ha
  off r := by
    rcases spread_cases hs r with ⟨j, hf, hj, e⟩ | ⟨_, e⟩ | ⟨_, _, e⟩ <;> rw [e]
    · exact (hp.off h).sub (hs.slot_sub hj) (.inl (show 0 < 24 by decide))
    · exact Off.nil _
    · exact hp.off r
  ram r hr := by
    rcases spread_cases hs r with ⟨j, hf, hj, e⟩ | ⟨_, e⟩ | ⟨_, _, e⟩ <;> rw [e]
    · have hsub := hs.slot_sub hj; exact Ram.sub (hp.ram h hs.hw) hsub.1 hsub.2
    · exact Ram.nil
    · exact hp.ram r hr

end

/-! ## The table's heap blocks -/

/-- The table with entry `x` set to `e`. -/
def tset (T : Nat → Option (Nat × MpInt)) (x : Nat) (e : Option (Nat × MpInt)) : Nat → Option (Nat × MpInt) :=
  fun j => if j = x then e else T j

theorem tset_self (T : Nat → Option (Nat × MpInt)) (x : Nat) (e : Option (Nat × MpInt)) : tset T x e x = e := by
  simp [tset]

theorem tset_ne (T : Nat → Option (Nat × MpInt)) {x j : Nat} (e : Option (Nat × MpInt)) (h : j ≠ x) :
    tset T x e j = T j := by simp [tset, h]

/-- An entry's block: its digit array, if the entry is live. -/
def tabBlk : Option (Nat × MpInt) → List (Nat × Nat)
  | some (q, v) => [(q, 4 * v.alloc)]
  | none => []

/-- The blocks of the live entries `lo, lo + 1, …, lo + k - 1` of the table `T`, in index order. -/
def tabBlks (T : Nat → Option (Nat × MpInt)) (lo : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | k + 1 => tabBlks T lo k ++ tabBlk (T (lo + k))

/-- One entry changed outside the range: the blocks are the same. -/
theorem tabBlks_out (T : Nat → Option (Nat × MpInt)) (lo x : Nat) (e : Option (Nat × MpInt)) :
    ∀ k, (x < lo ∨ lo + k ≤ x) → tabBlks (tset T x e) lo k = tabBlks T lo k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [tabBlks]
    rw [tabBlks_out T lo x e k (by omega), tset_ne _ _ (by omega)]

/-- **An entry's block to the front**: the table with that entry dead behind it. -/
theorem tabBlks_front (T : Nat → Option (Nat × MpInt)) (lo x : Nat) (e : Option (Nat × MpInt)) :
    ∀ k, lo ≤ x → x < lo + k →
      (tabBlks (tset T x e) lo k).Perm (tabBlk e ++ tabBlks (tset T x none) lo k)
  | 0, _, h => absurd h (by omega)
  | k + 1, h1, h2 => by
    simp only [tabBlks]
    by_cases hx : x = lo + k
    · subst hx
      rw [tabBlks_out T lo (lo + k) e k (.inr (Nat.le_refl _)), tabBlks_out T lo (lo + k) none k (.inr (Nat.le_refl _)),
        tset_self, tset_self]
      simp only [tabBlk, List.append_nil]
      exact List.perm_append_comm
    · rw [tset_ne _ _ (Ne.symm hx), tset_ne _ _ (Ne.symm hx)]
      have ih := tabBlks_front T lo x e k h1 (by omega)
      exact (ih.append_right _).trans (by rw [List.append_assoc])

/-- The table's blocks after one entry changed: the old blocks with that entry's block replaced. -/
theorem tabBlks_set (T : Nat → Option (Nat × MpInt)) (lo x k : Nat) (h1 : lo ≤ x) (h2 : x < lo + k)
    (e : Option (Nat × MpInt)) (hT : T x = none) :
    (tabBlks (tset T x e) lo k).Perm (tabBlk e ++ tabBlks T lo k) := by
  have := tabBlks_front T lo x e k h1 h2
  rwa [show tset T x none = T from by
    funext j; by_cases hj : j = x
    · subst hj; rw [tset_self, hT]
    · rw [tset_ne _ _ hj]] at this

/-! ## The heap list of a function with a table: `rB ++ (tabBlks T lo k ++ R)` -/

/-- **An entry's block to the front** (a call on `M[x]`), behind it the rest with `x` dead. -/
theorem tab_front (rB R : List (Nat × Nat)) (T : Nat → Option (Nat × MpInt)) (lo k x : Nat) (h1 : lo ≤ x)
    (h2 : x < lo + k) :
    (rB ++ (tabBlks T lo k ++ R)).Perm (tabBlk (T x) ++ (rB ++ (tabBlks (tset T x none) lo k ++ R))) := by
  have e : tset T x (T x) = T := by
    funext j; by_cases hj : j = x
    · subst hj; rw [tset_self]
    · rw [tset_ne _ _ hj]
  have hf := tabBlks_front T lo x (T x) k h1 h2
  rw [e] at hf
  refine List.perm_iff_count.2 fun a => ?_
  have := hf.count_eq a
  simp only [List.count_append] at this ⊢; omega

/-- **The entry's block back** (after the call, re-placed or not): the table with `x` set. -/
theorem tab_back (rB R : List (Nat × Nat)) (T : Nat → Option (Nat × MpInt)) (lo k x : Nat) (h1 : lo ≤ x)
    (h2 : x < lo + k) (e : Option (Nat × MpInt)) :
    (tabBlk e ++ (rB ++ (tabBlks (tset T x none) lo k ++ R))).Perm (rB ++ (tabBlks (tset T x e) lo k ++ R)) := by
  have hf := tabBlks_front T lo x e k h1 h2
  refine List.perm_iff_count.2 fun a => ?_
  have := hf.count_eq a
  simp only [List.count_append] at this ⊢; omega

/-- **A new entry `lo + k` placed** (`mp_init_size(&M[lo + k], …)` returned its block in front). -/
theorem tab_alloc (R : List (Nat × Nat)) (T : Nat → Option (Nat × MpInt)) (lo k : Nat) (e : Option (Nat × MpInt)) :
    (tabBlk e ++ (tabBlks T lo k ++ R)).Perm (tabBlks (tset T (lo + k) e) lo (k + 1) ++ R) := by
  have h : tabBlks (tset T (lo + k) e) lo (k + 1) = tabBlks T lo k ++ tabBlk e := by
    simp only [tabBlks, tset_self]; rw [tabBlks_out T lo (lo + k) e k (.inr (Nat.le_refl _))]
  rw [h]
  refine List.perm_iff_count.2 fun a => ?_
  simp only [List.count_append]; omega

/-- **A block of the rest to the front** (a call on `M[1]`, whose block lies behind the table's). -/
theorem tab_mid (rB A b R : List (Nat × Nat)) : (rB ++ (A ++ (b ++ R))).Perm (b ++ (rB ++ (A ++ R))) := by
  refine List.perm_iff_count.2 fun a => ?_
  simp only [List.count_append]; omega

end Tom.Machine
