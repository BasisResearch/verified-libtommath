import Tom.Machine.Kit.Tab
import Tom.Machine.Kit.HeapBlk
import Tom.Spec.WindowStep

/-!
# A table of `mp_int`s as a function's state (`s_mp_exptmod_fast`, `s_mp_exptmod`)

`Kit/Tab.lean` spreads the table's frame piece over its slots and keeps its heap blocks in order;
this file states a cut over the table's *contents*. A region type with a table names, by a
`TabSig`, its struct slots `tS j` and digit arrays `tD j` (indexed constructors, read back by
`famS`/`famD`) and one more entry, `res` (`rS` its struct, `rD` its digits). The table is
`T : Nat → Option (Nat × MpInt)` (entry `j`: its digit block and value, or dead), `res` the entry
`rI` (its struct `rS'` may hold another value, after `mp_exch(&res, Y)`):

* `tLay G ρ T rI`: the layout with the digit arrays placed (`entIv`), the rest `ρ`'s;
* `tKind G κ b pr T rS' rI`: the kinds, struct `j` at `b + 24 j`, `res`'s at `pr`, the rest `κ`'s;
* `St.entCall`, `St.resCall`, `St.resStd`: the state after a call on one entry `x` (σ onto the callees'
  area, `tS x`, `tD x`) or on `res`, over `tset T x e` (resp. `res := e`); the premises are computations
  on the callee's record, the old kinds' agreement `hκ` with `tKind` one `rfl` per region.
* `tabV one Q V lo hi`: the live entries `M[1]` (if `one`) and `[lo, hi)`, entry `j` at `Q j` holding
  `V j`, and the heap lists of the init loop, the clear loops and the table calls (`heap_snoc`,
  `heap_front`, `heap_m1`, `heap_empty`, `tabBlks_set1`).
-/

namespace Tom.Machine

open Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-- An entry's digit array, its kinds. -/
def entIv : Option (Nat × MpInt) → Iv
  | some (q, v) => ⟨q, 4 * v.alloc⟩
  | none => Iv.nil

def entS (pa : Nat) : Option (Nat × MpInt) → Kind
  | some (q, v) => .mpS pa q v
  | none => .ram

def entD : Option (Nat × MpInt) → Kind
  | some (q, v) => .mpD q v.alloc v.digit
  | none => .ram

/-- A region type's table: the slots, the digit arrays, `res`'s struct and digits. -/
structure TabSig (ι : Type) where
  tS : Nat → ι
  tD : Nat → ι
  rS : ι
  rD : ι
  famS : ι → Option Nat
  famD : ι → Option Nat

/-- The names are distinct and read back. -/
structure TabSig.Ok {ι : Type} (G : TabSig ι) : Prop where
  sS : ∀ j, G.famS (G.tS j) = some j
  dD : ∀ j, G.famD (G.tD j) = some j
  sInv : ∀ r j, G.famS r = some j → r = G.tS j
  dInv : ∀ r j, G.famD r = some j → r = G.tD j
  sD : ∀ j, G.famS (G.tD j) = none
  dS : ∀ j, G.famD (G.tS j) = none
  sRS : G.famS G.rS = none
  dRS : G.famD G.rS = none
  sRD : G.famS G.rD = none
  dRD : G.famD G.rD = none
  rSD : G.rS ≠ G.rD

section
variable {ι : Type} [DecidableEq ι]

/-- The layout with the table's and `res`'s digit arrays placed. -/
def tLay (G : TabSig ι) (ρ : ι → Iv) (T : Nat → Option (Nat × MpInt)) (rI : Option (Nat × MpInt)) : ι → Iv :=
  fun r => match G.famD r with
  | some j => entIv (T j)
  | none => if r = G.rD then entIv rI else ρ r

/-- The kinds with the table's and `res`'s entries (`res`'s struct `rS'`, its digits `rI`: one entry
but after `mp_exch(&res, Y)`, when the struct holds `Y`'s old value). -/
def tKind (G : TabSig ι) (κ : ι → Kind) (b pr : Nat) (T : Nat → Option (Nat × MpInt))
    (rS' rI : Option (Nat × MpInt)) : ι → Kind :=
  fun r => match G.famS r with
  | some j => entS (b + 24 * j) (T j)
  | none => match G.famD r with
    | some j => entD (T j)
    | none => if r = G.rD then entD rI else if r = G.rS then entS pr rS' else κ r

variable {G : TabSig ι} {ρ : ι → Iv} {κ : ι → Kind} {b pr : Nat} {T : Nat → Option (Nat × MpInt)}
  {rS' rI : Option (Nat × MpInt)}

theorem tLay_tD (hG : G.Ok) (j : Nat) : tLay G ρ T rI (G.tD j) = entIv (T j) := by
  simp only [tLay, hG.dD]

theorem tLay_rD (hG : G.Ok) : tLay G ρ T rI G.rD = entIv rI := by
  simp only [tLay, hG.dRD, if_true]

theorem tLay_other (hG : G.Ok) {r : ι} (hD : G.famD r = none) (hR : r ≠ G.rD) : tLay G ρ T rI r = ρ r := by
  simp only [tLay, hD, if_neg hR]

theorem tKind_tS (hG : G.Ok) (j : Nat) : tKind G κ b pr T rS' rI (G.tS j) = entS (b + 24 * j) (T j) := by
  simp only [tKind, hG.sS]

theorem tKind_tD (hG : G.Ok) (j : Nat) : tKind G κ b pr T rS' rI (G.tD j) = entD (T j) := by
  simp only [tKind, hG.sD, hG.dD]

theorem tKind_rD (hG : G.Ok) : tKind G κ b pr T rS' rI G.rD = entD rI := by
  simp only [tKind, hG.sRD, hG.dRD, if_true]

theorem tKind_rS (hG : G.Ok) : tKind G κ b pr T rS' rI G.rS = entS pr rS' := by
  simp only [tKind, hG.sRS, hG.dRS, if_neg hG.rSD, if_true]

/-- Away from the table and `res`: the base kinds. -/
theorem tKind_other {r : ι} (hS : G.famS r = none) (hD : G.famD r = none) (h1 : r ≠ G.rD) (h2 : r ≠ G.rS) :
    tKind G κ b pr T rS' rI r = κ r := by
  simp only [tKind, hS, hD, if_neg h1, if_neg h2]

/-- A region outside the table and `res` re-placed: the layer moves under the table's layout. -/
theorem tLay_updO (ρ : ι → Iv) (T : Nat → Option (Nat × MpInt)) (rI : Option (Nat × MpInt)) {r : ι}
    (hD : G.famD r = none) (hR : r ≠ G.rD) (J : Iv) :
    ∀ r', Iv.upd (tLay G ρ T rI) r J r' = tLay G (Iv.upd ρ r J) T rI r' := by
  intro r'
  unfold Iv.upd tLay
  by_cases h : r' = r
  · subst h; simp [hD, hR]
  · simp only [if_neg h]

/-- **Entry `x`'s digit array placed at `entIv e`**: the table with `x` set. -/
theorem tLay_updD (hG : G.Ok) (ρ : ι → Iv) (T : Nat → Option (Nat × MpInt)) (rI : Option (Nat × MpInt)) (x : Nat)
    (e : Option (Nat × MpInt)) : ∀ r, Iv.upd (tLay G ρ T rI) (G.tD x) (entIv e) r = tLay G ρ (tset T x e) rI r := by
  intro r
  unfold Iv.upd
  split
  · next h => subst h; rw [tLay_tD hG, tset_self]
  · next h =>
    unfold tLay
    cases hd : G.famD r with
    | none => rfl
    | some j =>
      have hj : j ≠ x := fun e => h (by rw [hG.dInv r j hd, e])
      simp only [tset_ne _ _ hj]

/-- **`res`'s digit array placed at `entIv e`**. -/
theorem tLay_updR (hG : G.Ok) (ρ : ι → Iv) (T : Nat → Option (Nat × MpInt)) (rI e : Option (Nat × MpInt)) :
    ∀ r, Iv.upd (tLay G ρ T rI) G.rD (entIv e) r = tLay G ρ T e r := by
  intro r
  unfold Iv.upd
  split
  · next h => subst h; rw [tLay_rD hG]
  · next h => unfold tLay; cases G.famD r <;> simp [h]

/-- Away from entry `x`, the kinds of `tset T x e` are `T`'s. -/
theorem tKind_out (hG : G.Ok) {x : Nat} {e : Option (Nat × MpInt)} {r : ι} (h1 : r ≠ G.tS x) (h2 : r ≠ G.tD x) :
    tKind G κ b pr (tset T x e) rS' rI r = tKind G κ b pr T rS' rI r := by
  unfold tKind
  cases hs : G.famS r with
  | some j =>
    have hj : j ≠ x := fun e => h1 (by rw [hG.sInv r j hs, e])
    simp only [tset_ne _ _ hj]
  | none =>
    cases hd : G.famD r with
    | some j =>
      have hj : j ≠ x := fun e => h2 (by rw [hG.dInv r j hd, e])
      simp only [tset_ne _ _ hj]
    | none => rfl

/-- Away from `res`, the kinds with `res := e` are the old ones. -/
theorem tKind_outR {e : Option (Nat × MpInt)} {r : ι} (h1 : r ≠ G.rS) (h2 : r ≠ G.rD) :
    tKind G κ b pr T e e r = tKind G κ b pr T rS' rI r := by
  unfold tKind
  cases G.famS r with
  | some j => rfl
  | none => cases G.famD r with
    | some j => rfl
    | none => simp only [if_neg h1, if_neg h2]

/-- **The empty table** over a layout with the digit arrays at `Iv.nil` (the entry's). -/
theorem tLay_nil (h1 : ∀ r j, G.famD r = some j → ρ r = Iv.nil) (h2 : ρ G.rD = Iv.nil) :
    ∀ r, ρ r = tLay G ρ (fun _ => none) none r := by
  intro r
  unfold tLay
  cases hd : G.famD r with
  | some j => exact h1 r j hd
  | none =>
    by_cases e : r = G.rD
    · subst e; simp [h2]; rfl
    · simp [e]

/-- The empty table over kinds with the table's regions and `res` RAM. -/
theorem tKind_nil (h1 : ∀ r j, G.famS r = some j → κ r = .ram) (h2 : ∀ r j, G.famD r = some j → κ r = .ram)
    (h3 : κ G.rD = .ram) (h4 : κ G.rS = .ram) : ∀ r, κ r = tKind G κ b pr (fun _ => none) none none r := by
  intro r
  unfold tKind
  cases hs : G.famS r with
  | some j => exact h1 r j hs
  | none =>
    cases hd : G.famD r with
    | some j => exact h2 r j hd
    | none =>
      by_cases e1 : r = G.rD
      · subst e1; simp [entD, h3]
      · by_cases e2 : r = G.rS
        · subst e2; simp [e1, entS, h4]
        · simp [e1, e2]

/-- `res`'s layout sees only its block's size. -/
theorem tLay_res_alloc (ρ : ι → Iv) (T : Nat → Option (Nat × MpInt)) (q : Nat) {v v' : MpInt}
    (h : v.alloc = v'.alloc) : ∀ r, tLay G ρ T (some (q, v)) r = tLay G ρ T (some (q, v')) r := by
  intro r; unfold tLay; cases G.famD r <;> simp [entIv, h]

end

/-! ## The kinds after a call on an entry or on `res` -/

section
variable {ι : Type} [DecidableEq ι] {κR : Type} {G : TabSig ι} {stk : ι} {σ : κR → ι} {ws : List κR}
  {κ : ι → Kind} {κc : κR → Kind} {b pr : Nat} {T : Nat → Option (Nat × MpInt)} {rS' rI : Option (Nat × MpInt)}

/-- **The kinds after a callee wrote entry `x`** (σ onto the callees' area `stk`, `tS x`, `tD x`, both
of the entry's regions written): the table with `x` set to what the callee left. `κ` is any kinds that
read the table and `res` as `tKind` does (`hκ`, by computation at the use). -/
theorem pushH_ent (hG : G.Ok) {x : Nat} {e : Option (Nat × MpInt)}
    (hκ : ∀ r, κ r = tKind G κ b pr T rS' rI r)
    (hmap : ∀ r ∈ ws.map σ, r = stk ∨ r = G.tS x ∨ r = G.tD x)
    (hstk : ∀ k ∈ ws, σ k = stk → κc k = κ stk)
    (hS : ∀ k ∈ ws, σ k = G.tS x → κc k = entS (b + 24 * x) e)
    (hD : ∀ k ∈ ws, σ k = G.tD x → κc k = entD e)
    (hSin : G.tS x ∈ ws.map σ) (hDin : G.tD x ∈ ws.map σ) (hsx : stk ≠ G.tS x) (hdx : stk ≠ G.tD x) :
    ∀ r, Kind.pushH σ ws κ κc r = tKind G κ b pr (tset T x e) rS' rI r := by
  intro r
  unfold Kind.pushH
  cases hf : ws.find? (fun k => decide (σ k = r)) with
  | some k =>
    have hk := List.mem_of_find?_eq_some hf
    have hr : σ k = r := by have := List.find?_some hf; simpa using this
    subst hr
    show κc k = _
    rcases hmap (σ k) (List.mem_map_of_mem hk) with h | h | h
    · rw [hstk k hk h, h, hκ stk, tKind_out hG hsx hdx]
    · rw [hS k hk h, h, tKind_tS hG, tset_self]
    · rw [hD k hk h, h, tKind_tD hG, tset_self]
  | none =>
    have hn : r ∉ ws.map σ := fun hm => by
      obtain ⟨k, hk, hr⟩ := List.mem_map.1 hm
      have := List.find?_eq_none.1 hf k hk
      simp [hr] at this
    show κ r = _
    have h1 : r ≠ G.tS x := fun e => hn (e ▸ hSin)
    have h2 : r ≠ G.tD x := fun e => hn (e ▸ hDin)
    rw [hκ r]; exact (tKind_out hG h1 h2).symm

/-- **The kinds after a callee wrote `res`** (σ onto `stk`, `rS`, `rD`). -/
theorem pushH_res (hG : G.Ok) {e : Option (Nat × MpInt)}
    (hκ : ∀ r, κ r = tKind G κ b pr T rS' rI r)
    (hmap : ∀ r ∈ ws.map σ, r = stk ∨ r = G.rS ∨ r = G.rD)
    (hstk : ∀ k ∈ ws, σ k = stk → κc k = κ stk)
    (hS : ∀ k ∈ ws, σ k = G.rS → κc k = entS pr e)
    (hD : ∀ k ∈ ws, σ k = G.rD → κc k = entD e)
    (hSin : G.rS ∈ ws.map σ) (hDin : G.rD ∈ ws.map σ) (hsS : stk ≠ G.rS) (hsD : stk ≠ G.rD) :
    ∀ r, Kind.pushH σ ws κ κc r = tKind G κ b pr T e e r := by
  intro r
  unfold Kind.pushH
  cases hf : ws.find? (fun k => decide (σ k = r)) with
  | some k =>
    have hk := List.mem_of_find?_eq_some hf
    have hr : σ k = r := by have := List.find?_some hf; simpa using this
    subst hr
    show κc k = _
    rcases hmap (σ k) (List.mem_map_of_mem hk) with h | h | h
    · rw [hstk k hk h, h, hκ stk, tKind_outR hsS hsD]
    · rw [hS k hk h, h, tKind_rS hG]
    · rw [hD k hk h, h, tKind_rD hG]
  | none =>
    have hn : r ∉ ws.map σ := fun hm => by
      obtain ⟨k, hk, hr⟩ := List.mem_map.1 hm
      have := List.find?_eq_none.1 hf k hk
      simp [hr] at this
    show κ r = _
    have h1 : r ≠ G.rS := fun e => hn (e ▸ hSin)
    have h2 : r ≠ G.rD := fun e => hn (e ▸ hDin)
    rw [hκ r]; exact (tKind_outR h1 h2).symm

/-- **The kinds after a plain callee wrote `res`** (`call_std`'s `Kind.push`: the callee's non-RAM
kinds win), its struct and digits now `(q, v)`'s. -/
theorem push_res (hG : G.Ok) {q : Nat} {v : MpInt}
    (hκ : ∀ r, κ r = tKind G κ b pr T rS' rI r)
    (hmap : ∀ r ∈ ws.map σ, r = stk ∨ r = G.rS ∨ r = G.rD)
    (hstk : ∀ k ∈ ws, σ k = stk → (κc k).isRam = true)
    (hS : ∀ k ∈ ws, σ k = G.rS → κc k = .mpS pr q v)
    (hD : ∀ k ∈ ws, σ k = G.rD → κc k = .mpD q v.alloc v.digit)
    (hSin : G.rS ∈ ws.map σ) (hDin : G.rD ∈ ws.map σ) (hsS : stk ≠ G.rS) (hsD : stk ≠ G.rD) :
    ∀ r, Kind.push σ ws κ κc r = tKind G κ b pr T (some (q, v)) (some (q, v)) r := by
  intro r
  unfold Kind.push
  cases hf : ws.find? (fun k => decide (σ k = r)) with
  | some k =>
    have hk := List.mem_of_find?_eq_some hf
    have hr : σ k = r := by have := List.find?_some hf; simpa using this
    subst hr
    show (if (κc k).isRam then _ else _) = _
    rcases hmap (σ k) (List.mem_map_of_mem hk) with h | h | h
    · rw [if_pos (hstk k hk h), h, hκ stk, tKind_outR hsS hsD]
    · rw [hS k hk h, h, tKind_rS hG]; rfl
    · rw [hD k hk h, h, tKind_rD hG]; rfl
  | none =>
    have hn : r ∉ ws.map σ := fun hm => by
      obtain ⟨k, hk, hr⟩ := List.mem_map.1 hm
      have := List.find?_eq_none.1 hf k hk
      simp [hr] at this
    show κ r = _
    have h1 : r ≠ G.rS := fun e => hn (e ▸ hSin)
    have h2 : r ≠ G.rD := fun e => hn (e ▸ hDin)
    rw [hκ r]; exact (tKind_outR h1 h2).symm

variable {isW : ι → Bool} {W : List ι} {ρ : ι → Iv} {m M : Mem}

/-- **After an allocating call on entry `x`** (`call_heap`, its site `tD x` placed at `entIv e`): the
state over the table with `x` set. -/
theorem St.entCall (hG : G.Ok) {x : Nat} {e : Option (Nat × MpInt)}
    (h : St (Iv.upd (tLay G ρ T rI) (G.tD x) (entIv e)) isW W (Kind.pushH σ ws κ κc) m M) (b pr : Nat)
    (hκ : ∀ r, κ r = tKind G κ b pr T rS' rI r)
    (hmap : ∀ r ∈ ws.map σ, r = stk ∨ r = G.tS x ∨ r = G.tD x)
    (hstk : ∀ k ∈ ws, σ k = stk → κc k = κ stk)
    (hS : ∀ k ∈ ws, σ k = G.tS x → κc k = entS (b + 24 * x) e)
    (hD : ∀ k ∈ ws, σ k = G.tD x → κc k = entD e)
    (hSin : G.tS x ∈ ws.map σ) (hDin : G.tD x ∈ ws.map σ) (hsx : stk ≠ G.tS x) (hdx : stk ≠ G.tD x) :
    St (tLay G ρ (tset T x e) rI) isW W (tKind G κ b pr (tset T x e) rS' rI) m M :=
  (h.congrL (tLay_updD hG ρ T rI x e)).congrK (pushH_ent hG hκ hmap hstk hS hD hSin hDin hsx hdx)

/-- **After an allocating call on `res`** (its site `rD` placed at `entIv e`). -/
theorem St.resCall (hG : G.Ok) {e : Option (Nat × MpInt)}
    (h : St (Iv.upd (tLay G ρ T rI) G.rD (entIv e)) isW W (Kind.pushH σ ws κ κc) m M) (b pr : Nat)
    (hκ : ∀ r, κ r = tKind G κ b pr T rS' rI r)
    (hmap : ∀ r ∈ ws.map σ, r = stk ∨ r = G.rS ∨ r = G.rD)
    (hstk : ∀ k ∈ ws, σ k = stk → κc k = κ stk)
    (hS : ∀ k ∈ ws, σ k = G.rS → κc k = entS pr e)
    (hD : ∀ k ∈ ws, σ k = G.rD → κc k = entD e)
    (hSin : G.rS ∈ ws.map σ) (hDin : G.rD ∈ ws.map σ) (hsS : stk ≠ G.rS) (hsD : stk ≠ G.rD) :
    St (tLay G ρ T e) isW W (tKind G κ b pr T e e) m M :=
  (h.congrL (tLay_updR hG ρ T rI e)).congrK (pushH_res hG hκ hmap hstk hS hD hSin hDin hsS hsD)

/-- **After a plain call writing `res`** (`call_std`, the layout kept): `res` holds `(q, v)`. -/
theorem St.resStd (hG : G.Ok) {q : Nat} {v : MpInt}
    (h : St (tLay G ρ T rI) isW W (Kind.push σ ws κ κc) m M) (b pr : Nat)
    (hκ : ∀ r, κ r = tKind G κ b pr T rS' rI r)
    (hmap : ∀ r ∈ ws.map σ, r = stk ∨ r = G.rS ∨ r = G.rD)
    (hstk : ∀ k ∈ ws, σ k = stk → (κc k).isRam = true)
    (hS : ∀ k ∈ ws, σ k = G.rS → κc k = .mpS pr q v)
    (hD : ∀ k ∈ ws, σ k = G.rD → κc k = .mpD q v.alloc v.digit)
    (hSin : G.rS ∈ ws.map σ) (hDin : G.rD ∈ ws.map σ) (hsS : stk ≠ G.rS) (hsD : stk ≠ G.rD) :
    St (tLay G ρ T rI) isW W (tKind G κ b pr T (some (q, v)) (some (q, v))) m M :=
  h.congrK (push_res hG hκ hmap hstk hS hD hSin hDin hsS hsD)

/-- **A plain-RAM slot read as a one-word cell** (`mp_reduce_2k_setup`'s `*d`, `Reduce2kSetup.Cell`):
the digit array `fun _ => v` of the word `v` it holds. -/
theorem St.cell1 (h : St ρ isW W κ m M) (r : ι) {pd : Nat} (hk : κ r = .ram) (hl : ρ r = ⟨pd, 4⟩)
    (hal : pd % 4 = 0) : St ρ isW W (Kind.set κ r (.mpD pd 1 (fun _ => (Vsa.Sim.bytesT4 M pd).toNat))) m M := by
  refine ⟨h.sound, fun r' => ?_, h.frm⟩
  unfold Kind.set
  by_cases hr : r' = r
  · subst hr; rw [if_pos rfl]
    have hw := (h.wit r').2; rw [hk, hl] at hw
    refine ⟨by rw [hl]; exact Iv.sub_self _, ?_⟩
    exact { ram := hw, al := hal
            arr := fun j hj => by
              have : j = 0 := by omega
              subst this
              simp }
  · rw [if_neg hr]; exact h.wit r'

end

/-! ## Calls whose site's interval is the entry's only by an equation (a block kept, its size restated) -/

section
variable {ι : Type} [DecidableEq ι] {κR : Type} {G : TabSig ι} {stk : ι} {σ : κR → ι} {ws : List κR}
  {κ : ι → Kind} {κc : κR → Kind} {T : Nat → Option (Nat × MpInt)} {rS' rI : Option (Nat × MpInt)}
  {isW : ι → Bool} {W : List ι} {ρ : ι → Iv} {m M : Mem}

/-- `St.entCall` with the site placed at `J = entIv e`. -/
theorem St.entCallJ (hG : G.Ok) {x : Nat} {e : Option (Nat × MpInt)} {J : Iv}
    (h : St (Iv.upd (tLay G ρ T rI) (G.tD x) J) isW W (Kind.pushH σ ws κ κc) m M) (hJ : J = entIv e) (b pr : Nat)
    (hκ : ∀ r, κ r = tKind G κ b pr T rS' rI r)
    (hmap : ∀ r ∈ ws.map σ, r = stk ∨ r = G.tS x ∨ r = G.tD x)
    (hstk : ∀ k ∈ ws, σ k = stk → κc k = κ stk)
    (hS : ∀ k ∈ ws, σ k = G.tS x → κc k = entS (b + 24 * x) e)
    (hD : ∀ k ∈ ws, σ k = G.tD x → κc k = entD e)
    (hSin : G.tS x ∈ ws.map σ) (hDin : G.tD x ∈ ws.map σ) (hsx : stk ≠ G.tS x) (hdx : stk ≠ G.tD x) :
    St (tLay G ρ (tset T x e) rI) isW W (tKind G κ b pr (tset T x e) rS' rI) m M := by
  subst hJ; exact St.entCall hG h b pr hκ hmap hstk hS hD hSin hDin hsx hdx

/-- `St.resCall` with the site placed at `J = entIv e`. -/
theorem St.resCallJ (hG : G.Ok) {e : Option (Nat × MpInt)} {J : Iv}
    (h : St (Iv.upd (tLay G ρ T rI) G.rD J) isW W (Kind.pushH σ ws κ κc) m M) (hJ : J = entIv e) (b pr : Nat)
    (hκ : ∀ r, κ r = tKind G κ b pr T rS' rI r)
    (hmap : ∀ r ∈ ws.map σ, r = stk ∨ r = G.rS ∨ r = G.rD)
    (hstk : ∀ k ∈ ws, σ k = stk → κc k = κ stk)
    (hS : ∀ k ∈ ws, σ k = G.rS → κc k = entS pr e)
    (hD : ∀ k ∈ ws, σ k = G.rD → κc k = entD e)
    (hSin : G.rS ∈ ws.map σ) (hDin : G.rD ∈ ws.map σ) (hsS : stk ≠ G.rS) (hsD : stk ≠ G.rD) :
    St (tLay G ρ T e) isW W (tKind G κ b pr T e e) m M := by
  subst hJ; exact St.resCall hG h b pr hκ hmap hstk hS hD hSin hDin hsS hsD

end

/-! ## The table's shape: `M[1]` (if `one`) and the entries `[lo, hi)` live -/

/-- `M[1]` (when `one`) and `M[lo] … M[hi - 1]` live, entry `j` at `Q j` holding `V j`. -/
def tabV (one : Bool) (Q : Nat → Nat) (V : Nat → MpInt) (lo hi : Nat) : Nat → Option (Nat × MpInt) :=
  fun j => if (one = true ∧ j = 1) ∨ (lo ≤ j ∧ j < hi) then some (Q j, V j) else none

def qset (Q : Nat → Nat) (x q : Nat) : Nat → Nat := fun j => if j = x then q else Q j
def vset (V : Nat → MpInt) (x : Nat) (v : MpInt) : Nat → MpInt := fun j => if j = x then v else V j

/-- Nothing live (before `M[1]`, after the last `mp_clear`). -/
abbrev tnil : Nat → Option (Nat × MpInt) := fun _ => none

theorem tabV_live {one : Bool} {Q : Nat → Nat} {V : Nat → MpInt} {lo hi j : Nat} (h : lo ≤ j) (h2 : j < hi) :
    tabV one Q V lo hi j = some (Q j, V j) := by
  simp [tabV, h, h2]

theorem tabV_dead {one : Bool} {Q : Nat → Nat} {V : Nat → MpInt} {lo hi x : Nat} (h1 : 1 < lo) (hlo : lo ≤ x)
    (hx : hi ≤ x) : tabV one Q V lo hi x = none := by
  simp only [tabV]; rw [if_neg (fun hc => by rcases hc with ⟨_, h⟩ | ⟨_, h⟩ <;> omega)]

theorem tabV_one {Q : Nat → Nat} {V : Nat → MpInt} {lo hi : Nat} : tabV true Q V lo hi 1 = some (Q 1, V 1) := by
  simp [tabV]

/-- `M[x]` placed at the end of the live range. -/
theorem tabV_snoc (one : Bool) (Q : Nat → Nat) (V : Nat → MpInt) {lo x : Nat} (q : Nat) (v : MpInt)
    (hx : lo ≤ x) :
    tset (tabV one Q V lo x) x (some (q, v)) = tabV one (qset Q x q) (vset V x v) lo (x + 1) := by
  funext j
  simp only [tset, tabV, qset, vset]
  by_cases hj : j = x
  · subst hj; rw [if_pos rfl, if_pos (Or.inr ⟨hx, Nat.lt_succ_self _⟩)]; simp
  · rw [if_neg hj]; simp only [hj, if_false]
    simp only [show (lo ≤ j ∧ j < x + 1) ↔ (lo ≤ j ∧ j < x) from by omega]

/-- A live entry re-set (its block and value). -/
theorem tabV_set (one : Bool) (Q : Nat → Nat) (V : Nat → MpInt) {lo hi x : Nat} (q : Nat) (v : MpInt)
    (hx : (one = true ∧ x = 1) ∨ (lo ≤ x ∧ x < hi)) :
    tset (tabV one Q V lo hi) x (some (q, v)) = tabV one (qset Q x q) (vset V x v) lo hi := by
  funext j
  simp only [tset, tabV, qset, vset]
  by_cases hj : j = x
  · subst hj; simp only [if_true]; rw [if_pos hx]
  · simp only [hj, if_false]

/-- The front entry `M[lo]` dropped (`mp_clear(&M[lo])`). -/
theorem tabV_drop (one : Bool) (Q : Nat → Nat) (V : Nat → MpInt) {lo hi : Nat} (h1 : 1 < lo) :
    tset (tabV one Q V lo hi) lo none = tabV one Q V (lo + 1) hi := by
  funext j
  simp only [tset, tabV]
  by_cases hj : j = lo
  · subst hj; rw [if_pos rfl, if_neg (by omega)]
  · rw [if_neg hj]; simp only [show (lo ≤ j ∧ j < hi) ↔ (lo + 1 ≤ j ∧ j < hi) from by omega]

/-- `M[1]` dropped. -/
theorem tabV_drop1 (Q : Nat → Nat) (V : Nat → MpInt) {lo hi : Nat} (h1 : 1 < lo) :
    tset (tabV true Q V lo hi) 1 none = tabV false Q V lo hi := by
  funext j
  simp only [tset, tabV]
  by_cases hj : j = 1
  · subst hj; rw [if_pos rfl, if_neg (by simp; omega)]
  · rw [if_neg hj]; simp [hj]

/-- `M[1]` placed in the empty table. -/
theorem tabV_first (q : Nat) (v : MpInt) (lo : Nat) :
    tset tnil 1 (some (q, v)) = tabV true (fun _ => q) (fun _ => v) lo lo := by
  funext j
  simp only [tset, tabV]
  by_cases hj : j = 1
  · subst hj; simp
  · rw [if_neg hj, if_neg (by omega)]

theorem qset_ne (Q : Nat → Nat) {x j : Nat} (q : Nat) (h : j ≠ x) : qset Q x q j = Q j := by
  simp [qset, h]

/-- A constant value function re-set to its value. -/
theorem vset_const (v : MpInt) (x : Nat) : vset (fun _ => v) x v = fun _ => v := by
  funext j; simp [vset]

/-- An entry past the live range killed: nothing changes. -/
theorem tabV_out (one : Bool) (Q : Nat → Nat) (V : Nat → MpInt) {lo x : Nat} (h1 : 1 < lo) (hx : lo ≤ x) :
    tset (tabV one Q V lo x) x none = tabV one Q V lo x := by
  funext j
  simp only [tset, tabV]
  by_cases hj : j = x
  · subst hj; rw [if_pos rfl, if_neg (fun hc => by rcases hc with ⟨_, h⟩ | ⟨_, h⟩ <;> omega)]
  · rw [if_neg hj]

/-- Killing an entry of the empty table. -/
theorem tset_nil (x : Nat) : tset tnil x none = tnil := by
  funext j; simp [tset]

/-- Nothing live. -/
theorem tabV_empty (Q : Nat → Nat) (V : Nat → MpInt) (lo : Nat) : tabV false Q V lo lo = tnil := by
  funext j; simp only [tabV]; rw [if_neg (by simp)]

/-- The blocks of `[lo, lo + k)` read only those entries. -/
theorem tabBlks_congr {T T' : Nat → Option (Nat × MpInt)} (lo : Nat) :
    ∀ k, (∀ j, lo ≤ j → j < lo + k → T j = T' j) → tabBlks T lo k = tabBlks T' lo k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [tabBlks]
    rw [tabBlks_congr lo k (fun j h1 h2 => h j h1 (by omega)), h (lo + k) (by omega) (by omega)]

/-- The first block of a range. -/
theorem tabBlks_cons (T : Nat → Option (Nat × MpInt)) (lo : Nat) :
    ∀ k, tabBlks T lo (k + 1) = tabBlk (T lo) ++ tabBlks T (lo + 1) k
  | 0 => by simp [tabBlks]
  | k + 1 => by
    rw [tabBlks, tabBlks_cons T lo k, tabBlks, List.append_assoc, show lo + 1 + k = lo + (k + 1) by omega]

/-- The blocks of the upper half do not see `M[1]`. -/
theorem tabBlks_set1 (one : Bool) (Q : Nat → Nat) (V : Nat → MpInt) {lo hi : Nat} (k q : Nat) (v : MpInt)
    (h1 : 1 < lo) : tabBlks (tabV one (qset Q 1 q) (vset V 1 v) lo hi) lo k = tabBlks (tabV one Q V lo hi) lo k :=
  tabBlks_congr lo k fun j h2 _ => by
    simp only [tabV, qset, vset, show ¬ j = 1 by omega, if_false]

/-- `tLay_updD`, `tLay_updR` with the site at `J = entIv e`. -/
theorem tLay_updDJ {ι : Type} [DecidableEq ι] {G : TabSig ι} (hG : G.Ok) (ρ : ι → Iv) (T : Nat → Option (Nat × MpInt))
    (rI : Option (Nat × MpInt)) (x : Nat) (e : Option (Nat × MpInt)) {J : Iv} (hJ : J = entIv e) :
    ∀ r, Iv.upd (tLay G ρ T rI) (G.tD x) J r = tLay G ρ (tset T x e) rI r := by
  subst hJ; exact tLay_updD hG ρ T rI x e

theorem tLay_updRJ {ι : Type} [DecidableEq ι] {G : TabSig ι} (hG : G.Ok) (ρ : ι → Iv) (T : Nat → Option (Nat × MpInt))
    (rI e : Option (Nat × MpInt)) {J : Iv} (hJ : J = entIv e) :
    ∀ r, Iv.upd (tLay G ρ T rI) G.rD J r = tLay G ρ T e r := by
  subst hJ; exact tLay_updR hG ρ T rI e

theorem vset_self (V : Nat → MpInt) (x : Nat) (v : MpInt) : vset V x v x = v := by simp [vset]

theorem vset_posP {P : MpInt → Prop} {V : Nat → MpInt} {x : Nat} {v : MpInt} (hv : P v) (hV : ∀ j, P (V j)) :
    ∀ j, P (vset V x v j) := by
  intro j; unfold vset; split
  · exact hv
  · exact hV j

theorem qset_self (Q : Nat → Nat) (x q : Nat) : qset Q x q x = q := by simp [qset]

theorem vset_ne (V : Nat → MpInt) {x j : Nat} (v : MpInt) (h : j ≠ x) : vset V x v j = V j := by
  simp [vset, h]

/-- The blocks of `[lo, lo + k)` read only those entries' blocks. -/
theorem tabBlks_congrB {T T' : Nat → Option (Nat × MpInt)} (lo : Nat) :
    ∀ k, (∀ j, lo ≤ j → j < lo + k → tabBlk (T j) = tabBlk (T' j)) → tabBlks T lo k = tabBlks T' lo k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [tabBlks]
    rw [tabBlks_congrB lo k (fun j h1 h2 => h j h1 (by omega)), h (lo + k) (by omega) (by omega)]

/-- An entry re-valued in place (its block kept, its size the same): the same blocks. -/
theorem tabBlks_keep {T : Nat → Option (Nat × MpInt)} {lo k x q : Nat} {v v' : MpInt} (hx : T x = some (q, v))
    (ha : v'.alloc = v.alloc) : tabBlks (tset T x (some (q, v'))) lo k = tabBlks T lo k :=
  tabBlks_congrB lo k fun j _ _ => by
    by_cases hj : j = x
    · subst hj; rw [tset_self, hx]; simp [tabBlk, ha]
    · rw [tset_ne _ _ hj]

theorem qset_id (Q : Nat → Nat) (x : Nat) : qset Q x (Q x) = Q := by
  funext j; by_cases h : j = x
  · subst h; simp [qset]
  · simp [qset, h]

theorem vset_id (V : Nat → MpInt) (x : Nat) : vset V x (V x) = V := by
  funext j; by_cases h : j = x
  · subst h; simp [vset]
  · simp [vset, h]

theorem qset_qset (Q : Nat → Nat) (x q q' : Nat) : qset (qset Q x q) x q' = qset Q x q' := by
  funext j; by_cases h : j = x <;> simp [qset, h]

theorem vset_vset (V : Nat → MpInt) (x : Nat) (v v' : MpInt) : vset (vset V x v) x v' = vset V x v' := by
  funext j; by_cases h : j = x <;> simp [vset, h]

/-- **The heap list with one entry re-valued in place** (its block and size kept): the same list. -/
theorem heap_conv {Q Q' : Nat → Nat} {V V' : Nat → MpInt} (lo hi k : Nat) (R : List (Nat × Nat)) {x : Nat}
    (hQ : ∀ j, j ≠ x → Q' j = Q j) (hV : ∀ j, j ≠ x → V' j = V j) (hq : Q' x = Q x)
    (ha : (V' x).alloc = (V x).alloc) (h1 : x ≠ 1) :
    tabBlks (tabV true Q' V' lo hi) lo k ++ ((Q' 1, 4 * (V' 1).alloc) :: R) =
      tabBlks (tabV true Q V lo hi) lo k ++ ((Q 1, 4 * (V 1).alloc) :: R) := by
  rw [hQ 1 (Ne.symm h1), hV 1 (Ne.symm h1)]
  congr 1
  refine tabBlks_congrB lo k fun j _ _ => ?_
  simp only [tabV]
  split
  · by_cases hj : j = x
    · subst hj; simp [tabBlk, hq, ha]
    · simp [tabBlk, hQ j hj, hV j hj]
  · rfl

/-- `M[1]`'s block behind the table, its pointer and value read through `qset`/`vset` at another entry. -/
theorem heap_m1set (Q : Nat → Nat) (V : Nat → MpInt) {x : Nat} (q : Nat) (v : MpInt) (A R : List (Nat × Nat))
    (h1 : x ≠ 1) : A ++ ((qset Q x q 1, 4 * (vset V x v 1).alloc) :: R) = A ++ ((Q 1, 4 * (V 1).alloc) :: R) := by
  rw [qset_ne Q q (Ne.symm h1), vset_ne V v (Ne.symm h1)]

/-- An empty range: no blocks. -/
theorem heap_empty (T : Nat → Option (Nat × MpInt)) {lo hi : Nat} (R : List (Nat × Nat)) (h : hi = lo) :
    tabBlks T lo (hi - lo) ++ R = R := by
  subst h; simp [tabBlks]

/-- `M[1]` placed, the upper half empty: the heap list at the first `mp_init_size` of the loop. -/
theorem heap_first (T : Nat → Option (Nat × MpInt)) (lo q n : Nat) (R : List (Nat × Nat)) :
    ((q, 4 * n) :: R).Perm (tabBlks T lo (lo - lo) ++ ((q, 4 * (MpInt.zeroN n).alloc) :: R)) := by
  rw [Nat.sub_self]; exact List.Perm.refl _

/-- **`M[x]` placed** (`mp_init_size(&M[x], …)` returned its block in front). -/
theorem heap_snoc (one : Bool) (Q : Nat → Nat) (V : Nat → MpInt) {lo x : Nat} (q : Nat) (v : MpInt)
    (R : List (Nat × Nat)) (hx : lo ≤ x) :
    ((q, 4 * v.alloc) :: (tabBlks (tabV one Q V lo x) lo (x - lo) ++ R)).Perm
      (tabBlks (tabV one (qset Q x q) (vset V x v) lo (x + 1)) lo (x + 1 - lo) ++ R) := by
  have := tab_alloc R (tabV one Q V lo x) lo (x - lo) (some (q, v))
  rw [show lo + (x - lo) = x by omega, show x - lo + 1 = x + 1 - lo by omega, tabV_snoc one Q V q v hx] at this
  exact this

/-- **`M[lo]`'s block to the front** (for `mp_clear(&M[lo])`), behind it the rest. -/
theorem heap_front (one : Bool) (Q : Nat → Nat) (V : Nat → MpInt) {lo hi : Nat} (R : List (Nat × Nat))
    (h : lo < hi) :
    tabBlks (tabV one Q V lo hi) lo (hi - lo) ++ R =
      (Q lo, 4 * (V lo).alloc) :: (tabBlks (tabV one Q V (lo + 1) hi) (lo + 1) (hi - (lo + 1)) ++ R) := by
  rw [show hi - lo = (hi - (lo + 1)) + 1 by omega, tabBlks_cons, tabV_live (Nat.le_refl _) h]
  simp only [tabBlk, List.cons_append]
  congr 2
  refine tabBlks_congr _ _ fun j h1 h2 => ?_
  simp only [tabV]
  simp only [show (lo ≤ j ∧ j < hi) ↔ (lo + 1 ≤ j ∧ j < hi) from by omega]

/-- `M[1]`'s block to the front, the table behind it without `M[1]` (`mp_clear(&M[1])`). -/
theorem heap_m1 (Q : Nat → Nat) (V : Nat → MpInt) {lo hi k : Nat} (e : Nat × Nat) (R : List (Nat × Nat))
    (h1 : 1 < lo) :
    (tabBlks (tabV true Q V lo hi) lo k ++ (e :: R)).Perm (e :: (tabBlks (tabV false Q V lo hi) lo k ++ R)) := by
  rw [tabBlks_congr (T' := tabV false Q V lo hi) lo k fun j h2 _ => by
    simp only [tabV]; simp only [show ¬ j = 1 by omega, and_false, false_or]]
  exact List.perm_middle

/-- **`M[1]` written by a callee** (its block `(q, n)` in front, behind it `res`'s `x` and the table):
the table with `M[1]` set, its block back behind the upper half. -/
theorem heap_set1 (Q : Nat → Nat) (V : Nat → MpInt) {lo hi k : Nat} (q n : Nat) (v : MpInt) (x : Nat × Nat)
    (R : List (Nat × Nat)) (h1 : 1 < lo) (hn : n = 4 * v.alloc) :
    ((q, n) :: (x :: (tabBlks (tabV true Q V lo hi) lo k ++ R))).Perm
      (x :: (tabBlks (tabV true (qset Q 1 q) (vset V 1 v) lo hi) lo k ++
        ((qset Q 1 q 1, 4 * (vset V 1 v 1).alloc) :: R))) := by
  rw [tabBlks_set1 true Q V k q v h1]
  simp only [qset, vset, if_true, ← hn]
  exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ List.perm_middle.symm)

/-- A placed block's size from the checkpoint: the region at `(q, 4 n)` with that block live. -/
theorem HP.blkPos {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {H0 H : List (Nat × Nat)}
    {Wr0 : Nat → Prop} {m0 m : Mem} (hp : HP ρ isW H0 H Wr0 m0 m) (r : ι) {q n : Nat}
    (hr : ρ r = ⟨q, 4 * n⟩) (hm : (q, 4 * n) ∈ H) : 0 < n :=
  Off.pos_blk (hr ▸ hp.off r) hp.heap.heap hm

/-! ## The window (`winsize`) and the modulus -/

/-- The window size's facts (`w = winsize`): the table's half `2^(w-1)` and its range. -/
structure WF (w : Nat) : Prop where
  two : 2 ≤ w
  le8 : w ≤ 8
  h2 : 2 ≤ 2 ^ (w - 1)
  h128 : 2 ^ (w - 1) ≤ 128
  dbl : 2 * 2 ^ (w - 1) = 2 ^ w

theorem WF.of {w : Nat} {X : MpInt} (hw : w = Exptmod.wsize X) : WF w := by
  have h2 : 2 ≤ w := hw ▸ Window.two_le_winSize _
  have h8 : w ≤ 8 := hw ▸ Window.winSize_le _
  refine ⟨h2, h8, WindowStep.two_le_half h2, ?_, ?_⟩
  · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show w - 1 ≤ 7 by omega); simpa using this
  · have := WindowStep.half_lt h2; omega

/-- An odd magnitude has an odd lowest digit. -/
theorem digit0_odd {N : MpInt} (hs : N.Shape) (h : N.mag % 2 = 1) : N.digit 0 % 2 = 1 := by
  rw [← Tom.Mont.MpInt.mag_mod_radix hs, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ Tom.radix)]; exact h

end Tom.Machine
