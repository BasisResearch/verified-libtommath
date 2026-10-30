import Tom.Machine.Kit.Meet

/-!
# A frame with a buffer: the stack region cut in four (over `Kit/Meet.lean`)

`Split` cuts a contract's stack region into the own frame and the callees'
area. A function whose frame holds a buffer (the comba column array
`W[MP_WARRAY]`) needs the buffer as a region of its own, of a kind other than
`frz` (a digit array, read and written by the segments and handed to
`memcpy`). `Bf.lay ρ s f a B` cuts the stack region `s`: the callees' area
`o s` (its bottom `len - f` bytes) and, in the top `f` bytes, `lo` (the first
`a`: the spills), `buf` (the next `B`), `hi` (the rest: the saved registers).

* `Bf.sound`, `Bf.bundle` (at the entry: `lo`, `hi` frozen at the entry
  memory, `buf` untracked RAM), `Bf.unframe`/`St.unbuf` (the frame back in the
  contract's names), `St.twoB` (the entry state of a `Two` contract);
* `St.ramDig`: an untracked RAM region `⟨dp, 4 n⟩` re-read as the digit array
  of its current contents (`rdD`), so that its stores go through
  `St.seqD`/`St.seqOvl`.
-/

namespace Tom.Machine

open Vsa.Sim

/-- The regions of a frame with a buffer. -/
inductive Bf (R : Type) | lo | buf | hi | o (r : R)
  deriving DecidableEq

instance {R : Type} [Names R] : Names (Bf R) := ⟨.lo :: .buf :: .hi :: (Names.all : List R).map .o⟩

section
variable {R : Type} [DecidableEq R] {ρ : R → Iv} {isW : R → Bool} {s : R} {f a B : Nat}

def Bf.lay (ρ : R → Iv) (s : R) (f a B : Nat) : Bf R → Iv
  | .lo => ⟨(ρ s).base + (ρ s).len - f, a⟩
  | .buf => ⟨(ρ s).base + (ρ s).len - f + a, B⟩
  | .hi => ⟨(ρ s).base + (ρ s).len - f + a + B, f - a - B⟩
  | .o r => if r = s then ⟨(ρ s).base, (ρ s).len - f⟩ else ρ r

def Bf.wr (isW : R → Bool) : Bf R → Bool
  | .o r => isW r
  | _ => true

/-- `lo` holds `ml`'s bytes, `hi` holds `mh`'s, `buf` is of kind `kb`. -/
def Bf.kind (κ : R → Kind) (ml mh : Mem) (kb : Kind) : Bf R → Kind
  | .lo => .frz ml
  | .hi => .frz mh
  | .buf => kb
  | .o r => κ r

/-- The contract's region a name lies in. -/
def Bf.getD (s : R) : Bf R → R
  | .o r => r
  | _ => s

theorem Bf.sub (hf : a + B ≤ f) (hfl : f ≤ (ρ s).len) : ∀ x, (Bf.lay ρ s f a B x).Sub (ρ (Bf.getD s x))
  | .lo | .buf | .hi => by simp only [Bf.lay, Bf.getD, Iv.Sub]; omega
  | .o r => by
    simp only [Bf.lay, Bf.getD]; split
    · subst r; simp only [Iv.Sub]; omega
    · exact Iv.sub_self _

theorem Bf.wr_getD (hs : isW s = true) : ∀ x, Bf.wr isW x = isW (Bf.getD s x)
  | .lo | .buf | .hi => hs.symm
  | .o _ => rfl

theorem Bf.sound (hS : Sound ρ isW) (hs : isW s = true) (hf : a + B ≤ f) (hfl : f ≤ (ρ s).len) :
    Sound (Bf.lay ρ s f a B) (Bf.wr isW) := by
  intro x y h
  by_cases hxy : Bf.getD s x = Bf.getD s y
  · have hx : x = .lo ∨ x = .buf ∨ x = .hi ∨ x = .o s := by
      rcases x with _ | _ | _ | r
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases y with _ | _ | _ | t
        · exact Or.inr (Or.inr (Or.inr (by simp only [Bf.getD] at hxy; rw [hxy])))
        · exact Or.inr (Or.inr (Or.inr (by simp only [Bf.getD] at hxy; rw [hxy])))
        · exact Or.inr (Or.inr (Or.inr (by simp only [Bf.getD] at hxy; rw [hxy])))
        · simp only [Bf.getD] at hxy; subst hxy; simp [Sep] at h
    have hy : y = .lo ∨ y = .buf ∨ y = .hi ∨ y = .o s := by
      rcases y with _ | _ | _ | t
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases hx with rfl | rfl | rfl | rfl <;> simp only [Bf.getD] at hxy <;> rw [← hxy] <;>
          exact Or.inr (Or.inr (Or.inr rfl))
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first
      | (simp only [Bf.lay, if_pos (rfl : s = s), ite_true, Iv.Disj, Disj]; omega)
      | exact absurd h (by simp [Sep])
  · refine hS.sub (Bf.sub hf hfl x) (Bf.sub hf hfl y) ?_
    have hne : ¬ Bf.getD s x = Bf.getD s y := hxy
    simp only [Sep, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h ⊢
    exact ⟨hne, by rw [← Bf.wr_getD hs, ← Bf.wr_getD hs]; exact h.2⟩

theorem Bf.bundle {κ : R → Kind} {m : Mem} (hB : Bundle ρ κ m) (hk : κ s = .ram) (hf : a + B ≤ f)
    (hfl : f ≤ (ρ s).len) : Bundle (Bf.lay ρ s f a B) (Bf.kind κ m m .ram) m
  | .lo | .buf | .hi => by
      have hr := (hB s).2; rw [hk] at hr
      have hw : Kind.Wit .ram (ρ s) m := hr
      refine ⟨trivial, ?_⟩
      first
      | exact ⟨Kind.Wit.sub (k := .ram) hw (Bf.sub (x := .lo) hf hfl), fun _ _ => rfl⟩
      | exact ⟨Kind.Wit.sub (k := .ram) hw (Bf.sub (x := .hi) hf hfl), fun _ _ => rfl⟩
      | exact Kind.Wit.sub (k := .ram) hw (Bf.sub (x := .buf) hf hfl)
  | .o r => by
      by_cases hr : r = s
      · subst hr
        exact ⟨by simp only [Bf.kind, hk, Kind.Fits], by
          simp only [Bf.kind]; exact (hB r).2.sub (Bf.sub (x := .o r) hf hfl)⟩
      · simp only [Bf.kind, Bf.lay, if_neg hr]; exact hB r

theorem Bf.unframe {ws : List (Bf R)} {m M : Mem} (hf : a + B ≤ f) (hfl : f ≤ (ρ s).len)
    (h : Frm (Bf.lay ρ s f a B) ws m M) : Frm ρ (ws.map (Bf.getD s)) m M :=
  Frm.push _ (Bf.sub hf hfl) h

/-- The frame in the contract's names. -/
theorem St.unbuf {W : List (Bf R)} {κ : Bf R → Kind} {m M : Mem}
    (h : St (Bf.lay ρ s f a B) (Bf.wr isW) W κ m M) (hf : a + B ≤ f) (hfl : f ≤ (ρ s).len) {ws : List R}
    (hws : SubN (W.map (Bf.getD s)) ws = true := by decide) : Frm ρ ws m M :=
  (Bf.unframe hf hfl h.frm).mono hws

end

/-- The entry state of a two-operand function (`b` written) whose own frame of
`f` bytes holds the spills (`a`), a buffer (`B`) and the saves. -/
theorem St.twoB {m : Mem} {F f a B sp pa adp pb bdp : Nat} {x y : MpInt} (hrx : MpAt m pa adp x)
    (hgx : MpGeom pa adp x.alloc) (hry : MpAt m pb bdp y) (hgy : MpGeom pb bdp y.alloc) (hrs : Ram (sp - F) F)
    (himg : Img m) (hS : Sound (Api.Two.lay F sp pa adp pb bdp x y) Api.Two.isW) (hf : a + B ≤ f) (hfF : f ≤ F) :
    St (Bf.lay (Api.Two.lay F sp pa adp pb bdp x y) .stk f a B) (Bf.wr Api.Two.isW)
      [.lo, .buf, .hi, .o .stk, .o .bS, .o .bD] (Bf.kind (Two.kind pa adp pb bdp x y) m m .ram) m m :=
  ⟨Bf.sound hS rfl hf hfF, Bf.bundle (Two.bundle hrx hgx hry hgy hrs himg) rfl hf hfF, Frm.refl _ _⟩

/-! ## A RAM region re-read as a digit array -/

/-- The words at `dp` as digits. -/
def rdD (M : Mem) (dp : Nat) (i : Nat) : Nat := (bytesT4 M (dp + 4 * i)).toNat

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}

/-- **An untracked RAM region `⟨dp, 4 n⟩` as the digit array of its contents.** -/
theorem St.ramDig (h : St ρ isW W κ m M) (r : ι) (hk : κ r = .ram) {dp n : Nat} (hb : (ρ r).base = dp)
    (hl : (ρ r).len = 4 * n) (hal : dp % 4 = 0) :
    St ρ isW W (Kind.set κ r (.mpD dp n (rdD M dp))) m M := by
  refine ⟨h.sound, fun r' => ?_, h.frm⟩
  unfold Kind.set
  by_cases hr : r' = r
  · subst hr; simp only [if_true]
    have hw := (h.wit r').2; rw [hk] at hw
    have hw' : Ram (ρ r').base (ρ r').len := hw
    rw [hb, hl] at hw'
    show Iv.Sub ⟨dp, 4 * n⟩ (ρ r') ∧ Dig M dp n (rdD M dp)
    refine ⟨⟨by rw [hb]; exact Nat.le_refl _, by rw [hb, hl]; exact Nat.le_refl _⟩, { ram := hw', al := hal, arr := fun j _ => ?_ }⟩
    simp only [rdD, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [hr, if_false]; exact h.wit r'

end

end Tom.Machine
