import Tom.Machine.Kit.Arr
import Tom.Machine.Kit.Auto
import Vsa.Sim.TripleCat

/-!
# Named regions: dynamic frames over the existing memory terms

A function's memory is described by a closed set of region *names* `ι` (an
enum per function, `deriving DecidableEq`) and a symbolic placement
`ρ : ι → Iv` (the only part that mentions `sp`, `pc`, `cdp`, …). Which names
the function writes is a closed `isW : ι → Bool`.

* `Sound ρ isW`: every two distinct names one of which is written are
  disjoint. Proved once per function from its layout (`sound_cases`).
  Use sites never see an interval disjointness: they decide `Sep`/`Misses`
  on closed names (`by decide`, the default argument).
* `Frm ρ ws m M`: `M` equals `m` outside the names `ws`. It composes along
  stores (`Frm.store`, `Frm.sw`: a `writeLog` entry inside a name), calls
  (`Frm.call`: a callee's frame clause inside a name), `Frm.trans`,
  `Frm.step` (append and renormalise by a closed inclusion), and it gives a
  function's frame clause back (`Frm.clause`).
* `Reads ρ rs P`: `P` reads only the names `rs`. The frame rule `Frm.keep`
  moves a `P m` to `P M` when `rs` misses `ws` (closed). Instances:
  `Reads.w4`/`w8` (a word or doubleword slot), `Reads.agree`, `ArrAt.reads`,
  `MpAt.reads`, `CodeAt.reads`. `Frm.on` is the point form.
* In-place array loops: `ovl g old i` (`g` below `i`, `old` above);
  `ArrFrm ρ w m0 M b n f` (memory since the snapshot `m0` changed only in the
  array's name `w`, which holds `f`), `ArrFrm.step` (one `sw` of `g i` at
  element `i`), `ArrFrm.fill` (a zero fill of elements `[i, k)`); `ASt` (a
  join point: `At` on such a memory), `ASt.seg`/`ASt.store` (a segment that
  stores nothing / one array element), `Triple.countup_from`.

Everything is stated over `Mem`, `writeLog`, `bytesT4`/`bytesT8`, `ArrAt`,
`MpAt`, `CodeAt`.
-/

namespace Tom.Machine

open Vsa.Sim

theorem Disj.symm {a n b k : Nat} (h : Disj a n b k) : Disj b k a n := Or.symm h

/-! ## Intervals -/

/-- The bytes `[base, base + len)`. -/
structure Iv where
  base : Nat
  len : Nat

def Iv.In (I : Iv) (x : Nat) : Prop := I.base ≤ x ∧ x < I.base + I.len

def Iv.Sub (I J : Iv) : Prop := J.base ≤ I.base ∧ I.base + I.len ≤ J.base + J.len

def Iv.Disj (I J : Iv) : Prop := Tom.Machine.Disj I.base I.len J.base J.len

theorem Iv.sub_self (I : Iv) : I.Sub I := ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- Element `i` of an array of `n` words. -/
theorem Iv.sub_elem {b i n : Nat} (h : i < n) : Iv.Sub ⟨b + 4 * i, 4⟩ ⟨b, 4 * n⟩ :=
  ⟨by simp, by simp only; omega⟩

/-- A prefix. -/
theorem Iv.sub_pre {a n k : Nat} (h : n ≤ k) : Iv.Sub ⟨a, n⟩ ⟨a, k⟩ := ⟨Nat.le_refl _, by simp only; omega⟩

/-! ## Names, footprints, soundness -/

section
variable {ι : Type}

/-- `x` lies in one of the regions `ws`. -/
def InAny (ρ : ι → Iv) : List ι → Nat → Prop
  | [], _ => False
  | r :: rs, x => (ρ r).In x ∨ InAny ρ rs x

theorem InAny.exists {ρ : ι → Iv} : ∀ {ws : List ι} {x : Nat}, InAny ρ ws x → ∃ w ∈ ws, (ρ w).In x
  | [], _, h => h.elim
  | _ :: _, _, Or.inl h => ⟨_, List.mem_cons_self .., h⟩
  | _ :: _, _, Or.inr h => let ⟨w, hw, hx⟩ := InAny.exists h; ⟨w, List.mem_cons_of_mem _ hw, hx⟩

theorem InAny.of_mem {ρ : ι → Iv} : ∀ {ws : List ι} {w : ι} {x : Nat}, w ∈ ws → (ρ w).In x → InAny ρ ws x
  | _ :: _, _, _, List.Mem.head _, hx => Or.inl hx
  | _ :: _, _, _, List.Mem.tail _ hw, hx => Or.inr (InAny.of_mem hw hx)

theorem InAny.append {ρ : ι → Iv} {ws ws' : List ι} {x : Nat} (h : InAny ρ (ws ++ ws') x) :
    InAny ρ ws x ∨ InAny ρ ws' x := by
  obtain ⟨w, hw, hx⟩ := h.exists
  rcases List.mem_append.1 hw with h | h
  · exact Or.inl (InAny.of_mem h hx)
  · exact Or.inr (InAny.of_mem h hx)

/-! ## The frame relation -/

/-- `M` equals `m` outside the regions `ws`. -/
def Frm (ρ : ι → Iv) (ws : List ι) (m M : Mem) : Prop := ∀ x, ¬ InAny ρ ws x → M[x]? = m[x]?

variable {ρ : ι → Iv} {isW : ι → Bool}

theorem Frm.refl (ws : List ι) (m : Mem) : Frm ρ ws m m := fun _ _ => rfl

theorem Frm.trans {ws ws' : List ι} {m M M' : Mem} (h : Frm ρ ws m M) (h' : Frm ρ ws' M M') :
    Frm ρ (ws ++ ws') m M' := fun x hx => by
  rw [h' x (fun hx' => hx (by
    obtain ⟨w, hw, hxw⟩ := hx'.exists
    exact InAny.of_mem (List.mem_append_right _ hw) hxw)),
    h x (fun hx' => hx (by
    obtain ⟨w, hw, hxw⟩ := hx'.exists
    exact InAny.of_mem (List.mem_append_left _ hw) hxw))]

/-- Every entry of a write log lies inside the region `w`. -/
def LogIn (ρ : ι → Iv) (w : ι) : List WEntry → Prop
  | [] => True
  | e :: l => Iv.Sub ⟨e.1, e.2.1⟩ (ρ w) ∧ LogIn ρ w l

/-- **The store rule.** -/
theorem Frm.store {w : ι} {M : Mem} : ∀ {log : List WEntry}, LogIn ρ w log → Frm ρ [w] M (writeLog M log)
  | log, h => fun x hx => writeLog_out _ _ _ (by
      have hx' : ¬ (ρ w).In x := fun h => hx (Or.inl h)
      induction log with
      | nil => trivial
      | cons e l ih =>
        refine ⟨?_, ih h.2⟩
        have := h.1
        unfold Iv.Sub Iv.In at *; simp only at this; omega)

/-- One `sw` inside `w`. -/
theorem Frm.sw {w : ι} {M : Mem} {a : Nat} {v : BitVec 64} (h : Iv.Sub ⟨a, 4⟩ (ρ w)) :
    Frm ρ [w] M (writeLog M [(a, 4, v)]) := Frm.store ⟨h, trivial⟩

/-- **The call rule**: a callee's frame clause `[lo, lo + n)` inside `w`. -/
theorem Frm.call {w : ι} {M M' : Mem} {lo n : Nat}
    (hc : ∀ x, x < lo ∨ lo + n ≤ x → M'[x]? = M[x]?) (h : Iv.Sub ⟨lo, n⟩ (ρ w)) : Frm ρ [w] M M' :=
  fun x hx => hc x (by
    have hx' : ¬ (ρ w).In x := fun h => hx (Or.inl h)
    unfold Iv.Sub Iv.In at *; simp only at h; omega)

/-- A callee's frame clause `W` as a frame (`W` inside the names `ws`). -/
theorem Frm.ofClause {ws : List ι} {m M : Mem} {W : Nat → Prop} (h : ∀ x, ¬ W x → M[x]? = m[x]?)
    (hW : ∀ x, W x → InAny ρ ws x) : Frm ρ ws m M :=
  fun x hx => h x fun hw => hx (hW x hw)

/-- The frame as a function's frame clause `W`. -/
theorem Frm.clause {ws : List ι} {m M : Mem} {W : Nat → Prop} (h : Frm ρ ws m M)
    (hW : ∀ x, InAny ρ ws x → W x) : ∀ x, ¬ W x → M[x]? = m[x]? :=
  fun x hx => h x fun h' => hx (hW x h')

/-! ## Read footprints and the frame rule -/

/-- `P` reads only the regions `rs`. -/
def Reads (ρ : ι → Iv) (rs : List ι) (P : Mem → Prop) : Prop :=
  ∀ M M', (∀ x, InAny ρ rs x → M'[x]? = M[x]?) → P M → P M'

theorem Reads.of_sub {r : ι} {I : Iv} {P : Mem → Prop} (hI : I.Sub (ρ r))
    (hP : ∀ M M', (∀ x, I.base ≤ x → x < I.base + I.len → M'[x]? = M[x]?) → P M → P M') :
    Reads ρ [r] P :=
  fun M M' h => hP M M' fun x h1 h2 => h x (Or.inl (by unfold Iv.Sub Iv.In at *; omega))

theorem Reads.w4 {r : ι} {a : Nat} {v : BitVec 32} (h : Iv.Sub ⟨a, 4⟩ (ρ r)) :
    Reads ρ [r] (fun M => bytesT4 M a = v) :=
  Reads.of_sub h fun _ _ hs hv => by rw [bytesT4_congr fun x h1 h2 => hs x h1 h2]; exact hv

theorem Reads.w8 {r : ι} {a : Nat} {v : BitVec 64} (h : Iv.Sub ⟨a, 8⟩ (ρ r)) :
    Reads ρ [r] (fun M => bytesT8 M a = v) :=
  Reads.of_sub h fun _ _ hs hv => by rw [bytesT8_congr fun x h1 h2 => hs x h1 h2]; exact hv

/-- Agreement with a fixed memory on `[lo, lo + n)`. -/
theorem Reads.agree {r : ι} {lo n : Nat} {m0 : Mem} (h : Iv.Sub ⟨lo, n⟩ (ρ r)) :
    Reads ρ [r] (fun M => ∀ x, lo ≤ x → x < lo + n → M[x]? = m0[x]?) :=
  Reads.of_sub h fun _ _ hs hv x h1 h2 => (hs x h1 h2).trans (hv x h1 h2)

theorem ArrAt.reads {r : ι} {b n : Nat} {f : Nat → Nat} (h : Iv.Sub ⟨b, 4 * n⟩ (ρ r)) :
    Reads ρ [r] (fun M => ArrAt M b n f) :=
  Reads.of_sub h fun _ _ hs hv => hv.of_agree hs

theorem CodeAt.reads {r : ι} {base k : Nat} {ws : List (BitVec 32)} (hk : ws.length = k)
    (h : Iv.Sub ⟨base, 4 * k⟩ (ρ r)) : Reads ρ [r] (fun M => CodeAt M base ws) :=
  Reads.of_sub h fun _ _ hs hv => hv.of_eq fun x h1 h2 => hs x h1 (hk ▸ h2)

theorem MpAt.reads {rs rd : ι} {p dp : Nat} {a : MpInt} (hs : Iv.Sub ⟨p, 24⟩ (ρ rs))
    (hd : Iv.Sub ⟨dp, 4 * a.alloc⟩ (ρ rd)) : Reads ρ [rs, rd] (fun M => MpAt M p dp a) :=
  fun _ _ h hv => hv.of_agree
    (fun x h1 h2 => h x (Or.inl (by unfold Iv.Sub Iv.In at *; simp only at *; omega)))
    (fun x h1 h2 => h x (Or.inr (Or.inl (by unfold Iv.Sub Iv.In at *; simp only at *; omega))))

variable [DecidableEq ι]

/-- Names that must be disjoint: distinct, one of them written (closed). -/
def Sep (isW : ι → Bool) (r s : ι) : Bool := !decide (r = s) && (isW r || isW s)

/-- The layout is sound for `isW`: `Sep` names are disjoint. -/
def Sound (ρ : ι → Iv) (isW : ι → Bool) : Prop := ∀ r s, Sep isW r s = true → (ρ r).Disj (ρ s)

/-- Every read name is `Sep` from every written one (closed: `decide`). -/
def Misses (isW : ι → Bool) (rs ws : List ι) : Bool := rs.all fun r => ws.all fun w => Sep isW r w

/-- `ws ⊆ ws'` (closed: `decide`). -/
def SubN (ws ws' : List ι) : Bool := ws.all fun w => decide (w ∈ ws')

theorem Frm.mono {ws ws' : List ι} {m M : Mem} (h : Frm ρ ws m M)
    (hs : SubN ws ws' = true := by decide) : Frm ρ ws' m M := fun x hx => h x fun hx' => hx (by
  obtain ⟨w, hw, hxw⟩ := hx'.exists
  exact InAny.of_mem (of_decide_eq_true (List.all_eq_true.1 hs w hw)) hxw)

/-- Extend the frame by a later change inside it (`ws' ⊆ ws`, closed). -/
theorem Frm.step {ws ws' : List ι} {m M M' : Mem} (h : Frm ρ ws m M) (h' : Frm ρ ws' M M')
    (hs : SubN ws' ws = true := by decide) : Frm ρ ws m M' := fun x hx => by
  rw [h' x (fun hx' => hx (by
    obtain ⟨w, hw, hxw⟩ := hx'.exists
    exact InAny.of_mem (of_decide_eq_true (List.all_eq_true.1 hs w hw)) hxw)), h x hx]

theorem Sound.disj {ρ : ι → Iv} {isW : ι → Bool} (hS : Sound ρ isW) {r s : ι}
    (h : Sep isW r s = true := by decide) : (ρ r).Disj (ρ s) := hS r s h

/-- Sub-intervals of two `Sep` names are disjoint. -/
theorem Sound.sub {ρ : ι → Iv} {isW : ι → Bool} (hS : Sound ρ isW) {r s : ι} {I J : Iv}
    (hI : I.Sub (ρ r)) (hJ : J.Sub (ρ s)) (h : Sep isW r s = true := by decide) : I.Disj J := by
  have := hS r s h
  unfold Iv.Disj Tom.Machine.Disj Iv.Sub at *; omega

theorem Frm.agree {rs ws : List ι} {m M : Mem} (hS : Sound ρ isW) (hF : Frm ρ ws m M)
    (hm : Misses isW rs ws = true) : ∀ x, InAny ρ rs x → M[x]? = m[x]? := by
  intro x hx
  refine hF x fun hw => ?_
  obtain ⟨r, hr, hxr⟩ := hx.exists
  obtain ⟨w, hw, hxw⟩ := hw.exists
  have hd := hS r w (List.all_eq_true.1 (List.all_eq_true.1 hm r hr) w hw)
  unfold Iv.Disj Tom.Machine.Disj Iv.In at *; omega

/-- **The frame rule.** -/
theorem Frm.keep {rs ws : List ι} {P : Mem → Prop} {m M : Mem} (hS : Sound ρ isW) (hR : Reads ρ rs P)
    (hF : Frm ρ ws m M) (h : P m) (hm : Misses isW rs ws = true := by decide) : P M :=
  hR m M (Frm.agree hS hF hm) h

/-- The frame rule, pointwise on one region. -/
theorem Frm.on {r : ι} {ws : List ι} {m M : Mem} (hS : Sound ρ isW) (hF : Frm ρ ws m M)
    (hm : Misses isW [r] ws = true := by decide) : ∀ x, (ρ r).In x → M[x]? = m[x]? :=
  fun x hx => Frm.agree hS hF hm x (Or.inl hx)

end

/-! ## Callee layouts by renaming

A callee's regions `κ` are placed inside the caller's by a renaming
`f : κ → ι` (closed). Its layout is sound when every two callee names it
must keep apart map to caller names the caller keeps apart (`decide`), and
each callee region lies in its image (`Iv.Sub`, symbolic). Its frame, in
its own names, is a frame in the caller's (`Frm.push`). -/

section
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

/-- The renaming keeps `Sep` pairs apart (closed). -/
def SepPres (isW : ι → Bool) (isW' : κ → Bool) (f : κ → ι) (ks : List κ) : Bool :=
  ks.all fun k => ks.all fun l => !Sep isW' k l || Sep isW (f k) (f l)

/-- **Sound by renaming.** -/
theorem Sound.pull {ρ : ι → Iv} {isW : ι → Bool} {σ : κ → Iv} {isW' : κ → Bool} (f : κ → ι)
    (ks : List κ) (hks : ∀ k, k ∈ ks) (hS : Sound ρ isW) (hsub : ∀ k, (σ k).Sub (ρ (f k)))
    (hsep : SepPres isW isW' f ks = true := by decide) : Sound σ isW' := by
  intro k l h
  have h' : Sep isW (f k) (f l) = true := by
    have := List.all_eq_true.1 (List.all_eq_true.1 hsep k (hks k)) l (hks l)
    simp only [h, Bool.not_true, Bool.false_or] at this; exact this
  have hd := hS _ _ h'
  have h1 := hsub k; have h2 := hsub l
  unfold Iv.Disj Tom.Machine.Disj Iv.Sub at *; omega

/-- A callee frame in its names is a frame in the caller's. -/
theorem Frm.push {ρ : ι → Iv} {σ : κ → Iv} (f : κ → ι) (hsub : ∀ k, (σ k).Sub (ρ (f k)))
    {ws : List κ} {m M : Mem} (h : Frm σ ws m M) : Frm ρ (ws.map f) m M := fun x hx => h x fun hx' => hx (by
  obtain ⟨w, hw, hxw⟩ := hx'.exists
  have := hsub w
  exact InAny.of_mem (List.mem_map_of_mem hw) (by unfold Iv.Sub Iv.In at *; omega))

end

/-- Close `Sound ρ isW` from the layout's disjointness facts in context (one
`Disj` per `Sep` pair, either orientation). -/
macro "sound_cases" : tactic => `(tactic|
  (intro r s h
   cases r <;> cases s <;>
     first
     | exact absurd h (by decide)
     | assumption
     | exact Disj.symm (by assumption)))

/-- Reading back the `k`-th entry of a write log, an 8-byte store, through the
later entries off it (a saved register in a stack frame). -/
theorem bytesT8_log : ∀ (log : List WEntry) (m : Mem) (k a : Nat) (v : BitVec 64),
    (log.drop k).head? = some (a, 8, v) → OutLRange (log.drop (k + 1)) a 8 → bytesT8 (writeLog m log) a = v
  | [], _, _, _, _, h, _ => by simp at h
  | e :: log, m, 0, a, v, h, hout => by
      simp only [List.drop_zero, List.head?_cons, Option.some.injEq] at h
      subst h
      show bytesT8 (writeLog (writeLog m [(a, 8, v)]) log) a = v
      have hout' : OutLRange log a 8 := hout
      rw [bytesT8_congr fun x h1 h2 => writeLog_out (writeLog m [(a, 8, v)]) log x (outL_of_range hout' h1 h2)]
      exact bytesT8_sd_self m a v
  | _ :: log, _, k + 1, a, v, h, hout => bytesT8_log log _ k a v h hout

/-! ## In-place array loops -/

/-- `g` below `i`, `old` from `i` on. -/
def ovl (g old : Nat → Nat) (i : Nat) : Nat → Nat := fun j => if j < i then g j else old j

theorem ovl_zero (g old : Nat → Nat) : ovl g old 0 = old := by funext j; simp [ovl]

theorem bytesT4_zero {M : Mem} {x : Nat} (h : ∀ k, k < 4 → M[x + k]? = some 0#8) :
    bytesT4 M x = 0#32 := by
  simp only [bytesT4]
  rw [show x = x + 0 from rfl, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]
  rfl

theorem MpAt.arr {M : Mem} {p dp : Nat} {a : MpInt} (h : MpAt M p dp a) : ArrAt M dp a.alloc a.digit :=
  fun j hj => by simpa [Layout.sizeofDigit] using h.digits j hj

/-- An `mp_int` whose struct bytes are those of `M0`'s `a` and whose digits are `ArrAt`. -/
theorem MpAt.of_hdr {M0 M : Mem} {p dp : Nat} {a a' : MpInt} (h : MpAt M0 p dp a)
    (hs : ∀ x, p ≤ x → x < p + 24 → M[x]? = M0[x]?) (hd : ArrAt M dp a.alloc a'.digit)
    (hu : a'.used = a.used) (hal : a'.alloc = a.alloc) (hsg : a'.sign = a.sign) : MpAt M p dp a' :=
  have h4 : ∀ o, o + 4 ≤ 24 → bytesT4 M (p + o) = bytesT4 M0 (p + o) :=
    fun _ ho => bytesT4_congr fun x h1 h2 => hs x (by omega) (by omega)
  { used := by rw [h4 _ (by decide), hu]; exact h.used
    alloc := by rw [h4 _ (by decide), hal]; exact h.alloc
    sign := by rw [h4 _ (by decide), hsg]; exact h.sign
    dpv := by
      rw [bytesT8_congr fun x h1 h2 => hs x (by simp [Layout.offDp] at *; omega)
        (by simp [Layout.offDp] at *; omega)]; exact h.dpv
    digits := fun i hi => by simpa [Layout.sizeofDigit] using hd i (hal ▸ hi) }

variable {ι : Type} {ρ : ι → Iv}

/-- An in-place array loop's state: since the snapshot `m0`, memory changed
only in the array's region `w`, which holds `f`. -/
structure ArrFrm (ρ : ι → Iv) (w : ι) (m0 M : Mem) (b n : Nat) (f : Nat → Nat) : Prop where
  rgn : Iv.Sub ⟨b, 4 * n⟩ (ρ w)
  fr : Frm ρ [w] m0 M
  arr : ArrAt M b n f

theorem ArrFrm.init [DecidableEq ι] {w : ι} {m0 : Mem} {b n : Nat} {f : Nat → Nat}
    (hr : Iv.Sub ⟨b, 4 * n⟩ (ρ w)) (h : ArrAt m0 b n f) : ArrFrm ρ w m0 m0 b n f :=
  ⟨hr, Frm.refl _ _, h⟩

theorem ArrFrm.congr {w : ι} {m0 M : Mem} {b n : Nat} {f f' : Nat → Nat} (h : ArrFrm ρ w m0 M b n f)
    (hf : ∀ j, j < n → f j = f' j) : ArrFrm ρ w m0 M b n f' := { h with arr := h.arr.congr hf }

/-- **The array overlay law**, one store: `g i` at element `i`. -/
theorem ArrFrm.step [DecidableEq ι] {w : ι} {m0 M : Mem} {b n i v : Nat} {g old : Nat → Nat}
    (h : ArrFrm ρ w m0 M b n (ovl g old i)) (hi : i < n) (hv : v < 2 ^ 32) (hgv : v = g i) :
    ArrFrm ρ w m0 (writeLog M [(b + 4 * i, 4, BitVec.ofNat 64 v)]) b n (ovl g old (i + 1)) :=
  { rgn := h.rgn
    fr := Frm.step h.fr (Frm.sw (w := w) (by have := h.rgn; unfold Iv.Sub at *; simp only at *; omega))
      (by simp [SubN])
    arr := (h.arr.set i v hv).congr fun j _ => by
      simp only [ovl]
      by_cases hj : j = i
      · subst hj; simp [hgv]
      · rw [if_neg hj]; by_cases hl : j < i
        · rw [if_pos hl, if_pos (by omega)]
        · rw [if_neg hl, if_neg (by omega)] }

/-- **The array overlay law**, a zero fill of elements `[i, k)` (`memset`'s
`fill` and `frame` clauses). -/
theorem ArrFrm.fill [DecidableEq ι] {w : ι} {m0 M M' : Mem} {b n i k : Nat} {g old : Nat → Nat}
    (h : ArrFrm ρ w m0 M b n (ovl g old i)) (hik : i ≤ k) (hkn : k ≤ n)
    (hfill : ∀ t, t < 4 * (k - i) → M'[b + 4 * i + t]? = some 0#8)
    (hfr : ∀ x, x < b + 4 * i ∨ b + 4 * i + 4 * (k - i) ≤ x → M'[x]? = M[x]?)
    (hg : ∀ j, i ≤ j → j < k → g j = 0) : ArrFrm ρ w m0 M' b n (ovl g old k) :=
  { rgn := h.rgn
    fr := Frm.step h.fr (Frm.call (w := w) hfr (by have := h.rgn; unfold Iv.Sub at *; simp only at *; omega))
      (by simp [SubN])
    arr := fun j hj => by
      by_cases hin : i ≤ j ∧ j < k
      · rw [bytesT4_zero fun t ht => by
          have := hfill (4 * (j - i) + t) (by omega)
          rwa [show b + 4 * i + (4 * (j - i) + t) = b + 4 * j + t by omega] at this]
        simp only [ovl, if_pos hin.2, hg j hin.1 hin.2]
      · rw [bytesT4_congr fun y h1 h2 => hfr y (by omega), h.arr j hj]
        simp only [ovl]
        by_cases hl : j < i
        · rw [if_pos hl, if_pos (by omega)]
        · rw [if_neg hl, if_neg (by omega)] }

/-! ## Join points of an in-place array loop -/

open Vsa.Logic in
/-- The machine at `pc` with `L`, on a memory that is an `ArrFrm` with `f`. -/
def ASt (ρ : ι → Iv) (w : ι) (m0 : Mem) (b n : Nat) (keep : GRegs) (outp : Array String)
    (pc : BitVec 64) (L : GRegs) (f : Nat → Nat) (cf : Vsa.Machine.Config) : Prop :=
  ∃ M, ArrFrm ρ w m0 M b n f ∧ At pc L M keep outp cf

open Vsa.Logic in
/-- A segment that stores nothing. -/
theorem ASt.seg {w : ι} {m0 : Mem} {b n : Nat} {keep : GRegs} {outp : Array String} {pc pc' : BitVec 64}
    {L L' : GRegs} {f : Nat → Nat}
    (h : ∀ M, ArrFrm ρ w m0 M b n f → Triple (At pc L M keep outp) (At pc' L' (writeLog M []) keep outp)) :
    Triple (ASt ρ w m0 b n keep outp pc L f) (ASt ρ w m0 b n keep outp pc' L' f) :=
  fun c ⟨M, hI, hc⟩ => Triple.rmap (fun _ h => ⟨_, hI, h⟩) (h M hI) c hc

open Vsa.Logic in
/-- A segment that stores `g i` into element `i`. -/
theorem ASt.store [DecidableEq ι] {w : ι} {m0 : Mem} {b n i v : Nat} {keep : GRegs}
    {outp : Array String} {pc pc' : BitVec 64} {L L' : GRegs} {g old : Nat → Nat}
    (h : ∀ M, ArrFrm ρ w m0 M b n (ovl g old i) → Triple (At pc L M keep outp)
      (At pc' L' (writeLog M [(b + 4 * i, 4, BitVec.ofNat 64 v)]) keep outp))
    (hi : i < n) (hgv : v = g i) (hv : v < 2 ^ 32) :
    Triple (ASt ρ w m0 b n keep outp pc L (ovl g old i))
      (ASt ρ w m0 b n keep outp pc' L' (ovl g old (i + 1))) :=
  fun c ⟨M, hI, hc⟩ => Triple.rmap (fun _ h => ⟨_, hI.step hi hv hgv, h⟩) (h M hI) c hc

open Vsa.Logic in
/-- `Triple.countup` from a lower bound `lo`. -/
theorem Triple.countup_from {P : Nat → Vsa.Machine.Config → Prop} {Q : Vsa.Machine.Config → Prop}
    {lo n : Nat} (step : ∀ i, lo ≤ i → i + 1 < n → Triple (P i) (P (i + 1)))
    (last : Triple (P (n - 1)) Q) : ∀ i, lo ≤ i → i < n → Triple (P i) Q := by
  suffices h : ∀ k i, lo ≤ i → i + k + 1 = n → Triple (P i) Q from
    fun i h1 h2 => h (n - 1 - i) i h1 (by omega)
  intro k
  induction k with
  | zero => intro i _ hi; rw [show i = n - 1 by omega]; exact last
  | succ k ih => intro i h1 hi; exact Triple.seq (step i h1 (by omega)) (ih (i + 1) (by omega) (by omega))

end Tom.Machine
