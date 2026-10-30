import Tom.Machine.Kit.Meet
import Tom.Machine.Fn.AllocRun
import Tom.Machine.Api.Heap

/-!
# The meet with the heap: heap checkpoints, placed sites, `call_heap`

`Kit/Meet.lean`'s state `St ρ isW W κ m M` says what the named regions hold at
`M` and that `M` differs from `m` only in the names `W`. The allocator does not
fit it: its footprint `Foot H` (globals, the arena minus the live blocks) is a
set with holes for the client's blocks, and the block a `calloc` returns gets its
placement at the call. This file adds both without changing `St`:

* **Heap checkpoint** `HP ρ isW H0 H Wr0 m0 m`: at the memory `m` of the last
  allocator call the heap holds the blocks `H` (`AHeap`: `Heap` and
  `_impure_ptr`), every region lies **off** the allocator (`Off`: RAM, no byte
  of `AFoot H`; the client's digit arrays are live blocks, its structs and
  stack off the arena), and `m` differs from the entry `m0` only in `Foot H0`
  and the contract's written bytes `Wr0`. `St`'s base memory is the checkpoint:
  between allocator calls a function is an ordinary `St` proof (its writes are
  in its regions, off the footprint), and the `HP` hypothesis does not change.
* **Placed sites.** A region whose placement a call decides (a block `calloc`
  returns, a block `free` retires) is laid out as `Iv.nil` until then; an
  allocating callee (`HContract`) names one such `site` and its placement
  after (`Place`: `nil`, or a `Fresh` block). The caller's layout is updated
  there (`Iv.upd`), its kinds by the callee's (`Kind.pushH`: every written
  region takes the callee's kind, RAM included), and **soundness is rebuilt
  from `Fresh`**: a fresh block lies in `Foot H`, every other region is off it.
* **`call_heap`**: a `jal` to an `HContract` at a checkpoint; the continuation
  gets a fresh `St` (base memory the call's result) and the new `HP`.
* `HP.fin`: the frame from the entry (`Foot H0 ∨ Wr0`) and the heap at the end.
-/

namespace Tom.Machine

open Vsa.Sim Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-! ## The allocator's bytes, and regions off them -/

/-- `_impure_ptr`'s bytes (the wrappers read them; never written). -/
def ImpI (a : Nat) : Prop := impurePtr ≤ a ∧ a < impurePtr + 8

/-- The allocator's bytes with the blocks `H` live: its footprint and `_impure_ptr`. -/
def AFoot (H : List (Nat × Nat)) (a : Nat) : Prop := Foot H a ∨ ImpI a

/-- The heap with the blocks `H`, and `_impure_ptr` (what every allocator call reads). -/
structure AHeap (m : Mem) (H : List (Nat × Nat)) : Prop where
  heap : Heap m H
  imp : ImpureAt m

theorem AHeap.frame {m M : Mem} {H : List (Nat × Nat)} (h : AHeap m H)
    (hk : ∀ a, AFoot H a → M[a]? = m[a]?) : AHeap M H :=
  ⟨h.heap.frame fun a ha => hk a (.inl ha), fun i b hb => by
    have hi : i < 8 := by
      have := (List.getElem?_eq_some_iff.1 hb).1
      simpa [impureBytes] using this
    rw [hk _ (.inr ⟨by omega, by omega⟩)]; exact h.imp i b hb⟩

theorem foot_perm {H H' : List (Nat × Nat)} (hp : H.Perm H') {a : Nat} : Foot H a ↔ Foot H' a := by
  unfold Foot
  exact or_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    ⟨fun h e he => h e (hp.mem_iff.2 he), fun h e he => h e (hp.mem_iff.1 he)⟩))

theorem AHeap.perm {m : Mem} {H H' : List (Nat × Nat)} (h : AHeap m H) (hp : H.Perm H') : AHeap m H' :=
  ⟨h.heap.perm hp, h.imp⟩

/-- The null placement: no bytes, below every region. -/
def Iv.nil : Iv := ⟨0x80000000, 0⟩

/-- **`I` lies off the allocator** for the blocks `H`: at or above the RAM base,
no byte of `AFoot H`, and, if empty, outside the arena. -/
structure Off (I : Iv) (H : List (Nat × Nat)) : Prop where
  lo : 0x80000000 ≤ I.base
  pt : ∀ a, I.In a → ¬ AFoot H a
  edge : I.len = 0 → I.base < heapStart ∨ heapEnd ≤ I.base

/-- A sub-interval, nonempty or outside the arena. -/
theorem Off.sub {I J : Iv} {H : List (Nat × Nat)} (h : Off I H) (hs : J.Sub I)
    (hp : 0 < J.len ∨ J.base < heapStart ∨ heapEnd ≤ J.base) : Off J H :=
  ⟨by have := h.lo; have := hs.1; omega, fun a ha => h.pt a ⟨by have := hs.1; have := ha.1; omega,
    by have := hs.2; have := ha.2; omega⟩, fun h0 => hp.resolve_left (by omega)⟩

theorem Off.nil (H : List (Nat × Nat)) : Off Iv.nil H :=
  ⟨by decide, fun _ h => by simp only [Iv.In, Iv.nil] at h; omega, fun _ => .inl (by decide)⟩

theorem Ram.nil : Ram Iv.nil.base Iv.nil.len := ⟨by decide, by decide, .inl (by unfold tohostAddr; decide)⟩

/-- **Off-heap** (`Api/Heap.lean`: structs, stack, code) is off the allocator. -/
theorem Off.of_offHeap {I : Iv} {H : List (Nat × Nat)} (h : OffHeap I.base I.len) (hr : 0x80000000 ≤ I.base) :
    Off I H :=
  ⟨hr, fun a ha hf => by
    have eS : heapStart = 0x80019d10 := rfl; have eL : allocLo = 0x800188a0 := rfl
    rcases hf with hf | hi
    · exact h.off_foot ha.1 ha.2 hf
    · unfold ImpI impurePtr at hi; unfold OffHeap at h; have := ha.1; have := ha.2
      have eE : heapEnd = 0x87800000 := rfl; omega,
   fun _ => by
    have eS : heapStart = 0x80019d10 := rfl; have eL : allocLo = 0x800188a0 := rfl
    unfold OffHeap at h; omega⟩

/-- **A live block** (`MpLive`'s `digBlk`), nonempty, is off the allocator. -/
theorem Off.of_blk {I : Iv} {m : Mem} {H : List (Nat × Nat)} (hH : Heap m H) (he : (I.base, I.len) ∈ H)
    (hp : 0 < I.len) : Off I H :=
  have hb := Fn.Alloc.Heap.blk hH he
  ⟨by have e : heapStart = 0x80019d10 := rfl; simp only at hb; omega, fun a ha hf => by
    rcases hf with hf | hi
    · exact blk_off_foot hH he ⟨ha.1, ha.2⟩ hf
    · have e : heapStart = 0x80019d10 := rfl
      unfold ImpI impurePtr at hi; simp only at hb; have := ha.1; omega,
   fun h0 => absurd h0 (by omega)⟩

theorem Off.text (H : List (Nat × Nat)) : Off textIv H := Off.of_offHeap text_off_heap (by decide)

/-- An off region whose bytes are a live block, an off-arena range, … : by points. -/
theorem Off.mono {I : Iv} {H H' : List (Nat × Nat)} (h : Off I H)
    (hm : ∀ a, I.In a → AFoot H' a → AFoot H a) : Off I H' :=
  ⟨h.lo, fun a ha hf => h.pt a ha (hm a ha hf), h.edge⟩

theorem Off.perm {I : Iv} {H H' : List (Nat × Nat)} (h : Off I H) (hp : H.Perm H') : Off I H' :=
  h.mono fun _ _ hf => hf.imp (foot_perm hp).2 id

theorem Off.disj_nil {I : Iv} {H : List (Nat × Nat)} (h : Off I H) : Iv.nil.Disj I := by
  have := h.lo; unfold Iv.Disj Disj Iv.nil; simp only; omega

/-- **A fresh block misses every off region.** -/
theorem Off.disj_fresh {I : Iv} {H : List (Nat × Nat)} (h : Off I H) {q n : Nat} (hf : Fresh H q n)
    (hn : 0 < n) : I.Disj ⟨q, n⟩ := by
  unfold Iv.Disj Disj; simp only
  by_cases h0 : I.len = 0
  · have := h.edge h0; have := hf.lo; have := hf.hi; omega
  · refine Classical.byContradiction fun hc => ?_
    by_cases hle : I.base ≤ q
    · exact h.pt q ⟨hle, by omega⟩ ((.inl (hf.foot ⟨Nat.le_refl _, by omega⟩)))
    · exact h.pt I.base ⟨Nat.le_refl _, by omega⟩ ((.inl (hf.foot ⟨by omega, by omega⟩)))

/-- Where an allocating call leaves its site (before at `I`): retired, kept, or
a fresh nonempty block. -/
inductive Place (H : List (Nat × Nat)) (I : Iv) : Iv → Prop
  | nil : Place H I Iv.nil
  | keep : Place H I I
  | fresh {q n : Nat} (hf : Fresh H q n) (hn : 0 < n) : Place H I ⟨q, n⟩
  /-- Re-placed (`realloc`): fresh for the other blocks, the site's old block freed. -/
  | regrow {H' : List (Nat × Nat)} {q n : Nat} (hf : Fresh H' q n) (hn : 0 < n) (hH : H = (I.base, I.len) :: H') :
      Place H I ⟨q, n⟩

/-- A block fresh but for the site's old block `I` misses every off region apart from `I`. -/
theorem Off.disj_regrow {I K : Iv} {H' : List (Nat × Nat)} (h : Off K ((I.base, I.len) :: H')) (hI : I.Disj K)
    {q n : Nat} (hf : Fresh H' q n) (hn : 0 < n) : K.Disj ⟨q, n⟩ := by
  have hpt : ∀ a, K.In a → q ≤ a → a < q + n → False := fun a ha h1 h2 => by
    refine h.pt a ha (.inl (.inr ⟨by have := hf.lo; omega, by have := hf.hi; omega, fun e he hb => ?_⟩))
    rcases List.mem_cons.1 he with rfl | he
    · unfold Iv.Disj Disj at hI; unfold InBlk at hb; unfold Iv.In at ha; simp only at hb; omega
    · exact hf.disj e he a ⟨h1, h2⟩ hb
  unfold Iv.Disj Disj; simp only
  by_cases h0 : K.len = 0
  · have := h.edge h0; have := hf.lo; have := hf.hi; omega
  · refine Classical.byContradiction fun hc => ?_
    by_cases hle : K.base ≤ q
    · exact hpt q ⟨hle, by omega⟩ (Nat.le_refl _) (by omega)
    · exact hpt K.base ⟨Nat.le_refl _, by omega⟩ (by omega) (by omega)

theorem Place.disj {H : List (Nat × Nat)} {I J K : Iv} (hp : Place H I J) (ho : Off K H) (hI : I.Disj K) :
    J.Disj K := by
  cases hp with
  | nil => exact ho.disj_nil
  | keep => exact hI
  | fresh hf hn => exact Disj.symm (ho.disj_fresh hf hn)
  | regrow hf hn hH => subst hH; exact Disj.symm (ho.disj_regrow hI hf hn)

theorem Place.cov {H : List (Nat × Nat)} {I J : Iv} (hp : Place H I J) {a : Nat} (ha : J.In a) :
    Foot H a ∨ I.In a := by
  cases hp with
  | nil => simp only [Iv.In, Iv.nil] at ha; omega
  | keep => exact .inr ha
  | fresh hf _ => exact .inl (hf.foot ⟨ha.1, ha.2⟩)
  | regrow hf _ hH =>
    subst hH
    by_cases hb : I.In a
    · exact .inr hb
    · refine .inl (.inr ⟨by have := hf.lo; have := ha.1; simp only at this; omega,
        by have := hf.hi; have := ha.2; simp only at this; omega, fun e he he' => ?_⟩)
      rcases List.mem_cons.1 he with rfl | he
      · exact hb he'
      · exact hf.disj e he a ⟨ha.1, ha.2⟩ he'

theorem Place.ram {H : List (Nat × Nat)} {I J : Iv} (hp : Place H I J) (hI : Ram I.base I.len) :
    Ram J.base J.len := by
  cases hp with
  | nil => exact Ram.nil
  | keep => exact hI
  | fresh hf _ | regrow hf _ _ =>
    have := hf.lo; have := hf.hi
    have eS : heapStart = 0x80019d10 := rfl; have eE : heapEnd = 0x87800000 := rfl
    exact ⟨by simp only; omega, by simp only; omega, .inr (by unfold tohostAddr; simp only; omega)⟩

/-! ## Layout and kinds after an allocating call -/

section
variable {ι κR : Type} [DecidableEq ι] [DecidableEq κR]

/-- One region re-placed. -/
def Iv.upd (ρ : ι → Iv) (r : ι) (I : Iv) : ι → Iv := fun r' => if r' = r then I else ρ r'

/-- The caller's kinds after an allocating callee wrote `wsc`: each written
region takes the callee's kind (RAM included: a freed or cleared region is
forgotten), the others keep theirs. -/
def Kind.pushH (σ : κR → ι) (wsc : List κR) (κ : ι → Kind) (κc : κR → Kind) (r : ι) : Kind :=
  match wsc.find? (fun k => decide (σ k = r)) with
  | some k => κc k
  | none => κ r

end

/-! ## The heap checkpoint -/

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind}

/-- **The heap at a checkpoint `m`** (see the module doc): `AHeap m H`, every
region off the allocator, `m` from the entry `m0` changed only in `Foot H0` and
`Wr0`, and the current footprint and the written regions inside those. -/
structure HP (ρ : ι → Iv) (isW : ι → Bool) (H0 H : List (Nat × Nat)) (Wr0 : Nat → Prop) (m0 m : Mem) :
    Prop where
  heap : AHeap m H
  frm0 : Keep (fun a => Wr0 a ∨ Foot H0 a) m0 m
  foot : ∀ a, Foot H a → Wr0 a ∨ Foot H0 a
  cov : ∀ r, isW r = true → ∀ a, (ρ r).In a → Wr0 a ∨ Foot H0 a
  off : ∀ r, Off (ρ r) H
  ram : ∀ r, isW r = true → Ram (ρ r).base (ρ r).len

omit [DecidableEq ι] in
/-- **The entry checkpoint.** -/
theorem HP.entry {H : List (Nat × Nat)} {Wr0 : Nat → Prop} {m : Mem} (hh : AHeap m H)
    (hoff : ∀ r, Off (ρ r) H) (hcov : ∀ r, isW r = true → ∀ a, (ρ r).In a → Wr0 a)
    (hram : ∀ r, isW r = true → Ram (ρ r).base (ρ r).len) :
    HP ρ isW H H Wr0 m m :=
  ⟨hh, fun _ _ => rfl, fun _ h => .inr h, fun r hr a ha => .inl (hcov r hr a ha), hoff, hram⟩

omit [DecidableEq ι] in
/-- The blocks reordered. -/
theorem HP.perm {H0 H H' : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m : Mem}
    (h : HP ρ isW H0 H Wr0 m0 m) (hp : H.Perm H') : HP ρ isW H0 H' Wr0 m0 m :=
  { h with heap := h.heap.perm hp, foot := fun a ha => h.foot a ((foot_perm hp).2 ha)
           off := fun r => (h.off r).perm hp }

omit [DecidableEq ι] in
/-- A layout equal by computation. -/
theorem HP.congrL {H0 H : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m : Mem} {ρ' : ι → Iv}
    (h : HP ρ isW H0 H Wr0 m0 m) (hl : ∀ r, ρ r = ρ' r) : HP ρ' isW H0 H Wr0 m0 m := by
  have : ρ = ρ' := funext hl
  subst this; exact h

theorem St.congrL {m M : Mem} {ρ' : ι → Iv} (h : St ρ isW W κ m M) (hl : ∀ r, ρ r = ρ' r) :
    St ρ' isW W κ m M := by
  have : ρ = ρ' := funext hl
  subst this; exact h

omit [DecidableEq ι] in
/-- Bytes in a written region of `W` are covered. -/
theorem HP.covW {H0 H : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m : Mem} (hp : HP ρ isW H0 H Wr0 m0 m)
    (hW : W.all isW = true) {a : Nat} (ha : InAny ρ W a) : Wr0 a ∨ Foot H0 a := by
  obtain ⟨r, hr, hx⟩ := ha.exists
  exact hp.cov r (List.all_eq_true.1 hW r hr) a hx

/-- The heap at a later memory of the same checkpoint. -/
theorem HP.heapAt {H0 H : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m M : Mem}
    (hp : HP ρ isW H0 H Wr0 m0 m) (h : St ρ isW W κ m M) : AHeap M H :=
  hp.heap.frame fun a ha => h.frm a fun hx => by
    obtain ⟨r, _, hxr⟩ := hx.exists
    exact (hp.off r).pt a hxr ha

/-- **The end**: the frame from the entry (for `Wr0 = InAny ρc ws`, the
contract's `HFrm ρc ws H0 m0 M`) and the heap. -/
theorem HP.fin {H0 H : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m M : Mem}
    (hp : HP ρ isW H0 H Wr0 m0 m) (h : St ρ isW W κ m M) (hW : W.all isW = true := by decide) :
    Keep (fun a => Wr0 a ∨ Foot H0 a) m0 M ∧ AHeap M H :=
  ⟨fun a ha => (h.frm a fun hx => ha (hp.covW hW hx)).trans (hp.frm0 a ha), hp.heapAt h⟩

end

/-! ## A store that re-kinds a region -/

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}
  {pc pc' : BitVec 64} {L0 L L' K : GRegs} {o : Array String} {Q : Vsa.Machine.Config → Prop}

/-- **A segment storing `log` inside region `r`**, which then holds the kind `k'`
(its witness at the new memory given): a struct initialised in place, a field
of a dead struct. -/
theorem St.seqK (h : St ρ isW W κ m M) (r : ι) {log : List WEntry} (k' : Kind)
    (hseg : Vsa.Logic.Triple (At pc L M K o) (At pc' L' (writeLog M log) K o))
    (hnew : k'.Fits (ρ r) ∧ k'.Wit (ρ r) (writeLog M log))
    (k : ∀ M', St ρ isW W (Kind.set κ r k') m M' → Vsa.Logic.Triple (At pc' L' M' K o) Q)
    (hlog : LogIn ρ r log := by login) (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Vsa.Logic.Triple (At pc L0 M K o) Q :=
  (Vsa.Logic.Triple.seq hseg (k _ (h.step (Frm.store hlog) (by simp [hw]) hW
    (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; simpa [Kind.set] using hnew)
    (fun r' hr' => by simp only [List.mem_singleton] at hr'; simp [Kind.set, hr'])))).pre hL

end

/-! ## An allocation site beside a layout -/

section
variable {R : Type} [DecidableEq R] {ρ : R → Iv} {isW : R → Bool}

/-- A layout with one more region `none`: an unplaced allocation site (`Iv.nil`). -/
def Site.lay (ρ : R → Iv) : Option R → Iv
  | none => Iv.nil
  | some r => ρ r

def Site.wr (isW : R → Bool) : Option R → Bool
  | none => true
  | some r => isW r

def Site.kind (κ : R → Kind) : Option R → Kind
  | none => .ram
  | some r => κ r

/-- The site is disjoint from every region at or above the RAM base. -/
theorem Site.sound (hS : Sound ρ isW) (hlo : ∀ r, 0x80000000 ≤ (ρ r).base) : Sound (Site.lay ρ) (Site.wr isW) := by
  intro r t h
  cases r <;> cases t
  · simp [Sep] at h
  · rename_i t; have := hlo t; simp only [Site.lay, Iv.Disj, Disj, Iv.nil]; omega
  · rename_i r; have := hlo r; simp only [Site.lay, Iv.Disj, Disj, Iv.nil]; omega
  · rename_i r t; exact hS r t (by simpa [Sep, Site.wr] using h)

theorem Site.bundle {κ : R → Kind} {m : Mem} (hB : Bundle ρ κ m) : Bundle (Site.lay ρ) (Site.kind κ) m
  | none => ⟨trivial, Ram.nil⟩
  | some r => hB r

end

/-! ## Allocating contracts -/

/-- What an allocating callee leaves, in its names (`site` placed at `J`). -/
structure HPost {R : Type} (lay : R → Iv) (ws : List R) (site : R) (out : R → Kind) (J : Iv)
    (hin hout : List (Nat × Nat)) (m M : Mem) : Prop where
  wit : ∀ r, r ∈ ws → r ≠ site → (out r).Fits (lay r) ∧ (out r).Wit (lay r) M
  wsite : (out site).Fits J ∧ (out site).Wit J M
  place : Place hin (lay site) J
  frame : HFrm lay ws hin m M
  heap : AHeap M hout
  foot : ∀ a, Foot hout a → Foot hin a ∨ (lay site).In a
  off : Off J hout

open LeanRV64DExecutable Vsa Vsa.Logic

/-- **An allocating contract**: `Contract`'s fields, the heap before (`hin`) and
after (`hout`), the `site` it places (`site'`), result-dependent returns. -/
structure HContract where
  P : Type
  X : Type
  R : Type
  [deq : DecidableEq R]
  all : List R
  hall : ∀ r, r ∈ all
  entry : BitVec 64
  args : P → GRegs
  rets : P → X → BitVec 64 → GRegs
  lay : P → R → Iv
  kind : P → R → Kind
  out : P → X → R → Kind
  isW : R → Bool
  ws : List R
  site : R
  site' : P → X → Iv
  hin : P → List (Nat × Nat)
  hout : P → X → List (Nat × Nat)
  Res : P → Prop
  Q : P → X → Prop
  fits : ∀ p r, (kind p r).Fits (lay p r)
  site_ws : site ∈ ws
  site_w : isW site = true
  out_ind : ∀ p x r, r ∈ ws → r ≠ site → (out p x r).isRam = false → (out p x r).indep = true
  pos : ∀ p, Res p → ∀ r, 0 < (lay p r).len ∨ (lay p r).base < heapStart ∨ heapEnd ≤ (lay p r).base
  spec : ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay p) ws site (out p x) (site' p x) (hin p) (hout p x) m M)

attribute [instance] HContract.deq

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι}

theorem find?_some_mem {κR : Type} {σ : κR → ι} {wsc : List κR} {r : ι} {k : κR}
    (hf : wsc.find? (fun k => decide (σ k = r)) = some k) : k ∈ wsc ∧ σ k = r :=
  ⟨List.mem_of_find?_eq_some hf, of_decide_eq_true (List.find?_some (p := fun k => decide (σ k = r)) hf)⟩

/-- `SepPres` gives `Sep` of the images. -/
theorem sepPres_sep {κR : Type} [DecidableEq κR] {isWc : κR → Bool} {σ : κR → ι} {ks : List κR}
    (hsep : SepPres isW isWc σ ks = true) (hks : ∀ k, k ∈ ks) {k l : κR} (h : Sep isWc k l = true) :
    Sep isW (σ k) (σ l) = true := by
  have := List.all_eq_true.1 (List.all_eq_true.1 hsep k (hks k)) l (hks l)
  simp only [h, Bool.not_true, Bool.false_or] at this; exact this

/-- **The state after an allocating call** (the bundle, layout, heap and frame
pieces of `call_heap`). -/
theorem HContract.after (C : HContract) (p : C.P) (x : C.X) (σ : C.R → ι) {κ : ι → Kind}
    {H0 : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m M M' : Mem}
    (hSt : St ρ isW W κ m M) (hp : HP ρ isW H0 (C.hin p) Wr0 m0 m)
    (hsub : ∀ r, (C.lay p r).Sub (ρ (σ r))) (hsep : SepPres isW C.isW σ C.all = true)
    (hw : (C.ws.map σ).all isW = true) (hWw : W.all isW = true)
    (hpo : HPost (C.lay p) C.ws C.site (C.out p x) (C.site' p x) (C.hin p) (C.hout p x) M M') :
    St (Iv.upd ρ (σ C.site) (C.site' p x)) isW W (Kind.pushH σ C.ws κ (C.out p x)) M' M' ∧
      HP (Iv.upd ρ (σ C.site) (C.site' p x)) isW H0 (C.hout p x) Wr0 m0 M' := by
  have hwσ : ∀ k ∈ C.ws, isW (σ k) = true := fun k hk =>
    List.all_eq_true.1 hw (σ k) (List.mem_map_of_mem hk)
  have hs := hwσ C.site C.site_ws
  -- regions other than the site's are disjoint from it
  have dsite : ∀ r, r ≠ σ C.site → (ρ r).Disj (ρ (σ C.site)) := fun r hr =>
    hSt.sound r (σ C.site) (by simp [Sep, hr, hs])
  -- a byte of the callee's written regions is in a written region of ours
  have inW : ∀ a, InAny (C.lay p) C.ws a → ∃ k ∈ C.ws, (ρ (σ k)).In a := fun a ha => by
    obtain ⟨k, hk, hx⟩ := ha.exists
    have := hsub k
    exact ⟨k, hk, by unfold Iv.Sub Iv.In at *; omega⟩
  -- a region outside the callee's images misses its writes
  have miss : ∀ r, (∀ k ∈ C.ws, σ k ≠ r) → ∀ a, (ρ r).In a → ¬ InAny (C.lay p) C.ws a := by
    intro r hr a hx ha
    obtain ⟨k, hk, hxk⟩ := inW a ha
    have := hSt.sound r (σ k) (by simp [Sep, Ne.symm (hr k hk), hwσ k hk])
    unfold Iv.Disj Disj Iv.In at *; omega
  have hupd : ∀ r, r ≠ σ C.site → Iv.upd ρ (σ C.site) (C.site' p x) r = ρ r := fun r hr => by
    simp [Iv.upd, hr]
  have hupd_s : Iv.upd ρ (σ C.site) (C.site' p x) (σ C.site) = C.site' p x := by simp [Iv.upd]
  have hheapM := hp.heapAt hSt
  refine ⟨⟨?_, ?_, Frm.refl _ _⟩, ⟨hpo.heap, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- soundness, rebuilt from the placement
    intro r t h
    by_cases hr : r = σ C.site
    · subst hr
      have ht : t ≠ σ C.site := fun e => by simp [Sep, e] at h
      rw [hupd_s, hupd t ht]
      exact hpo.place.disj (hp.off t) (hSt.sound.sub (hsub C.site) (Iv.sub_self _) (by simp [Sep, Ne.symm ht, hs]))
    · by_cases ht : t = σ C.site
      · subst ht; rw [hupd_s, hupd r hr]
        exact Disj.symm (hpo.place.disj (hp.off r) (hSt.sound.sub (hsub C.site) (Iv.sub_self _) (by simp [Sep, Ne.symm hr, hs])))
      · rw [hupd r hr, hupd t ht]; exact hSt.sound r t h
  · -- the witnesses
    intro r
    unfold Kind.pushH
    cases hf : C.ws.find? (fun k => decide (σ k = r)) with
    | some k =>
      obtain ⟨hk, hσ⟩ := find?_some_mem hf
      subst hσ
      dsimp only
      by_cases hks : k = C.site
      · subst hks; rw [hupd_s]; exact hpo.wsite
      · have hne : σ k ≠ σ C.site := fun e => by
          have := sepPres_sep hsep C.hall (k := k) (l := C.site) (by simp [Sep, hks, C.site_w])
          simp [Sep, e] at this
        rw [hupd _ hne]
        cases hram : (C.out p x k).isRam
        · exact ⟨(hpo.wit k hk hks).1.mono (hsub k),
            (hpo.wit k hk hks).2.indep (C.out_ind p x k hk hks hram)⟩
        · rw [Kind.eq_ram hram]; exact ⟨trivial, hp.ram (σ k) (hwσ k hk)⟩
    | none =>
      dsimp only
      have hr : ∀ k ∈ C.ws, σ k ≠ r := fun k hk e => by
        have := List.find?_eq_none.1 hf k hk; simp [e] at this
      have hne : r ≠ σ C.site := fun e => hr C.site C.site_ws e.symm
      rw [hupd r hne]
      refine ⟨(hSt.wit r).1, Kind.reads (hSt.wit r).1 M M' (fun a ha => hpo.frame a fun hw' => ?_) (hSt.wit r).2⟩
      have hx : (ρ r).In a := by rcases ha with ha | ha; exact ha; exact ha.elim
      rcases hw' with hw' | hw'
      · exact miss r hr a hx hw'
      · exact (hp.off r).pt a hx (.inl hw')
  · -- the frame from the entry
    intro a ha
    rw [hpo.frame a fun hw' => ha (hw'.elim (fun h1 => by
        obtain ⟨k, hk, hx⟩ := inW a h1
        exact hp.cov _ (hwσ k hk) a hx) (fun h1 => hp.foot a h1)),
      hSt.frm a fun hx => ha (hp.covW hWw hx)]
    exact hp.frm0 a ha
  · -- the footprint after
    intro a ha
    rcases hpo.foot a ha with h1 | h1
    · exact hp.foot a h1
    · exact hp.cov _ hs a (by have := hsub C.site; unfold Iv.Sub Iv.In at *; omega)
  · -- the written regions covered
    intro r hr a ha
    by_cases hrs : r = σ C.site
    · subst hrs; rw [hupd_s] at ha
      rcases hpo.place.cov ha with h1 | h1
      · exact hp.foot a h1
      · exact hp.cov _ hs a (by have := hsub C.site; unfold Iv.Sub Iv.In at *; omega)
    · rw [hupd r hrs] at ha; exact hp.cov r hr a ha
  · -- every region off the allocator after
    intro r
    by_cases hrs : r = σ C.site
    · subst hrs; rw [hupd_s]; exact hpo.off
    · rw [hupd r hrs]
      refine (hp.off r).mono fun a hx hf => hf.imp (fun hf' => (hpo.foot a hf').resolve_right fun hl => ?_) id
      have := dsite r hrs; have := hsub C.site
      unfold Iv.Disj Disj Iv.Sub Iv.In at *; omega
  · -- the written regions are RAM
    intro r hr
    by_cases hrs : r = σ C.site
    · subst hrs; rw [hupd_s]; exact hpo.place.ram (Ram.sub (hp.ram _ hs) (hsub C.site).1 (hsub C.site).2)
    · rw [hupd r hrs]; exact hp.ram r hr

/-- **Run an allocating contract** from its entry at a checkpoint. -/
theorem HContract.run (C : HContract) (p : C.P) (σ : C.R → ι) {κ : ι → Kind}
    {H0 : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m M : Mem}
    (hSt : St ρ isW W κ m M) (hp : HP ρ isW H0 (C.hin p) Wr0 m0 m) {L K : GRegs} {outp : Array String}
    {ra : BitVec 64} (hres : C.Res p) (hra : ra.toNat % 4 = 0)
    (hsub : ∀ r, (C.lay p r).Sub (ρ (σ r))) (hk : ∀ r, C.kind p r = κ (σ r))
    (hsep : SepPres isW C.isW σ C.all = true) (hw : (C.ws.map σ).all isW = true) (hWw : W.all isW = true)
    (hargs : SubR ((1, ra) :: C.args p) (L ++ K))
    (hkeys : abiKeys.all (fun n => (lookupG n (L ++ K)).isSome) = true)
    (hK' : ∀ x, SubR K (C.rets p x ra ++ (Abi.ofL (L ++ K)).keep)) :
    Triple (At C.entry L M K outp)
      (fun cf => ∃ x M', At ra (C.rets p x ra ++ (Abi.ofL (L ++ K)).keep) M' K outp cf ∧ C.Q p x ∧
        St (Iv.upd ρ (σ C.site) (C.site' p x)) isW W (Kind.pushH σ C.ws κ (C.out p x)) M' M' ∧
        HP (Iv.upd ρ (σ C.site) (C.site' p x)) isW H0 (C.hout p x) Wr0 m0 M') := by
  intro c hc
  have hall : GHolds c.σ (L ++ K) := gholds_append.2 ⟨hc.regs, hc.keep⟩
  have hc' : At C.entry ((1, ra) :: C.args p) M (Abi.ofL (L ++ K)).keep outp c :=
    { hc with regs := hargs.gholds hall, keep := gholds_ofL hall hkeys }
  obtain ⟨c', hs, x, M', hat, hq, hpo⟩ := C.spec hra hres (hSt.sound.pull σ C.all C.hall hsub hsep)
    (hSt.wit.pull σ hsub hk (C.fits p)) (hp.heapAt hSt)
    (fun r => (hp.off (σ r)).sub (hsub r) (C.pos p hres r)) c hc'
  obtain ⟨h1, h2⟩ := C.after p x σ hSt hp hsub hsep hw hWw hpo
  exact ⟨c', hs, x, M', hat.cat (hK' x), hq, h1, h2⟩

open LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail

/-- **The allocating call rule**: `jal ra, C.entry` at `pc` at a heap checkpoint
(`hp`, the blocks `C.hin p`), then the continuation at `ret = pc + 4` with the
site placed, the caller's kinds updated, a fresh `St` and the new checkpoint. -/
theorem call_heap (C : HContract) (p : C.P) (σ : C.R → ι) {κ : ι → Kind}
    {H0 : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m M : Mem}
    (hSt : St ρ isW W κ m M) (hp : HP ρ isW H0 (C.hin p) Wr0 m0 m)
    {base : Nat} {code : List (BitVec 32)} (hc : CodeAt M base code)
    {pc : BitVec 64} (w : BitVec 32) (imm : BitVec 21) (ret : BitVec 64) {L K : GRegs} {outp : Array String}
    {Q : Vsa.Machine.Config → Prop} (hres : C.Res p)
    (k : ∀ x M', C.Q p x →
      St (Iv.upd ρ (σ C.site) (C.site' p x)) isW W (Kind.pushH σ C.ws κ (C.out p x)) M' M' →
      HP (Iv.upd ρ (σ C.site) (C.site' p x)) isW H0 (C.hout p x) Wr0 m0 M' →
      Triple (At ret (C.rets p x ret ++ (Abi.ofL (((1, ret) :: dropRa L) ++ K)).keep) M' K outp) Q)
    (hsub : ∀ r, (C.lay p r).Sub (ρ (σ r)) := by intro r; cases r <;> iv_omega)
    (hk : ∀ r, C.kind p r = κ (σ r) := by intro r; cases r <;> rfl)
    (hwd : WordIn base code pc.toNat w = true := by decide +kernel)
    (hdec : ∀ s : SequentialState RegisterType trivialChoiceSource,
      s.regs.get? Register.misa = some ((Vsa.Sim.initMisa) : RegisterType Register.misa) →
      s.regs.get? Register.cur_privilege = some ((Privilege.Machine) : RegisterType Register.cur_privilege) →
      s.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) →
      (ext_decode w).run s = .ok (instruction.JAL (imm, regidx.Regidx 0x01#5)) s :=
        by exact fun s h1 h2 h3 => decodeW s h1 h2 h3)
    (hword : ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append (w.extractLsb' 8 8)).append
      (w.extractLsb' 0 8)) = w := by decide)
    (hnotrvc : Sail.BitVec.extractLsb ((((w.extractLsb' 24 8).append (w.extractLsb' 16 8)).append
      (w.extractLsb' 8 8)).append (w.extractLsb' 0 8)) 1 0 = (0b11#2 : BitVec 2) := by decide)
    (hpc : pc + Functions.sign_extend (m := 64) imm = C.entry := by decide)
    (hal : C.entry.toNat % 4 = 0 := by decide) (hret : Sail.BitVec.addInt pc 4 = ret := by decide)
    (hra : ret.toNat % 4 = 0 := by decide)
    (hfe : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0 :=
      by exact ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩)
    (hsep : SepPres isW C.isW σ C.all = true := by decide) (hw : (C.ws.map σ).all isW = true := by decide)
    (hWw : W.all isW = true := by decide)
    (hLk : (keysG (dropRa L)).all (fun n => decide (2 ≤ n) && decide (n ≤ 31)) = true := by exact rfl)
    (hKk : (keysG K).all (fun n => decide (2 ≤ n) && decide (n ≤ 31)) = true := by exact rfl)
    (hargs : SubR ((1, ret) :: C.args p) (((1, ret) :: dropRa L) ++ K) := by exact rfl)
    (hkeys : abiKeys.all (fun n => (lookupG n (((1, ret) :: dropRa L) ++ K)).isSome) = true := by exact rfl)
    (hK' : ∀ x, SubR K (C.rets p x ret ++ (Abi.ofL (((1, ret) :: dropRa L) ++ K)).keep) := by
      intro _; exact rfl) :
    Triple (At pc L M K outp) Q := by
  have hj := jal_at (L := L) (L' := dropRa L) (keep := K) (outp := outp) (m := M) (hc.word hwd) hword hnotrvc
    hdec hfe (by rw [hpc]; exact hal) (fun _ h => (List.mem_filter.1 h).1)
    (fun n hn => by have := List.all_eq_true.1 hLk n hn; simpa using this)
    (fun n hn => by have := List.all_eq_true.1 hKk n hn; simpa using this)
  rw [hpc, hret] at hj
  exact Triple.seq hj (Triple.ex (C.run p σ hSt hp hres hra hsub hk hsep hw hWw hargs hkeys hK')
    fun x M' ⟨hq, hS', hP'⟩ => k x M' hq hS' hP')

end

end Tom.Machine
