import Tom.Machine.Kit.MeetHeap

/-!
# Allocating calls that place or free several blocks at once

`Kit/MeetHeap.lean`'s `HContract` places one `site` per call. `mp_init_multi(&a, &b, …, NULL)`
places one fresh block per struct and `mp_clear_multi(&a, &b, …, NULL)` retires one per struct.
This file is the same meet with a list of sites, additively (nothing of `MeetHeap.lean` changes):

* `PlaceM hin I J`: where a call leaves one of its sites — a `Place` (retired, kept, fresh,
  re-placed), or a nonempty block **in the arena and off every block of `hin`** (`foot`; what
  `mp_init_multi`'s post gives for each new block: `Heap.blk` and `Apart.off`, without
  `malloc`'s alignment). Its three uses (`disj`, `cov`, `ram`) are `Place`'s.
* `HPostN`: `HPost` with the sites `sites`, their placements `J s`, the new blocks **pairwise
  apart** (`apart`: two fresh blocks of one call do not meet), the footprint after inside the
  one before and the sites' old bytes.
* `Iv.updN ρ σ sites J`: one `Iv.upd` layer per site (`Iv.upd (Iv.updN ρ σ ss J) (σ s) (J s)`),
  so a concrete list unfolds to the nested layers of one-site calls.
* `HContractN.after`: **soundness rebuilt from the placements** as in `HContract.after`: a
  placed site misses every other region (`PlaceM.disj` against an off region; `apart` against
  another site), kinds by `Kind.pushH` (unchanged), the checkpoint's frame, footprint, cover,
  off and RAM facts. The callee's sites are written names, so `SepPres` makes `σ` injective on
  them (`inj`).
* `call_heapN`: the `jal` rule, `call_heap`'s arguments and defaults.

Iris meaning: the state after a call is an ordinary
`St`/`HP` pair (sound layout, `AHeap` at `hout`, every region `Off`), so `aheap_isHeap`,
`off_split`, `region_blockOwn` and `sound_split` apply to it unchanged; `Kit/MeetHeapNIris.lean`
adds the one multi-site fact: the sites' bytes split into one `blockOwn` per site.
-/

namespace Tom.Machine

open Vsa.Sim Tom.Machine.Api.Alloc Tom.Machine.Api.Heap

/-! ## Placements -/

/-- Where a multi-site call leaves one site (before at `I`): a one-site `Place`, or a nonempty
block in the arena off every block of `H`. -/
inductive PlaceM (H : List (Nat × Nat)) (I : Iv) : Iv → Prop
  | place {J : Iv} (h : Place H I J) : PlaceM H I J
  | foot {J : Iv} (hn : 0 < J.len) (hlo : heapStart ≤ J.base) (hhi : J.base + J.len ≤ heapEnd)
      (hd : ∀ e ∈ H, ∀ a, J.In a → ¬ InBlk e a) : PlaceM H I J

theorem PlaceM.foot_in {H : List (Nat × Nat)} {J : Iv} (hlo : heapStart ≤ J.base) (hhi : J.base + J.len ≤ heapEnd)
    (hd : ∀ e ∈ H, ∀ a, J.In a → ¬ InBlk e a) {a : Nat} (ha : J.In a) : Foot H a :=
  .inr ⟨by have := ha.1; omega, by have := ha.2; omega, fun e he hb => hd e he a ha hb⟩

/-- A nonempty block of the footprint misses every off region. -/
theorem Off.disj_footB {K : Iv} {H : List (Nat × Nat)} (h : Off K H) {J : Iv} (hn : 0 < J.len)
    (hlo : heapStart ≤ J.base) (hhi : J.base + J.len ≤ heapEnd) (hf : ∀ a, J.In a → Foot H a) : J.Disj K := by
  unfold Iv.Disj Disj
  by_cases h0 : K.len = 0
  · have := h.edge h0; omega
  · refine Classical.byContradiction fun hc => ?_
    by_cases hle : K.base ≤ J.base
    · exact h.pt J.base ⟨hle, by omega⟩ (.inl (hf _ ⟨Nat.le_refl _, by omega⟩))
    · exact h.pt K.base ⟨Nat.le_refl _, by omega⟩ (.inl (hf _ ⟨by omega, by omega⟩))

theorem PlaceM.disj {H : List (Nat × Nat)} {I J K : Iv} (hp : PlaceM H I J) (ho : Off K H) (hI : I.Disj K) :
    J.Disj K := by
  cases hp with
  | place h => exact h.disj ho hI
  | foot hn hlo hhi hd => exact ho.disj_footB hn hlo hhi fun a ha => PlaceM.foot_in hlo hhi hd ha

theorem PlaceM.cov {H : List (Nat × Nat)} {I J : Iv} (hp : PlaceM H I J) {a : Nat} (ha : J.In a) :
    Foot H a ∨ I.In a := by
  cases hp with
  | place h => exact h.cov ha
  | foot _ hlo hhi hd => exact .inl (PlaceM.foot_in hlo hhi hd ha)

theorem PlaceM.ram {H : List (Nat × Nat)} {I J : Iv} (hp : PlaceM H I J) (hI : Ram I.base I.len) :
    Ram J.base J.len := by
  cases hp with
  | place h => exact h.ram hI
  | foot _ hlo hhi _ =>
    have eS : heapStart = 0x80019d10 := rfl; have eE : heapEnd = 0x87800000 := rfl
    exact ⟨by omega, by omega, .inr (by unfold tohostAddr; omega)⟩

/-! ## The layout after: one layer per site -/

section
variable {ι κR : Type} [DecidableEq ι]

/-- The sites `ss` re-placed at `J`, one `Iv.upd` layer each (the first outermost). -/
def Iv.updN (ρ : ι → Iv) (σ : κR → ι) : List κR → (κR → Iv) → ι → Iv
  | [], _ => ρ
  | s :: ss, J => Iv.upd (Iv.updN ρ σ ss J) (σ s) (J s)

theorem Iv.updN_nil (ρ : ι → Iv) (σ : κR → ι) (J : κR → Iv) : Iv.updN ρ σ [] J = ρ := rfl

theorem Iv.updN_cons (ρ : ι → Iv) (σ : κR → ι) (s : κR) (ss : List κR) (J : κR → Iv) :
    Iv.updN ρ σ (s :: ss) J = Iv.upd (Iv.updN ρ σ ss J) (σ s) (J s) := rfl

/-- A region no site maps to keeps its interval. -/
theorem Iv.updN_out {ρ : ι → Iv} {σ : κR → ι} {J : κR → Iv} {r : ι} :
    ∀ {ss : List κR}, (∀ t ∈ ss, σ t ≠ r) → Iv.updN ρ σ ss J r = ρ r
  | [], _ => rfl
  | s :: ss, h => by
    simp only [Iv.updN, Iv.upd]
    split
    · next e => exact absurd e.symm (h s (List.mem_cons_self ..))
    · exact Iv.updN_out fun t ht => h t (List.mem_cons_of_mem _ ht)

/-- A site's image (no other site maps there) is at its placement. -/
theorem Iv.updN_at {ρ : ι → Iv} {σ : κR → ι} {J : κR → Iv} {s : κR} :
    ∀ {ss : List κR}, s ∈ ss → (∀ t ∈ ss, σ t = σ s → t = s) → Iv.updN ρ σ ss J (σ s) = J s
  | [], hs, _ => absurd hs List.not_mem_nil
  | t :: ss, hs, h => by
    simp only [Iv.updN, Iv.upd]
    split
    · next e => rw [h t (List.mem_cons_self ..) e.symm]
    · next e =>
      rcases List.mem_cons.1 hs with rfl | hs
      · exact absurd rfl e
      · exact Iv.updN_at hs fun t' ht' => h t' (List.mem_cons_of_mem _ ht')

end

/-! ## Multi-site contracts -/

/-- `r` is the image of one of the sites `ss`. -/
abbrev SiteImg {ι κR : Type} (σ : κR → ι) (ss : List κR) (r : ι) : Prop := ∃ s ∈ ss, σ s = r

/-- Byte `a` lies in one of the sites' regions. -/
abbrev InSite {κR : Type} (lay : κR → Iv) (ss : List κR) (a : Nat) : Prop := ∃ s ∈ ss, (lay s).In a

/-- What a multi-site callee leaves, in its names (each site `s ∈ sites` placed at `J s`). -/
structure HPostN {R : Type} (lay : R → Iv) (ws sites : List R) (out : R → Kind) (J : R → Iv)
    (hin hout : List (Nat × Nat)) (m M : Mem) : Prop where
  wit : ∀ r, r ∈ ws → r ∉ sites → (out r).Fits (lay r) ∧ (out r).Wit (lay r) M
  wsite : ∀ s, s ∈ sites → (out s).Fits (J s) ∧ (out s).Wit (J s) M
  place : ∀ s, s ∈ sites → PlaceM hin (lay s) (J s)
  /-- The new placements pairwise apart. -/
  apart : ∀ s, s ∈ sites → ∀ t, t ∈ sites → s ≠ t → (J s).Disj (J t)
  frame : HFrm lay ws hin m M
  heap : AHeap M hout
  foot : ∀ a, Foot hout a → Foot hin a ∨ InSite lay sites a
  off : ∀ s, s ∈ sites → Off (J s) hout

open LeanRV64DExecutable Vsa Vsa.Logic

/-- **A multi-site allocating contract**: `HContract` with a list of `sites` placed at
`site' p x s`. -/
structure HContractN where
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
  sites : List R
  site' : P → X → R → Iv
  hin : P → List (Nat × Nat)
  hout : P → X → List (Nat × Nat)
  Res : P → Prop
  Q : P → X → Prop
  fits : ∀ p r, (kind p r).Fits (lay p r)
  sites_ws : ∀ s, s ∈ sites → s ∈ ws
  sites_w : ∀ s, s ∈ sites → isW s = true
  out_ind : ∀ p x r, r ∈ ws → r ∉ sites → (out p x r).isRam = false → (out p x r).indep = true
  pos : ∀ p, Res p → ∀ r, 0 < (lay p r).len ∨ (lay p r).base < heapStart ∨ heapEnd ≤ (lay p r).base
  spec : ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res p →
    Sound (lay p) isW → Bundle (lay p) (kind p) m → AHeap m (hin p) → (∀ r, Off (lay p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPostN (lay p) ws sites (out p x) (site' p x) (hin p) (hout p x) m M)

attribute [instance] HContractN.deq

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι}

/-- `σ` is injective on the callee's written names. -/
theorem sepPres_inj {κR : Type} [DecidableEq κR] {isWc : κR → Bool} {σ : κR → ι} {ks : List κR}
    (hsep : SepPres isW isWc σ ks = true) (hks : ∀ k, k ∈ ks) {k l : κR} (hk : isWc k = true) (hne : k ≠ l) :
    σ k ≠ σ l := fun e => by
  have := sepPres_sep hsep hks (k := k) (l := l) (by simp [Sep, hne, hk])
  simp [Sep, e] at this

/-- **The state after a multi-site call** (`HContract.after` with a list of sites). -/
theorem HContractN.after (C : HContractN) (p : C.P) (x : C.X) (σ : C.R → ι) {κ : ι → Kind}
    {H0 : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m M M' : Mem}
    (hSt : St ρ isW W κ m M) (hp : HP ρ isW H0 (C.hin p) Wr0 m0 m)
    (hsub : ∀ r, (C.lay p r).Sub (ρ (σ r))) (hsep : SepPres isW C.isW σ C.all = true)
    (hw : (C.ws.map σ).all isW = true) (hWw : W.all isW = true)
    (hpo : HPostN (C.lay p) C.ws C.sites (C.out p x) (C.site' p x) (C.hin p) (C.hout p x) M M') :
    St (Iv.updN ρ σ C.sites (C.site' p x)) isW W (Kind.pushH σ C.ws κ (C.out p x)) M' M' ∧
      HP (Iv.updN ρ σ C.sites (C.site' p x)) isW H0 (C.hout p x) Wr0 m0 M' := by
  have hwσ : ∀ k ∈ C.ws, isW (σ k) = true := fun k hk =>
    List.all_eq_true.1 hw (σ k) (List.mem_map_of_mem hk)
  have hsw : ∀ s ∈ C.sites, isW (σ s) = true := fun s hs => hwσ s (C.sites_ws s hs)
  -- the layout after at a site's image, and off the images
  have hS : ∀ s ∈ C.sites, Iv.updN ρ σ C.sites (C.site' p x) (σ s) = C.site' p x s := fun s hs =>
    Iv.updN_at hs fun t ht e => Classical.byContradiction fun hne =>
      sepPres_inj hsep C.hall (C.sites_w t ht) hne e
  have hN : ∀ r, (∀ s ∈ C.sites, σ s ≠ r) → Iv.updN ρ σ C.sites (C.site' p x) r = ρ r := fun r h =>
    Iv.updN_out h
  -- a region that is no site's image misses every site's region
  have dsite : ∀ r, (∀ s ∈ C.sites, σ s ≠ r) → ∀ s ∈ C.sites, (ρ r).Disj (ρ (σ s)) := fun r hr s hs =>
    hSt.sound r (σ s) (by simp [Sep, Ne.symm (hr s hs), hsw s hs])
  have inW : ∀ a, InAny (C.lay p) C.ws a → ∃ k ∈ C.ws, (ρ (σ k)).In a := fun a ha => by
    obtain ⟨k, hk, hx⟩ := ha.exists
    have := hsub k
    exact ⟨k, hk, by unfold Iv.Sub Iv.In at *; omega⟩
  have miss : ∀ r, (∀ k ∈ C.ws, σ k ≠ r) → ∀ a, (ρ r).In a → ¬ InAny (C.lay p) C.ws a := by
    intro r hr a hx ha
    obtain ⟨k, hk, hxk⟩ := inW a ha
    have := hSt.sound r (σ k) (by simp [Sep, Ne.symm (hr k hk), hwσ k hk])
    unfold Iv.Disj Disj Iv.In at *; omega
  have hheapM := hp.heapAt hSt
  -- a site's region against an off region `t` it is `Sep` from
  have sdisj : ∀ s ∈ C.sites, ∀ t, σ s ≠ t → (C.site' p x s).Disj (ρ t) := fun s hs t ht =>
    (hpo.place s hs).disj (hp.off t)
      (hSt.sound.sub (hsub s) (Iv.sub_self _) (by simp [Sep, ht, hsw s hs]))
  refine ⟨⟨?_, ?_, Frm.refl _ _⟩, ⟨hpo.heap, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- soundness, rebuilt from the placements
    intro r t h
    have hrt : r ≠ t := fun e => by simp [Sep, e] at h
    by_cases hr : SiteImg σ C.sites r
    · obtain ⟨s, hs, rfl⟩ := hr
      rw [hS s hs]
      by_cases ht : SiteImg σ C.sites t
      · obtain ⟨s', hs', rfl⟩ := ht
        rw [hS s' hs']
        exact hpo.apart s hs s' hs' fun e => hrt (by rw [e])
      · have ht' : ∀ s' ∈ C.sites, σ s' ≠ t := fun s' hs' e => ht ⟨s', hs', e⟩
        rw [hN t ht']; exact sdisj s hs t hrt
    · have hr' : ∀ s ∈ C.sites, σ s ≠ r := fun s hs e => hr ⟨s, hs, e⟩
      rw [hN r hr']
      by_cases ht : SiteImg σ C.sites t
      · obtain ⟨s', hs', rfl⟩ := ht
        rw [hS s' hs']; exact Disj.symm (sdisj s' hs' r (Ne.symm hrt))
      · have ht' : ∀ s' ∈ C.sites, σ s' ≠ t := fun s' hs' e => ht ⟨s', hs', e⟩
        rw [hN t ht']; exact hSt.sound r t h
  · -- the witnesses
    intro r
    unfold Kind.pushH
    cases hf : C.ws.find? (fun k => decide (σ k = r)) with
    | some k =>
      obtain ⟨hk, hσ⟩ := find?_some_mem hf
      subst hσ
      dsimp only
      by_cases hks : k ∈ C.sites
      · rw [hS k hks]; exact hpo.wsite k hks
      · have hne : ∀ s ∈ C.sites, σ s ≠ σ k := fun s hs =>
          sepPres_inj hsep C.hall (C.sites_w s hs) (fun e => hks (e ▸ hs))
        rw [hN _ hne]
        cases hram : (C.out p x k).isRam
        · exact ⟨(hpo.wit k hk hks).1.mono (hsub k),
            (hpo.wit k hk hks).2.indep (C.out_ind p x k hk hks hram)⟩
        · rw [Kind.eq_ram hram]; exact ⟨trivial, hp.ram (σ k) (hwσ k hk)⟩
    | none =>
      dsimp only
      have hr : ∀ k ∈ C.ws, σ k ≠ r := fun k hk e => by
        have := List.find?_eq_none.1 hf k hk; simp [e] at this
      rw [hN r fun s hs => hr s (C.sites_ws s hs)]
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
    rcases hpo.foot a ha with h1 | ⟨s, hs, h1⟩
    · exact hp.foot a h1
    · exact hp.cov _ (hsw s hs) a (by have := hsub s; unfold Iv.Sub Iv.In at *; omega)
  · -- the written regions covered
    intro r hr a ha
    by_cases hrs : SiteImg σ C.sites r
    · obtain ⟨s, hs, rfl⟩ := hrs
      rw [hS s hs] at ha
      rcases (hpo.place s hs).cov ha with h1 | h1
      · exact hp.foot a h1
      · exact hp.cov _ (hsw s hs) a (by have := hsub s; unfold Iv.Sub Iv.In at *; omega)
    · rw [hN r fun s hs e => hrs ⟨s, hs, e⟩] at ha; exact hp.cov r hr a ha
  · -- every region off the allocator after
    intro r
    by_cases hrs : SiteImg σ C.sites r
    · obtain ⟨s, hs, rfl⟩ := hrs
      rw [hS s hs]; exact hpo.off s hs
    · have hr' : ∀ s ∈ C.sites, σ s ≠ r := fun s hs e => hrs ⟨s, hs, e⟩
      rw [hN r hr']
      refine (hp.off r).mono fun a hx hf => hf.imp (fun hf' => (hpo.foot a hf').resolve_right fun ⟨s, hs, hl⟩ => ?_) id
      have := dsite r hr' s hs; have := hsub s
      unfold Iv.Disj Disj Iv.Sub Iv.In at *; omega
  · -- the written regions are RAM
    intro r hr
    by_cases hrs : SiteImg σ C.sites r
    · obtain ⟨s, hs, rfl⟩ := hrs
      rw [hS s hs]
      exact (hpo.place s hs).ram (Ram.sub (hp.ram _ (hsw s hs)) (hsub s).1 (hsub s).2)
    · rw [hN r fun s hs e => hrs ⟨s, hs, e⟩]; exact hp.ram r hr

/-- **Run a multi-site contract** from its entry at a checkpoint. -/
theorem HContractN.run (C : HContractN) (p : C.P) (σ : C.R → ι) {κ : ι → Kind}
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
        St (Iv.updN ρ σ C.sites (C.site' p x)) isW W (Kind.pushH σ C.ws κ (C.out p x)) M' M' ∧
        HP (Iv.updN ρ σ C.sites (C.site' p x)) isW H0 (C.hout p x) Wr0 m0 M') := by
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

/-- **The multi-site call rule**: `call_heap` for an `HContractN`; the continuation gets the
sites placed (`Iv.updN`), the kinds by `Kind.pushH`, a fresh `St` and the new checkpoint. -/
theorem call_heapN (C : HContractN) (p : C.P) (σ : C.R → ι) {κ : ι → Kind}
    {H0 : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m M : Mem}
    (hSt : St ρ isW W κ m M) (hp : HP ρ isW H0 (C.hin p) Wr0 m0 m)
    {base : Nat} {code : List (BitVec 32)} (hc : CodeAt M base code)
    {pc : BitVec 64} (w : BitVec 32) (imm : BitVec 21) (ret : BitVec 64) {L K : GRegs} {outp : Array String}
    {Q : Vsa.Machine.Config → Prop} (hres : C.Res p)
    (k : ∀ x M', C.Q p x →
      St (Iv.updN ρ σ C.sites (C.site' p x)) isW W (Kind.pushH σ C.ws κ (C.out p x)) M' M' →
      HP (Iv.updN ρ σ C.sites (C.site' p x)) isW H0 (C.hout p x) Wr0 m0 M' →
      Triple (At ret (C.rets p x ret ++ (Abi.ofL (((1, ret) :: dropRa L) ++ K)).keep) M' K outp) Q)
    (hsub : ∀ r, (C.lay p r).Sub (ρ (σ r)))
    (hk : ∀ r, C.kind p r = κ (σ r))
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
