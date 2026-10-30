import VsaIris.Vsa.SymGeom
import Tom.Machine.Kit.At
import Vsa.Densify

/-!
# ship-your-interpreter's symbolic executor on this image, and its adequacy for `At`

The executor runs a stretch of code as one closed computation `symRun C n s` and proves the residual
weakest precondition sound against `SWP`, the Iris-layer local run of `VsaIris/Vsa/SymRun.lean`
(`symRun_auto`). This file supplies

* the image of one function (`img base ws`: the words `ws` of `Tom/Machine/Code.lean` at
  `base`), its range `rT`, the text `T` (`rangeText`), the tracked registers `rs` (`regsOf`:
  the PC and the GPRs the code names, never `gp`) and the configuration `cfg base ws stops`;
* `textLoaded`: our `CodeAt m base ws` is the executor's `TextLoaded (T base ws) m`;
* **adequacy**: an `SWP` from an `At` state whose post `QAt` names the end state is a machine run
  to that state (`triple_of_swp`, exact; `tripleZ_of_swp`, up to zero-equivalence).

`SWP`'s machine model reads bytes totally (`getD 0`) and frames byte presence only outside the
owned set `S`. `At` fixes the memory exactly. So:

* `triple_of_swp` needs the owned bytes present at entry (`hpres`): they are then `live`
  (`VsaOk`) and stay present, and the end memory is exactly `m1`. A read-only run can own
  nothing (`S = ⊥`) and read its bytes through the data view `DA` (bytes of the text): then
  `hpres` is vacuous and the conclusion is the incumbent's `Triple (At …) (At …)`.
* `tripleZ_of_swp` drops `hpres` and concludes `TripleZ`: the run reaches a configuration
  zero-equivalent (`Vsa.Densify.CEqv`: same registers, same total reads) to an `At` state.
  `TripleZ.seq` composes it with any `Triple`, through `Vsa.Densify.steps_sim`.

The executor's read-only register is `gp = gpV` (`MallocFast.roR`, fixed in `SWP`), so the
kept registers must pin it (`hgp`).
-/

namespace Tom.Machine.Sym

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open VsaIris VsaIris.Sym VsaIris.SymExec VsaIris.Inst VsaIris.MallocFast
open Vsa.Machine (Config MState StepsN Steps)

/-! ## A function's code as the executor's image -/

/-- Byte `a` of the words `ws` placed at `base` (little-endian). -/
def img (base : Nat) (ws : List (BitVec 32)) (a : Nat) : BitVec 8 :=
  match ws[(a - base) / 4]? with
  | some w => w.extractLsb' (8 * ((a - base) % 4)) 8
  | none => 0

/-- The code range. -/
def rT (base : Nat) (ws : List (BitVec 32)) : List (Nat × Nat) := [(base, base + 4 * ws.length)]

/-- The code text. -/
def T (base : Nat) (ws : List (BitVec 32)) : List (Nat × BitVec 8) :=
  rangeText (img base ws) (rT base ws)

/-- Every GPR but `gp`, and the PC: the largest tracked set. -/
def allRegs : List Nat := 32 :: 1 :: 2 :: List.range' 4 28

/-- The registers an instruction word names (by format). -/
def wregs (w : BitVec 32) : List Nat :=
  let op := (w.extractLsb' 0 7).toNat
  let rd := (w.extractLsb' 7 5).toNat
  let r1 := (w.extractLsb' 15 5).toNat
  let r2 := (w.extractLsb' 20 5).toNat
  if op = 0x33 ∨ op = 0x3b then [rd, r1, r2]
  else if op = 0x13 ∨ op = 0x1b ∨ op = 0x03 ∨ op = 0x67 then [rd, r1]
  else if op = 0x23 ∨ op = 0x63 then [r1, r2] else [rd]

/-- The registers the code `ws` names, and the PC (`#eval` it once for a function's `rs`: the
tracked registers of its runs; registers off `rs` are framed by `SWP` itself). -/
def regsOf (ws : List (BitVec 32)) : List Nat :=
  32 :: (List.range' 1 31).filter fun r => r ≠ 3 && ws.any fun w => (wregs w).contains r

/-- The executor's configuration for the function at `base`, tracking the registers `rs`. -/
def cfg (base : Nat) (ws : List (BitVec 32)) (rs : List Nat) (stops : List (BitVec 64))
    (dpcs : List (BitVec 64) := []) : Cfg :=
  { img := img base ws, rT := rT base ws, rs := rs, stops := stops, dbase := [], dpcs := dpcs,
    hasB := bytesHasB [⟨img base ws, rT base ws⟩] }

theorem hasB_T {base : Nat} {ws : List (BitVec 32)} {rs : List Nat} {s d : List (BitVec 64)} :
    ∀ i code, (cfg base ws rs s d).hasB i code = true →
      ∀ q ∈ codeFoot i code, (q.1, q.2.2) ∈ T base ws := by
  intro i code h q hq
  obtain ⟨⟨b, j⟩, hbj, rfl⟩ := List.mem_map.1 hq
  have := mem_piecesText (piecesHasB_of_bytes h hbj)
  unfold piecesText at this
  simpa [T] using this

theorem codeAt (base : Nat) (ws : List (BitVec 32)) :
    SymExec.CodeAt (T base ws) (img base ws) (rT base ws) := by
  intro m hm a ha
  exact hm (a, img base ws a) (mem_rangeText_iff.2 ⟨inRangesB_iff.2 ha, rfl⟩)

theorem inRanges_rT {base : Nat} {ws : List (BitVec 32)} {a : Nat} :
    InRanges (rT base ws) a ↔ base ≤ a ∧ a < base + 4 * ws.length := by
  simp [InRanges, rT]

theorem live_T {base : Nat} {ws : List (BitVec 32)} :
    ∀ p ∈ T base ws, InRanges (rT base ws) p.1 := by
  intro p hp
  exact inRangesB_iff.1 (mem_rangeText_iff.1 hp).1


/-- **Our code predicate is the executor's text.** -/
theorem textLoaded {m : Mem} {base : Nat} {ws : List (BitVec 32)}
    (h : Tom.Machine.CodeAt m base ws) : TextLoaded (T base ws) m := by
  intro p hp
  obtain ⟨hr, he⟩ := mem_rangeText_iff.1 hp
  obtain ⟨r, hr, h1, h2⟩ := inRangesB_iff.1 hr
  simp only [rT, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  obtain ⟨a, b⟩ := p
  simp only at he h1 h2
  subst he
  have hj : (a - base) / 4 < ws.length := by omega
  obtain ⟨w, hw⟩ : ∃ w, ws[(a - base) / 4]? = some w := ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨b0, b1, b2, b3⟩ := h _ w hw
  simp only [img, hw]
  have ha : a = base + 4 * ((a - base) / 4) + (a - base) % 4 := by omega
  rcases (by omega : (a - base) % 4 = 0 ∨ (a - base) % 4 = 1 ∨ (a - base) % 4 = 2 ∨
      (a - base) % 4 = 3) with e | e | e | e <;> rw [e] at ha ⊢ <;> rw [ha]
  · exact b0
  · exact b1
  · exact b2
  · exact b3

/-! ## The post of a run that ends in an `At` state -/

/-- The live (present) bytes: the code, and the owned bytes known present. -/
def liveS (base : Nat) (ws : List (BitVec 32)) (Own : Nat → Prop) (a : Nat) : Prop :=
  InRanges (rT base ws) a ∨ Own a

/-- The end state of a run, as `SWP`'s post: the PC, the pins `L1`, the kept registers the run
tracks, and the owned bytes of the end memory `m1`. -/
def QAt (rs : List Nat) (pc1 : BitVec 64) (L1 keep : GRegs) (S : Nat → Prop) (m1 : Mem)
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop :=
  rv VsaIris.PC = pc1 ∧ (∀ p ∈ L1, rv p.1 = p.2) ∧ (∀ p ∈ keep, p.1 ∈ rs → rv p.1 = p.2) ∧
    ∀ a, S a → mv a = imgM m1 a

/-- **A leaf of a run**: the run is done when the symbolic end state is the `QAt` state. -/
theorem swp_leaf {live : Nat → Prop} {Tx : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
    {pc1 : BitVec 64} {L1 keep : GRegs} {m1 : Mem} {pc : BitVec 64} {R : Nat → BitVec 64}
    {M : Mem} (hpc : pc = pc1) (hL1 : ∀ p ∈ L1, p.1 ∈ rs ∧ p.1 ≠ VsaIris.PC ∧ R p.1 = p.2)
    (hK : ∀ p ∈ keep, p.1 ∈ rs → p.1 ≠ VsaIris.PC ∧ R p.1 = p.2)
    (hM : ∀ a, S a → imgM M a = imgM m1 a) :
    SWP live Tx rs S (QAt rs pc1 L1 keep S m1) pc R M :=
  swp_done fun _ _ hm => ⟨hm.pc.trans hpc,
    fun p hp => (hm.regs _ (hL1 p hp).1 (hL1 p hp).2.1).trans (hL1 p hp).2.2,
    fun p hp hr => (hm.regs _ hr (hK p hp hr).1).trans (hK p hp hr).2,
    fun a ha => (hm.img a ha).trans (hM a ha)⟩

/-! ## From `SWP` to a machine run -/

/-- The total read of a configuration's memory. -/
abbrev memD (c : Config) (a : Nat) : BitVec 8 := (c.σ.mem[a]?).getD 0

/-- The end of a run: what `LocalRun` gives about the configuration it reaches. -/
structure RunEnd (live : Nat → Prop) (rs : List Nat) (c : Config) (S : Nat → Prop)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (c' : Config) : Prop where
  steps : Steps c c'
  ok : VsaOk live c'
  quiet : c'.σ.sailOutput = c.σ.sailOutput
  post : Q (vsaReg c') (memD c')
  regs : ∀ r, r ∉ rs → vsaReg c' r = vsaReg c r
  mem : ∀ a, ¬ S a → memD c' a = memD c a
  pres : ∀ a, ¬ S a → ((c'.σ.mem[a]?).isSome ↔ (c.σ.mem[a]?).isSome)

theorem localRun_end {live : Nat → Prop} {Tx : List (Nat × BitVec 8)} {rs : List Nat}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (hgp : 3 ∉ rs)
    (hS : ∀ p ∈ Tx, ¬ S p.1) :
    ∀ n (c : Config), LocalRun (vsaModel live) roR Tx rs S Q n (vsaReg c) (memD c) →
      VsaOk live c → ROHolds (vsaModel live) c roR Tx → ∃ c', RunEnd live rs c S Q c'
  | 0, c, h, hok, _ => ⟨c, ⟨.refl c, hok, rfl, h, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => .rfl⟩⟩
  | n + 1, c, h, hok, hro => by
    rcases h with h | ⟨k, hseg⟩
    · exact ⟨c, ⟨.refl c, hok, rfl, h, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => .rfl⟩⟩
    obtain ⟨c1, hr, hok1, hregs, hmem, ⟨_, hq⟩, hP⟩ :=
      hseg c hok hro (fun _ _ => rfl) (fun _ _ => rfl)
    have hro1 : ROHolds (vsaModel live) c1 roR Tx := by
      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
      · simp only [roR, List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp
        exact (hregs gp hgp).trans (hro.1 _ List.mem_cons_self)
      · exact (hmem p.1 (hS p hp)).1.trans (hro.2 p hp)
    obtain ⟨c2, he⟩ := localRun_end hgp hS n c1 hP hok1 hro1
    exact ⟨c2, ⟨(stepsN_of_reachesN hr).toSteps.trans he.steps, he.ok, he.quiet.trans hq, he.post,
      fun r hr' => (he.regs r hr').trans (hregs r hr'),
      fun a ha => (he.mem a ha).trans (hmem a ha).1,
      fun a ha => (he.pres a ha).trans (hmem a ha).2⟩⟩

theorem gholds_of_forall {σ : MState} : ∀ {L : GRegs}, (∀ p ∈ L, gprGet σ p.1 = some p.2) →
    GHolds σ L
  | [], _ => trivial
  | (_, _) :: _, h => ⟨h _ List.mem_cons_self, gholds_of_forall fun p hp => h p (.tail _ hp)⟩

theorem vsaReg_of_gprGet {c : Config} {n : Nat} {v : BitVec 64} (h : gprGet c.σ n = some v) :
    vsaReg c n = v := by
  have hn : n ≠ VsaIris.PC := by
    intro e; subst e
    rw [gprGet_none (by unfold VsaIris.PC; omega)] at h; cases h
  rw [vsaReg_gpr hn, h]; rfl

/-- **An `SWP` from an `At` state is a machine run** (the shared half of both adequacy forms). -/
theorem run_of_swp {base : Nat} {ws : List (BitVec 32)} {rs DA : List Nat} {S Own : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {pc : BitVec 64} {L keep : GRegs} {m : Mem} {outp : Array String} {c : Config}
    (hcode : Tom.Machine.CodeAt m base ws) (hgp : (3, gpV) ∈ keep) (hgp3 : 3 ∉ rs)
    (hTS : ∀ a, InRanges (rT base ws) a → ¬ S a) (hDS : ∀ a ∈ DA, ¬ S a)
    (hOwn : ∀ a, Own a → (m[a]?).isSome)
    (h : SWP (liveS base ws Own) (T base ws ++ dataOf m DA) rs S Q pc (vsaReg c) m)
    (hc : Tom.Machine.At pc L m keep outp c) : ∃ c', RunEnd (liveS base ws Own) rs c S Q c' := by
  have htl := textLoaded hcode
  have hm := hc.mem
  have hok : VsaOk (liveS base ws Own) c := by
    refine ⟨hc.good, hc.tick, hc.gprs, fun a ha => ?_, hc.pw⟩
    rw [hm]
    rcases ha with ha | ha
    · rw [htl (a, img base ws a) (mem_rangeText_iff.2 ⟨inRangesB_iff.2 ha, rfl⟩)]; rfl
    · exact hOwn a ha
  have hro : ROHolds (vsaModel (liveS base ws Own)) c roR (T base ws ++ dataOf m DA) := by
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · simp only [roR, List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact vsaReg_of_gprGet (Tom.Machine.gholds_mem hc.keep hgp)
    · rcases List.mem_append.1 hp with hp | hp
      · show (c.σ.mem[p.1]?).getD 0 = p.2
        rw [hm, htl p hp]; rfl
      · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hp
        show (c.σ.mem[a]?).getD 0 = imgM m a
        rw [hm]; rfl
  have hS : ∀ p ∈ T base ws ++ dataOf m DA, ¬ S p.1 := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hTS _ (live_T p hp)
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
      exact hDS a ha
  obtain ⟨n, hn⟩ := h
  have hpc : vsaReg c VsaIris.PC = pc := by
    show (c.σ.regs.get? Register.PC).getD 0 = pc
    rw [hc.pcv]; rfl
  exact localRun_end hgp3 hS n c (hn _ _ ⟨hpc, fun _ _ _ => rfl, fun a _ => by
    show (c.σ.mem[a]?).getD 0 = imgM m a; rw [hm]; rfl⟩) hok hro

theorem opt_eq {o o' : Option (BitVec 8)} (h1 : o.isSome ↔ o'.isSome) (h2 : o.getD 0 = o'.getD 0) :
    o = o' := by
  cases o <;> cases o' <;> simp_all

/-- The registers of the run's end, for `At`. -/
theorem end_regs {live : Nat → Prop} {rs : List Nat} {c c' : Config} {S : Nat → Prop}
    {pc1 : BitVec 64} {L1 keep : GRegs} {m1 : Mem} (e : RunEnd live rs c S (QAt rs pc1 L1 keep S m1) c')
    (hkeep : GHolds c.σ keep) (hL1 : ∀ p ∈ L1, 1 ≤ p.1 ∧ p.1 ≤ 31)
    (hK1 : ∀ p ∈ keep, 1 ≤ p.1 ∧ p.1 ≤ 31) :
    c'.σ.regs.get? Register.PC = some pc1 ∧ GHolds c'.σ L1 ∧ GHolds c'.σ keep := by
  obtain ⟨hpc, hL, hK, -⟩ := e.post
  refine ⟨?_, gholds_of_forall fun p hp => gprGet_eq_of_vsaReg e.ok (hL1 p hp).1 (hL1 p hp).2
    (hL p hp), gholds_of_forall fun p hp => ?_⟩
  · obtain ⟨w, hw⟩ := e.ok.good.PC
    have h : (c'.σ.regs.get? Register.PC).getD 0 = pc1 := hpc
    rw [hw] at h ⊢; exact congrArg some h
  · refine gprGet_eq_of_vsaReg e.ok (hK1 p hp).1 (hK1 p hp).2 ?_
    by_cases hr : p.1 ∈ rs
    · exact hK p hp hr
    · exact (e.regs _ hr).trans (vsaReg_of_gprGet (Tom.Machine.gholds_mem hkeep hp))

/-- **Adequacy, exact form.** An `SWP` with post `QAt` from every register file that agrees with
`At pc L m keep`, with the owned bytes `S` present at entry, is the triple to
`At pc1 L1 m1 keep`. `m1` agrees with `m` off `S` and has the owned bytes present (for
`m1 = writeLog m lg`: `hframe` from the log's addresses, `hpres1` by `writeLog_present`). -/
theorem triple_of_swp {base : Nat} {ws : List (BitVec 32)} {rs DA : List Nat} {S : Nat → Prop}
    {pc pc1 : BitVec 64} {L L1 keep : GRegs} {m m1 : Mem} {outp : Array String}
    (hcode : Tom.Machine.CodeAt m base ws) (hgp : (3, gpV) ∈ keep) (hgp3 : 3 ∉ rs)
    (hTS : ∀ a, InRanges (rT base ws) a → ¬ S a) (hDS : ∀ a ∈ DA, ¬ S a)
    (hpres : ∀ a, S a → (m[a]?).isSome)
    (hframe : ∀ a, ¬ S a → m1[a]? = m[a]?) (hpres1 : ∀ a, S a → (m1[a]?).isSome)
    (hL1 : ∀ p ∈ L1, 1 ≤ p.1 ∧ p.1 ≤ 31) (hK1 : ∀ p ∈ keep, 1 ≤ p.1 ∧ p.1 ≤ 31)
    (h : ∀ R : Nat → BitVec 64, (∀ p ∈ L, R p.1 = p.2) → (∀ p ∈ keep, R p.1 = p.2) →
      SWP (liveS base ws S) (T base ws ++ dataOf m DA) rs S (QAt rs pc1 L1 keep S m1) pc R m) :
    Triple (Tom.Machine.At pc L m keep outp) (Tom.Machine.At pc1 L1 m1 keep outp) := by
  intro c hc
  obtain ⟨c', e⟩ := run_of_swp hcode hgp hgp3 hTS hDS hpres
    (h _ (fun p hp => vsaReg_of_gprGet (Tom.Machine.gholds_mem hc.regs hp))
      (fun p hp => vsaReg_of_gprGet (Tom.Machine.gholds_mem hc.keep hp))) hc
  obtain ⟨hpc, hL, hK⟩ := end_regs e hc.keep hL1 hK1
  have hmem : c'.σ.mem = m1 := by
    apply Std.ExtHashMap.ext_getElem?
    intro a
    by_cases ha : S a
    · exact opt_eq (by simp only [e.ok.live a (.inr ha), hpres1 a ha])
        (e.post.2.2.2 a ha)
    · rw [hframe a ha]
      have h1 := e.mem a ha
      have h2 := e.pres a ha
      unfold memD at h1
      rw [hc.mem] at h1 h2
      exact opt_eq h2 h1
  exact ⟨c', e.steps,
    { good := e.ok.good, tick := e.ok.tick, mem := hmem, pcv := hpc,
      minstret := e.ok.good.minstret, regs := hL, keep := hK, out := e.quiet.trans hc.out,
      pw := e.ok.htifIdle, th := e.ok.good.htif_tohost, gprs := e.ok.gpr }⟩

/-! ## The weaker form: up to zero-equivalence -/

theorem gprGet_regs {σ σ' : MState} (h : σ'.regs = σ.regs) (n : Nat) : gprGet σ' n = gprGet σ n := by
  unfold gprGet; rw [h]

theorem gholds_regs {σ σ' : MState} (h : σ'.regs = σ.regs) : ∀ {L : GRegs}, GHolds σ L → GHolds σ' L
  | [], _ => trivial
  | (_, _) :: _, hL => ⟨(gprGet_regs h _).trans hL.1, gholds_regs h hL.2⟩

/-- `c` with its memory replaced by `m`. -/
def withMem (c : Config) (m : Mem) : Config :=
  ⟨⟨c.σ.regs, c.σ.choiceState, m, c.σ.tags, c.σ.cycleCount, c.σ.sailOutput⟩, c.tick, c.steps⟩

/-- A run to a configuration zero-equivalent to a `Q` state (`Vsa.Densify.CEqv`). -/
def TripleZ (P Q : Config → Prop) : Prop :=
  ∀ c, P c → ∃ c' c₀, Steps c c' ∧ Vsa.Densify.CEqv c' c₀ ∧ Q c₀

theorem TripleZ.of_triple {P Q : Config → Prop} (h : Triple P Q) : TripleZ P Q := fun c hc => by
  obtain ⟨c', hs, hq⟩ := h c hc
  exact ⟨c', c', hs, .refl _, hq⟩

/-- `TripleZ` then `Triple`: the second run is replayed from the zero-equivalent configuration
(`steps_sim`; the model's step never inspects presence, `stepOnce_resp`). -/
theorem TripleZ.seq {P Q R : Config → Prop} (h1 : TripleZ P Q) (h2 : Triple Q R) :
    TripleZ P R := fun c hc => by
  obtain ⟨c', c₀, hs, he, hq⟩ := h1 c hc
  obtain ⟨c₂, hs₂, hr⟩ := h2 c₀ hq
  obtain ⟨c₂', hs₂', he₂⟩ := Vsa.Densify.steps_sim Vsa.Densify.stepOnce_resp he.symm hs₂
  exact ⟨c₂', c₂, hs.trans hs₂', he₂.symm, hr⟩

theorem TripleZ.seqZ {P Q R : Config → Prop} (h1 : TripleZ P Q) (h2 : TripleZ Q R) :
    TripleZ P R := fun c hc => by
  obtain ⟨c', c₀, hs, he, hq⟩ := h1 c hc
  obtain ⟨c₂, c₃, hs₂, he₂, hr⟩ := h2 c₀ hq
  obtain ⟨c₂', hs₂', he₂'⟩ := Vsa.Densify.steps_sim Vsa.Densify.stepOnce_resp he.symm hs₂
  exact ⟨c₂', c₃, hs.trans hs₂', ⟨he₂'.σ.symm.trans he₂.σ, he₂'.tick.symm.trans he₂.tick,
    he₂'.steps.symm.trans he₂.steps⟩, hr⟩

/-- **Adequacy, weaker form.** As `triple_of_swp` without the presence premises: the run ends
zero-equivalent to the `At` state. -/
theorem tripleZ_of_swp {base : Nat} {ws : List (BitVec 32)} {rs DA : List Nat} {S : Nat → Prop}
    {pc pc1 : BitVec 64} {L L1 keep : GRegs} {m m1 : Mem} {outp : Array String}
    (hcode : Tom.Machine.CodeAt m base ws) (hgp : (3, gpV) ∈ keep) (hgp3 : 3 ∉ rs)
    (hTS : ∀ a, InRanges (rT base ws) a → ¬ S a) (hDS : ∀ a ∈ DA, ¬ S a)
    (hframe : ∀ a, ¬ S a → (m1[a]?).getD 0 = (m[a]?).getD 0)
    (hL1 : ∀ p ∈ L1, 1 ≤ p.1 ∧ p.1 ≤ 31) (hK1 : ∀ p ∈ keep, 1 ≤ p.1 ∧ p.1 ≤ 31)
    (h : ∀ R : Nat → BitVec 64, (∀ p ∈ L, R p.1 = p.2) → (∀ p ∈ keep, R p.1 = p.2) →
      SWP (liveS base ws fun _ => False) (T base ws ++ dataOf m DA) rs S
        (QAt rs pc1 L1 keep S m1) pc R m) :
    TripleZ (Tom.Machine.At pc L m keep outp) (Tom.Machine.At pc1 L1 m1 keep outp) := by
  intro c hc
  obtain ⟨c', e⟩ := run_of_swp hcode hgp hgp3 hTS hDS (fun _ h => h.elim)
    (h _ (fun p hp => vsaReg_of_gprGet (Tom.Machine.gholds_mem hc.regs hp))
      (fun p hp => vsaReg_of_gprGet (Tom.Machine.gholds_mem hc.keep hp))) hc
  obtain ⟨hpc, hL, hK⟩ := end_regs e hc.keep hL1 hK1
  refine ⟨c', withMem c' m1, e.steps,
    ⟨⟨rfl, rfl, fun a => ?_, rfl, rfl⟩, rfl, rfl⟩,
    { good := { e.ok.good with }, tick := e.ok.tick, mem := rfl, pcv := hpc,
      minstret := e.ok.good.minstret, regs := gholds_regs (σ := c'.σ) (σ' := (withMem c' m1).σ) rfl hL, keep := gholds_regs (σ := c'.σ) (σ' := (withMem c' m1).σ) rfl hK,
      out := e.quiet.trans hc.out, pw := e.ok.htifIdle, th := e.ok.good.htif_tohost,
      gprs := fun n h1 h2 => (gprGet_regs rfl n).symm ▸ e.ok.gpr n h1 h2 }⟩
  simp only [Std.ExtHashMap.get?_eq_getElem?]
  show _ = (m1[a]?).getD 0
  by_cases ha : S a
  · exact e.post.2.2.2 a ha
  · rw [hframe a ha]
    have := e.mem a ha
    unfold memD at this
    rwa [hc.mem] at this

end Tom.Machine.Sym

namespace Tom.Machine.Sym

open LeanRV64DExecutable Vsa Vsa.Sim
open VsaIris VsaIris.Sym VsaIris.SymExec VsaIris.MallocFast

/-! ## Helpers for runs -/

/-- Every RAM byte (`[0x80000000, 2^32)`): the data view of a read-only run. -/
def ramA : List Nat := List.range' 0x80000000 0x80000000

theorem mem_ramA {a : Nat} : a ∈ ramA ↔ 0x80000000 ≤ a ∧ a < 0x100000000 := by
  simp only [ramA, List.mem_range'_1]

/-- The pcs of the loads of the code `ws` at `base` (opcode `0x03`): a read-only run reads
them all through the data view. -/
def loadPcs (base : Nat) (ws : List (BitVec 32)) : List (BitVec 64) :=
  (ws.zipIdx.filter fun p => p.1.extractLsb' 0 7 == 0x03#7).map fun p => BitVec.ofNat 64 (base + 4 * p.2)

/-- (Not a `rfl` lemma: `simp` would use it as a definitional unfolding, which blows up on the
upd chains of a run; `Eq.trans rfl rfl` keeps it a rewrite.) -/
theorem ldv_lw (m : Mem) (a : Nat) : ldv .lw m a = BitVec.signExtend 64 (bytesT4 m a) :=
  Eq.trans rfl rfl

theorem ldv_ld (m : Mem) (a : Nat) : ldv .ld m a = bytesT8 m a := by
  simp only [ldv, bytesVal, bytesAt, widthOfM, imgM, bytesT8, Functions.sign_extend,
    Sail.BitVec.signExtend, BitVec.signExtend_eq]
  rfl

/-- **One executor run** of the function at `base` from `pc`, with the entry memory `m` as both
the owned image and the data view: the residual of the pruned tree, the leaves continued by
`SWP` (`symRun_auto` for this configuration). -/
theorem sym_at {base : Nat} {ws : List (BitVec 32)} {rs : List Nat} {stops dpcs : List (BitVec 64)}
    {S Own : Nat → Prop} {DA : List Nat} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (Γ : Geom) (n : Nat) (pc : BitVec 64) (R : Nat → BitVec 64) (m : Mem)
    (hΓn : Γ.all (fun f => f.atom.noHv) = true)
    (hΓ : Γ.holds ⟨R, m, m, fun _ => 0⟩ S DA)
    (h : ((symRun (cfg base ws rs stops dpcs) n ⟨pc, [], [], []⟩).prune Γ).WP ⟨R, m, m, fun _ => 0⟩
      S DA (fun pc R M => SWP (liveS base ws Own) (T base ws ++ dataOf m DA) rs S Q pc R M))
    (hPC : 32 ∈ rs := by decide) (hgp : 3 ∉ rs := by decide) :
    SWP (liveS base ws Own) (T base ws ++ dataOf m DA) rs S Q pc R m :=
  symRun_auto (live := liveS base ws Own) (cfg base ws rs stops dpcs) (codeAt _ _) hasB_T
    (fun p hp => Or.inl (live_T p hp)) hPC hgp Γ n pc R m [] (by simp)
    (by simp [cfg]) (by simp [cfg]) (by simp [cfg]) (by simp [cfg]) hΓn hΓ h

/-! ## Runs with several exits (a whole branching stretch in one run) -/

/-- One exit of a run: the path's guard and the `At` state it ends in (memory `m`). -/
structure Exit where
  guard : Prop
  pc : BitVec 64
  L : GRegs
  m : Mem

/-- The post of a run with exits `xs`: some exit's guard holds and the run is in its state. -/
def QAny (rs : List Nat) (xs : List Exit) (keep : GRegs) (S : Nat → Prop)
    (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop :=
  ∃ x ∈ xs, x.guard ∧ QAt rs x.pc x.L keep S x.m rv mv

theorem swp_leaf_any {live : Nat → Prop} {Tx : List (Nat × BitVec 8)} {rs : List Nat}
    {S : Nat → Prop} {xs : List Exit} {keep : GRegs} {x : Exit} {pc : BitVec 64}
    {R : Nat → BitVec 64} {M : Mem} (hx : x ∈ xs) (hg : x.guard) (hpc : pc = x.pc)
    (hL1 : ∀ p ∈ x.L, p.1 ∈ rs ∧ p.1 ≠ VsaIris.PC ∧ R p.1 = p.2)
    (hK : ∀ p ∈ keep, p.1 ∈ rs → p.1 ≠ VsaIris.PC ∧ R p.1 = p.2)
    (hM : ∀ a, S a → imgM M a = imgM x.m a) :
    SWP live Tx rs S (QAny rs xs keep S) pc R M :=
  swp_done fun _ _ hm => ⟨x, hx, hg, hm.pc.trans hpc,
    fun p hp => (hm.regs _ (hL1 p hp).1 (hL1 p hp).2.1).trans (hL1 p hp).2.2,
    fun p hp hr => (hm.regs _ hr (hK p hp hr).1).trans (hK p hp hr).2,
    fun a ha => (hm.img a ha).trans (hM a ha)⟩

/-- **Adequacy with several exits, exact form**: the run ends in the `At` state of an exit whose
guard holds. -/
theorem triple_of_swp_any {base : Nat} {ws : List (BitVec 32)} {rs DA : List Nat}
    {S : Nat → Prop} {pc : BitVec 64} {L keep : GRegs} {m : Mem} {outp : Array String}
    {xs : List Exit}
    (hcode : Tom.Machine.CodeAt m base ws) (hgp : (3, gpV) ∈ keep) (hgp3 : 3 ∉ rs)
    (hTS : ∀ a, InRanges (rT base ws) a → ¬ S a) (hDS : ∀ a ∈ DA, ¬ S a)
    (hpres : ∀ a, S a → (m[a]?).isSome)
    (hframe : ∀ x ∈ xs, ∀ a, ¬ S a → x.m[a]? = m[a]?)
    (hpres1 : ∀ x ∈ xs, ∀ a, S a → (x.m[a]?).isSome)
    (hL1 : ∀ x ∈ xs, ∀ p ∈ x.L, 1 ≤ p.1 ∧ p.1 ≤ 31) (hK1 : ∀ p ∈ keep, 1 ≤ p.1 ∧ p.1 ≤ 31)
    (h : ∀ R : Nat → BitVec 64, (∀ p ∈ L, R p.1 = p.2) → (∀ p ∈ keep, R p.1 = p.2) →
      SWP (liveS base ws S) (T base ws ++ dataOf m DA) rs S (QAny rs xs keep S) pc R m) :
    Vsa.Logic.Triple (Tom.Machine.At pc L m keep outp)
      (fun c => ∃ x ∈ xs, x.guard ∧ Tom.Machine.At x.pc x.L x.m keep outp c) := by
  intro c hc
  obtain ⟨c', e⟩ := run_of_swp hcode hgp hgp3 hTS hDS hpres
    (h _ (fun p hp => vsaReg_of_gprGet (Tom.Machine.gholds_mem hc.regs hp))
      (fun p hp => vsaReg_of_gprGet (Tom.Machine.gholds_mem hc.keep hp))) hc
  obtain ⟨x, hx, hg, hq⟩ := e.post
  have e1 : RunEnd (liveS base ws S) rs c S (QAt rs x.pc x.L keep S x.m) c' := { e with post := hq }
  obtain ⟨hpc, hL, hK⟩ := end_regs e1 hc.keep (hL1 x hx) hK1
  have hmem : c'.σ.mem = x.m := by
    apply Std.ExtHashMap.ext_getElem?
    intro a
    by_cases ha : S a
    · exact opt_eq (by simp only [e.ok.live a (.inr ha), hpres1 x hx a ha]) (hq.2.2.2 a ha)
    · rw [hframe x hx a ha]
      have h1 := e.mem a ha
      have h2 := e.pres a ha
      unfold memD at h1
      rw [hc.mem] at h1 h2
      exact opt_eq h2 h1
  exact ⟨c', e.steps, x, hx, hg,
    { good := e.ok.good, tick := e.ok.tick, mem := hmem, pcv := hpc,
      minstret := e.ok.good.minstret, regs := hL, keep := hK, out := e.quiet.trans hc.out,
      pw := e.ok.htifIdle, th := e.ok.good.htif_tohost, gprs := e.ok.gpr }⟩

end Tom.Machine.Sym
