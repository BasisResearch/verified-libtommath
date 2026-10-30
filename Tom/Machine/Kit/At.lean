import Tom.Machine.Kit.Code
import Vsa.Sim.SegToTripleFramed

/-!
# Machine states at block boundaries, and the segment rule

`At pc L m keep outp c`: the machine is parked at `pc`; the registers
`L` hold their listed values; memory is `m`; the registers `keep`
(callee-saved, return address, stack pointer, …) hold theirs; the console
is `outp`; the HTIF mailbox is idle; and every general-purpose register is
mapped (`gprs`: ship-your-interpreter's allocator proofs run on a model whose
invariant asks for it, and every rule here keeps it). These are the fields of
`Vsa.Sim.FramedSegPost` with the computed outcome replaced by plain
parameters, so a function proof is a chain of `At` states.

`seg_at` is `Vsa.Sim.segRowFramed` between two `At` states. Its normal-form
side conditions (`hpc`, `hregs`, `hlog`) are what the segment computes,
and are closed by `simp` with `seg_simp`. `At.weaken` drops register pins.
-/

namespace Tom.Machine

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Vsa.Machine (Config MState)

/-- Every general-purpose register `x1`–`x31` is mapped. -/
def AllGprs (σ : MState) : Prop := ∀ n, 1 ≤ n → n ≤ 31 → (gprGet σ n).isSome

theorem noise_gprA : ∀ n, n < 32 → 1 ≤ n → ∀ rr ∈ noiseRegs, (rr == gprReg n) = false := by
  decide

/-- **`AllGprs` across a register frame**: the registers off `wrs` unchanged,
those in `wrs` (real GPRs) mapped after. -/
theorem allGprs_of_frame {σ σ' : MState} {wrs : List Nat} (hg : AllGprs σ)
    (hframe : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ m ∈ wrs, (gprReg m == R) = false) → σ'.regs.get? R = σ.regs.get? R)
    (hwr : ∀ m ∈ wrs, (1 ≤ m ∧ m ≤ 31) ∧ (gprGet σ' m).isSome) : AllGprs σ' := by
  intro n h1 h31
  by_cases hn : n ∈ wrs
  · exact (hwr n hn).2
  · rw [gprGet_of_frame n h1 h31 (noise_gprA n (by omega) h1)
      (fun m hm => gprReg_beq_false m (by have := (hwr m hm).1; omega) n (by omega) (hwr m hm).1.1 h1
        (fun e => hn (e ▸ hm))) hframe]
    exact hg n h1 h31

/-- A pinned register is mapped. -/
theorem gholds_isSome {σ : MState} {L : GRegs} (h : GHolds σ L) {n : Nat} (hn : n ∈ keysG L) :
    (gprGet σ n).isSome := by
  induction L with
  | nil => cases hn
  | cons p L ih =>
    obtain ⟨k, v⟩ := p
    rcases List.mem_cons.1 hn with rfl | hn
    · rw [h.1]; rfl
    · exact ih h.2 hn

/-- The machine parked at `pc` (see the module doc). -/
structure At (pc : BitVec 64) (L : GRegs) (m : Mem) (keep : GRegs) (outp : Array String)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  mem : c.σ.mem = m
  pcv : c.σ.regs.get? Register.PC = some pc
  minstret : ∃ w, c.σ.regs.get? Register.minstret = some w
  regs : GHolds c.σ L
  keep : GHolds c.σ keep
  out : c.σ.sailOutput = outp
  pw : c.σ.regs.get? Register.htif_payload_writes = some 0#4
  th : ∃ v, c.σ.regs.get? Register.htif_tohost = some v
  gprs : AllGprs c.σ

theorem gholds_mem {σ : MState} : ∀ {L : GRegs} {n : Nat} {v : BitVec 64},
    GHolds σ L → (n, v) ∈ L → gprGet σ n = some v
  | [], _, _, _, hm => nomatch hm
  | (_, _) :: _, _, _, h, hm => by
    rcases List.mem_cons.1 hm with he | hm
    · cases he; exact h.1
    · exact gholds_mem h.2 hm

theorem gholds_of_mem {σ : MState} : ∀ {L L' : GRegs}, GHolds σ L → (∀ p ∈ L', p ∈ L) → GHolds σ L'
  | _, [], _, _ => trivial
  | _, (_, _) :: _, h, hsub =>
    ⟨gholds_mem h (hsub _ (List.mem_cons_self ..)),
     gholds_of_mem h (fun q hq => hsub q (List.mem_cons_of_mem _ hq))⟩

/-- Drop register pins. -/
theorem At.weaken {pc : BitVec 64} {L L' : GRegs} {m : Mem} {keep : GRegs} {outp : Array String}
    {c : Config} (h : At pc L m keep outp c) (hsub : ∀ p ∈ L', p ∈ L) : At pc L' m keep outp c :=
  { h with regs := gholds_of_mem h.regs hsub }

/-! ## The registers a chain writes are pinned after it -/

theorem keysG_eraseG {L : GRegs} {n k : Nat} (h : n ∈ keysG L) (hne : n ≠ k) :
    n ∈ keysG (eraseG k L) := by
  induction L with
  | nil => cases h
  | cons p L ih =>
    obtain ⟨j, v⟩ := p
    simp only [keysG, List.mem_cons] at h
    simp only [eraseG]
    split
    · next hj => rcases h with rfl | h
                 · exact absurd hj hne
                 · exact ih h
    · rcases h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

/-- The stores (they write no register). -/
def isStoreK : MKind → Bool
  | .sw | .sd | .sb | .sh => true
  | _ => false

theorem stepGM_eq (a : MInstr) (L : GRegs) (bs : List (BitVec 8)) :
    stepGM a L bs = if isStoreK a.kind then L else (a.rd, wvalM a L bs) :: eraseG a.rd L := by
  unfold stepGM
  generalize a.kind = k
  cases k <;> rfl

theorem wrRegsM_cons (a : MInstr) (r : List MInstr) :
    wrRegsM (a :: r) = (if isStoreK a.kind then [] else [a.rd]) ++ wrRegsM r := by
  simp only [wrRegsM]
  generalize a.kind = k
  cases k <;> simp [isStoreK]

theorem keys_stepGM (a : MInstr) {L : GRegs} (bs : List (BitVec 8)) {n : Nat}
    (h : n ∈ keysG L ∨ (isStoreK a.kind = false ∧ n = a.rd)) : n ∈ keysG (stepGM a L bs) := by
  rw [stepGM_eq]
  split
  · next hs => rcases h with h | ⟨h, _⟩
               · exact h
               · rw [hs] at h; cases h
  · rcases h with h | ⟨_, rfl⟩
    · by_cases he : n = a.rd
      · subst he; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (keysG_eraseG h he)
    · exact List.mem_cons_self ..

theorem keys_runGM : ∀ (is : List MInstr) (L : GRegs) (lds : List (List (BitVec 8))) {n : Nat},
    n ∈ keysG L ∨ n ∈ wrRegsM is → n ∈ keysG (runGM is L lds)
  | [], _, _, _, h => by simpa [wrRegsM, runGM] using h
  | a :: r, L, lds, n, h => by
    simp only [runGM]
    apply keys_runGM r
    rw [wrRegsM_cons, List.mem_append] at h
    rcases h with h | h | h
    · exact .inl (keys_stepGM a _ (.inl h))
    · split at h
      · cases h
      · next hs => exact .inl (keys_stepGM a _ (.inr ⟨by simpa using hs, List.mem_singleton.1 h⟩))
    · exact .inr h

theorem keys_evalBlocks : ∀ (bs : List BBlock) (s : SegEvalState) {n : Nat},
    n ∈ keysG s.regs ∨ n ∈ wrChain bs → n ∈ keysG (evalBlocks bs s).regs
  | [], _, _, h => by simpa [wrChain] using h
  | b :: bs, s, n, h => by
    simp only [evalBlocks]
    apply keys_evalBlocks bs
    simp only [wrChain, List.mem_append] at h
    rcases h with h | h | h
    · exact .inl (keys_runGM b.body s.regs s.loads (.inl h))
    · exact .inl (keys_runGM b.body s.regs s.loads (.inr h))
    · exact .inr h

/-- The registers a chain writes are real GPRs (closed: `decide`). -/
def WrOK (bs : List BBlock) : Bool := (wrChain bs).all fun n => 1 ≤ n && n ≤ 31

/-- **The segment rule.** A `#derive_case` chain `bs` run from `At pc0 L m`
reaches `At pc1 L1 (writeLog m lg)`, where `pc1`, `L1` and `lg` are what the
chain computes (`hpc`, `hregs`, `hlog`). `ks`/`kk` are the literal key
lists of `L` and `keep` (`rfl`), so `hwf`, `hfr` and `hkeys` are kernel
`decide`s on literals; `hfacts` is `tom_facts` plus the data-dependent
leaves. -/
theorem seg_at (bs : List BBlock) {pc0 pc1 : BitVec 64} {L L1 : GRegs}
    (lds : List (List (BitVec 8))) {m : Mem} {lg : List WEntry} {keep : GRegs}
    {outp : Array String} (ks kk : List Nat)
    (hfacts : ChainFacts m m L lds bs)
    (hpc : evalBlocksPC pc0 (SegEvalState.init L lds) bs = pc1)
    (hregs : (evalBlocks bs (SegEvalState.init L lds)).regs = L1)
    (hlog : (evalBlocks bs (SegEvalState.init L lds)).log = lg)
    (hks : keysG L = ks := by rfl) (hkk : keysG keep = kk := by rfl)
    (hwf : ChainOK pc0 ks bs := by decide) (hfr : FrameOK kk bs := by decide)
    (hkeys : KeysOK ks := by decide) (hwr : WrOK bs = true := by decide) :
    Triple (At pc0 L m keep outp) (At pc1 L1 (writeLog m lg) keep outp) := by
  subst hks hkk
  intro c h
  obtain ⟨vm, hmi⟩ := h.minstret
  obtain ⟨σ', i', hs, hi', hG', hmem', hout, hpc', hmi', hregs', hframe⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm L lds h.good h.pcv hmi h.regs hkeys
      (h.mem ▸ hfacts) hwf h.tick
  have hw := List.all_eq_true.1 hwr
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel bs⟩, hs, ?_⟩
  exact { good := hG', tick := hi', mem := by rw [hmem', h.mem, hlog], pcv := hpc ▸ hpc',
          minstret := hmi', regs := hregs ▸ hregs'
          keep := gholds_keep_of_frame keep hfr.1 hframe h.keep
          out := hout.trans h.out
          pw := (hframe Register.htif_payload_writes (by decide)
            (fun m hm => (hfr.2 m hm).1)).trans h.pw
          th := by
            obtain ⟨v, hv⟩ := h.th
            exact ⟨v, (hframe Register.htif_tohost (by decide) (fun m hm => (hfr.2 m hm).2)).trans hv⟩
          gprs := allGprs_of_frame h.gprs hframe fun n hn =>
            ⟨by have := hw n hn; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this,
              gholds_isSome hregs' (keys_evalBlocks bs _ (.inr hn))⟩ }

end Tom.Machine

namespace Tom.Machine

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Vsa.Machine (Config MState)

/-- Every pin of `L1` is what `lookupG` finds in `L` (a conjunction once `L1`
is a literal list). -/
def SubL : GRegs → GRegs → Prop
  | [], _ => True
  | (n, v) :: L1, L => lookupG n L = some v ∧ SubL L1 L

theorem gholds_of_subL {σ : MState} {L : GRegs} (hL : GHolds σ L) :
    ∀ {L1 : GRegs}, SubL L1 L → GHolds σ L1
  | [], _ => trivial
  | (_, _) :: _, h => ⟨gholds_lookup L hL h.1, gholds_of_subL hL h.2⟩

/-- `seg_at` with the post's registers any `L1` that `SubL L1` the computed
list (`hsub`), so the caller states the registers it needs in its own order. -/
theorem seg_at' (bs : List BBlock) {pc0 pc1 : BitVec 64} {L L1 : GRegs}
    (lds : List (List (BitVec 8))) {m : Mem} {lg : List WEntry} {keep : GRegs}
    {outp : Array String} (ks kk : List Nat)
    (hfacts : ChainFacts m m L lds bs)
    (hpc : evalBlocksPC pc0 (SegEvalState.init L lds) bs = pc1)
    (hsub : SubL L1 (evalBlocks bs (SegEvalState.init L lds)).regs)
    (hlog : (evalBlocks bs (SegEvalState.init L lds)).log = lg)
    (hks : keysG L = ks := by rfl) (hkk : keysG keep = kk := by rfl)
    (hwf : ChainOK pc0 ks bs := by decide) (hfr : FrameOK kk bs := by decide)
    (hkeys : KeysOK ks := by decide) (hwr : WrOK bs = true := by decide) :
    Triple (At pc0 L m keep outp) (At pc1 L1 (writeLog m lg) keep outp) :=
  Triple.conseq (seg_at bs (L1 := (evalBlocks bs (SegEvalState.init L lds)).regs) lds ks kk hfacts hpc
      rfl hlog hks hkk hwf hfr hkeys hwr)
    (fun _ h => h) (fun _ h => { h with regs := gholds_of_subL h.regs hsub })

/-- Compute a chain's end PC, registers and write log into normal form
(`seg_nf [chain]`; used on `seg_at`'s `hpc`/`hregs`/`hlog`). -/
syntax "seg_nf" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| seg_nf [$ls,*]) => `(tactic| simp [$ls,*, Vsa.Sim.evalBlocksPC, Vsa.Sim.evalBlocks,
      Vsa.Sim.evalBlock, Vsa.Sim.SegEvalState.init, Vsa.Sim.runGM, Vsa.Sim.mkLine, Vsa.Sim.decodeM,
      Vsa.Sim.stepGM, Vsa.Sim.stepLdsM, Vsa.Sim.wvalM, Vsa.Sim.eraseG, Vsa.Sim.lookupG,
      Vsa.Sim.srcVal, Vsa.Sim.wentryM, Vsa.Sim.eaddrM, Vsa.Sim.bytesVal, Vsa.Sim.chainEndPC,
      Vsa.Sim.endPCB, Vsa.Sim.nextPC0, Vsa.Sim.tgtPCT, Vsa.Sim.tgtPC0, Vsa.Sim.wlogM, Vsa.Sim.ldsRunM, Vsa.Sim.widthOfM, Vsa.Sim.shamtOf,
      Sail.BitVec.addInt, LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
      Tom.Machine.bv_append_eq])

end Tom.Machine

namespace Tom.Machine

/-- Normalise a data-dependent leaf `tom_facts` leaves (a load's or store's
`MemFacts`, a branch guard) into address arithmetic and byte facts
(`leaf_nf [register-list defs]`). Two phases: full `simp` only to decode the
instruction literals, then `simp only` over the register lookups and the
address. Never on a code-frame leaf: use `code_frame`. -/
syntax "leaf_nf" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| leaf_nf [$ls,*]) => `(tactic|
      (simp only [Vsa.Sim.MemFacts, Vsa.Sim.TermFactsT, Vsa.Sim.TermFactsO]
       try simp only [$ls,*]
       try simp only [Vsa.Sim.mkLine, Vsa.Sim.decodeM, ↓reduceIte, BitVec.reduceExtractLsb',
         BitVec.reduceToNat, Nat.reduceEqDiff, Option.some.injEq, reduceCtorEq] 
       simp only [Vsa.Sim.guardB, Vsa.Sim.eaddrM, Vsa.Sim.srcVal, Vsa.Sim.lookupG,
         Vsa.Sim.runGM, Vsa.Sim.stepGM, Vsa.Sim.stepLdsM, Vsa.Sim.wvalM, Vsa.Sim.eraseG,
         Vsa.Sim.bytesVal, Vsa.Sim.ldsRunM, ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff,
         Option.getD_some, List.headD, List.tail_cons, Tom.Machine.writeLog_nil, List.append_nil, Sail.BitVec.addInt, LeanRV64DExecutable.Functions.sign_extend,
         Sail.BitVec.signExtend, Sail.BitVec.extractLsb, Tom.Machine.bv_append_eq, BitVec.reduceAppend,
         BitVec.reduceSignExtend, BitVec.signExtend_eq, Tom.Machine.toNat_ofNat_add,
         Tom.Machine.toNat_ofNat']))

/-- Close a code-frame leaf `∀ a, base ≤ a → a < base + 4 * n → (writeLog … )[a]? = m[a]?`
(`code_frame [register-list defs]`): `writeLog_out`, then each store's address
by `leaf_nf`'s lookups and `omega` (the context must give the stores' distance
from the code). -/
syntax "code_frame" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| code_frame [$ls,*]) => `(tactic|
      (intro a h1 h2
       try simp only [Vsa.Sim.stepMemM, Vsa.Sim.mkLine, Vsa.Sim.decodeM, ↓reduceIte,
         BitVec.reduceExtractLsb', BitVec.reduceToNat, Nat.reduceEqDiff, reduceCtorEq,
         ← Tom.Machine.writeLog_single]
       repeat rw [Vsa.Sim.writeLog_out]
       all_goals try simp only [$ls,*]
       all_goals
         try simp only [Vsa.Sim.wlogM, Vsa.Sim.mkLine, Vsa.Sim.decodeM, ↓reduceIte,
           BitVec.reduceExtractLsb', BitVec.reduceToNat, Nat.reduceEqDiff, reduceCtorEq]
         simp only [Vsa.Sim.OutL, Vsa.Sim.wlogM, Vsa.Sim.wentryM, Vsa.Sim.widthOfM,
           Vsa.Sim.eaddrM, Vsa.Sim.srcVal, Vsa.Sim.lookupG, Vsa.Sim.runGM, Vsa.Sim.stepGM,
           Vsa.Sim.stepLdsM, Vsa.Sim.wvalM, Vsa.Sim.eraseG, Vsa.Sim.bytesVal, ↓reduceIte,
           Nat.reduceAdd, Nat.reduceEqDiff, Option.getD_some, List.headD, and_true,
           LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
           Tom.Machine.bv_append_eq, BitVec.reduceAppend, BitVec.reduceSignExtend,
           Tom.Machine.ofNat_add_ofNat, Tom.Machine.toNat_ofNat_add, Tom.Machine.toNat_ofNat']
         try omega
       all_goals try exact rfl))

/-- `seg_nf` without full `simp`, for long bodies where full `simp` with the
default BitVec/`toNat` set runs away: three
`simp only` phases (structure, instruction decode, register and log
evaluation). -/
syntax "seg_nfo" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| seg_nfo [$ls,*]) => `(tactic|
      (try simp only [$ls,*]
       simp only [Vsa.Sim.evalBlocksPC, Vsa.Sim.evalBlocks, Vsa.Sim.evalBlock,
         Vsa.Sim.SegEvalState.init, Vsa.Sim.chainEndPC, Vsa.Sim.endPCB, Vsa.Sim.nextPC0,
         Vsa.Sim.tgtPCT, Vsa.Sim.tgtPC0, List.nil_append, List.cons_append]
       try simp only [Vsa.Sim.mkLine, Vsa.Sim.decodeM, ↓reduceIte, BitVec.reduceExtractLsb',
         BitVec.reduceToNat, Nat.reduceEqDiff, Option.some.injEq, reduceCtorEq]
       simp only [Vsa.Sim.runGM, Vsa.Sim.stepGM, Vsa.Sim.stepLdsM, Vsa.Sim.ldsRunM, Vsa.Sim.wvalM,
         Vsa.Sim.eraseG, Vsa.Sim.lookupG, Vsa.Sim.srcVal, Vsa.Sim.wentryM, Vsa.Sim.eaddrM,
         Vsa.Sim.bytesVal, Vsa.Sim.wlogM, Vsa.Sim.widthOfM, Vsa.Sim.shamtOf, Vsa.Sim.endPCM,
         Vsa.Sim.imm20Of, ↓reduceIte,
         Nat.reduceAdd, Nat.reduceEqDiff, Option.getD_some, List.headD, List.tail_cons, List.head?_cons,
         List.nil_append, List.cons_append, List.cons.injEq, Prod.mk.injEq, and_true, true_and,
         Sail.BitVec.addInt, Sail.BitVec.extractLsb, LeanRV64DExecutable.Functions.sign_extend,
         Sail.BitVec.signExtend, Tom.Machine.bv_append_eq, BitVec.reduceAppend,
         BitVec.reduceSignExtend, BitVec.reduceExtractLsb, BitVec.reduceExtractLsb', BitVec.signExtend_eq,
         BitVec.zero_add, BitVec.reduceAdd, BitVec.reduceOfInt, BitVec.add_zero,
         Tom.Machine.toNat_ofNat_add, Tom.Machine.toNat_ofNat']))

end Tom.Machine

namespace Tom.Machine

/-- The registers every function keeps (RISC-V psABI): `sp`, `gp`, `tp`,
`s0` and `s1..s11` (`Vsa.Sim.SRegs`). -/
structure Abi where
  sp : BitVec 64
  gp : BitVec 64
  tp : BitVec 64
  s0 : BitVec 64
  s : Vsa.Sim.SRegs

/-- Their pins, keys `[2, 3, 4, 8, 9, 18, …, 27]`. -/
def Abi.keep (v : Abi) : Vsa.Sim.GRegs :=
  [(2, v.sp), (3, v.gp), (4, v.tp), (8, v.s0)] ++ Vsa.Sim.sKeepL v.s

/-- The literal key list of `Abi.keep` (for `seg_at`'s `kk`). -/
abbrev abiKeys : List Nat := [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- `Abi.keep` without `sp` and `s0`, for a function that writes them (a stack
frame, `s0` as a local) and restores them by its epilogue: they travel in the
segment's own register list instead. -/
def Abi.keepR (v : Abi) : Vsa.Sim.GRegs := [(3, v.gp), (4, v.tp)] ++ Vsa.Sim.sKeepL v.s

abbrev abiKeysR : List Nat := [3, 4, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- `Abi.keepR` without `s1`, for a function that also uses `s1` as a local. -/
def Abi.keepR1 (v : Abi) : Vsa.Sim.GRegs :=
  [(3, v.gp), (4, v.tp), (18, v.s.s2), (19, v.s.s3), (20, v.s.s4), (21, v.s.s5), (22, v.s.s6),
   (23, v.s.s7), (24, v.s.s8), (25, v.s.s9), (26, v.s.s10), (27, v.s.s11)]

abbrev abiKeysR1 : List Nat := [3, 4, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

end Tom.Machine
