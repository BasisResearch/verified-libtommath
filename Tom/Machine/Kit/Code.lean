import Vsa.Sim.DeriveCase
import Vsa.Sim.DecodeNF
import Vsa.Sim.WriteLogNF

/-!
# Code in memory, and the mechanical half of a segment's facts

`CodeAt m base ws`: the instruction words `ws` sit little-endian at `base`
in `m`. One predicate serves every function: a function's contract carries
`CodeAt m base <fn>Code` (the words generated from the image,
`Tom/Machine/Code.lean`), and the code-byte pins a segment needs
(`BytePinsM`/`BytePinsT`) follow by one kernel `decide` on the word list
(`WordIn`), with no per-instruction lemma. `CodeAt.writeLog` keeps it across
stores outside the code.

`tom_facts h₁, …` is `Vsa.Sim.block_facts` with these closers: byte pins from
the `hᵢ : CodeAt m base ws` and `decide`, decode facts from `Vsa.Sim.decodeW`
(rule R15, no per-word decode table). Data-dependent leaves (`MemFacts` of
loads and stores, branch guards) are left as goals in program order.
-/

namespace Tom.Machine

open LeanRV64DExecutable Vsa Vsa.Sim

/-- Memory, as the machine layer has it. -/
abbrev Mem := Std.ExtHashMap Nat (BitVec 8)

/-- The words `ws` at `base`, little-endian. -/
def CodeAt (m : Mem) (base : Nat) (ws : List (BitVec 32)) : Prop :=
  ∀ j w, ws[j]? = some w →
    m[base + 4 * j]? = some (w.extractLsb' 0 8) ∧ m[base + 4 * j + 1]? = some (w.extractLsb' 8 8) ∧
    m[base + 4 * j + 2]? = some (w.extractLsb' 16 8) ∧ m[base + 4 * j + 3]? = some (w.extractLsb' 24 8)

/-- `w` is the word of `ws` at address `a` (decidable on literals). -/
def WordIn (base : Nat) (ws : List (BitVec 32)) (a : Nat) (w : BitVec 32) : Bool :=
  decide (base ≤ a) && (a - base) % 4 == 0 && ws[(a - base) / 4]? == some w

theorem CodeAt.word {m : Mem} {base : Nat} {ws : List (BitVec 32)} (h : CodeAt m base ws)
    {a : Nat} {w : BitVec 32} (hw : WordIn base ws a w = true) :
    m[a]? = some (w.extractLsb' 0 8) ∧ m[a + 1]? = some (w.extractLsb' 8 8) ∧
    m[a + 2]? = some (w.extractLsb' 16 8) ∧ m[a + 3]? = some (w.extractLsb' 24 8) := by
  simp only [WordIn, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  obtain ⟨⟨hle, hmod⟩, hj⟩ := hw
  have ha : a = base + 4 * ((a - base) / 4) := by omega
  rw [ha]; exact h _ w hj

theorem mkLine_fields (pc : BitVec 64) (w : BitVec 32) :
    (mkLine pc w).pc = pc ∧ (mkLine pc w).b0 = w.extractLsb' 0 8 ∧
    (mkLine pc w).b1 = w.extractLsb' 8 8 ∧ (mkLine pc w).b2 = w.extractLsb' 16 8 ∧
    (mkLine pc w).b3 = w.extractLsb' 24 8 := by
  unfold mkLine; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem bytePinsM_of {m : Mem} {base : Nat} {ws : List (BitVec 32)} (h : CodeAt m base ws)
    {pc : BitVec 64} {w : BitVec 32} (hw : WordIn base ws pc.toNat w = true) :
    BytePinsM m (mkLine pc w) := by
  obtain ⟨hp, h0, h1, h2, h3⟩ := mkLine_fields pc w
  unfold BytePinsM; rw [hp, h0, h1, h2, h3]; exact h.word hw

/-- A terminator's bytes are its word's (checked by `decide` on the literal). -/
def TBytesOK (t : TInstr) : Bool :=
  t.b0 == t.word.extractLsb' 0 8 && t.b1 == t.word.extractLsb' 8 8 &&
    t.b2 == t.word.extractLsb' 16 8 && t.b3 == t.word.extractLsb' 24 8

theorem bytePinsT_of {m : Mem} {base : Nat} {ws : List (BitVec 32)} (h : CodeAt m base ws)
    {t : TInstr} (hw : WordIn base ws t.pc.toNat t.word = true ∧ TBytesOK t = true) :
    BytePinsT m t := by
  obtain ⟨hw, hb⟩ := hw
  simp only [TBytesOK, Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hb
  unfold BytePinsT; rw [h0, h1, h2, h3]; exact h.word hw

/-- Stores off the code keep it. -/
theorem CodeAt.writeLog {m : Mem} {base : Nat} {ws : List (BitVec 32)} (h : CodeAt m base ws)
    {log : List WEntry} (hout : ∀ a, base ≤ a → a < base + 4 * ws.length → OutL log a) :
    CodeAt (Vsa.Sim.writeLog m log) base ws := by
  intro j w hj
  have hl : j < ws.length := by
    rcases Nat.lt_or_ge j ws.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hj; cases hj
  obtain ⟨h0, h1, h2, h3⟩ := h j w hj
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [writeLog_out] <;> first | assumption | (apply hout <;> omega)

/-- Memory that agrees with `m` on the code keeps it. -/
theorem CodeAt.of_eq {m m' : Mem} {base : Nat} {ws : List (BitVec 32)} (h : CodeAt m base ws)
    (heq : ∀ a, base ≤ a → a < base + 4 * ws.length → m'[a]? = m[a]?) : CodeAt m' base ws := by
  intro j w hj
  have hl : j < ws.length := by
    rcases Nat.lt_or_ge j ws.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hj; cases hj
  obtain ⟨h0, h1, h2, h3⟩ := h j w hj
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [heq] <;> first | assumption | omega

/-! ## Ground arithmetic for the leaf normal form (`leaf_nf`, `seg_nf`) -/

/-- The value of an address `x + c` (`c` the immediate's literal). -/
theorem toNat_ofNat_add (x c : Nat) :
    (BitVec.ofNat 64 x + BitVec.ofNat 64 c).toNat = (x + c) % 18446744073709551616 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, ← Nat.add_mod]

theorem toNat_ofNat' (x : Nat) : (BitVec.ofNat 64 x).toNat = x % 18446744073709551616 := by
  rw [BitVec.toNat_ofNat]


/-- Literal appends (S-type store immediates) for `BitVec.reduceAppend`. -/
theorem bv_append_eq {m n : Nat} (a : BitVec m) (b : BitVec n) : a.append b = a ++ b := rfl

/-- An `addi` on an `ofNat` value. -/
theorem ofNat_add_ofNat (x y : Nat) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.add_mod]

/-- `ofNat` equality is equality mod `2^64`. -/
theorem ofNat_eq_ofNat {x y : Nat} (h : x % 2 ^ 64 = y % 2 ^ 64) :
    BitVec.ofNat 64 x = BitVec.ofNat 64 y := by
  apply BitVec.eq_of_toNat_eq; simpa using h

theorem writeLog_nil (m : Mem) : writeLog m [] = m := rfl

/-- One write-log entry is one `applyW` (to fold `stepMemM` into `writeLog`). -/
theorem writeLog_single (m : Mem) (e : WEntry) : writeLog m [e] = applyW m e := rfl

/-! ## `tom_facts` -/

open Lean Elab Tactic Meta in
private partial def tfSolve (hs : Array Term) (g : MVarId) : TacticM (List MVarId) := do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  let run (tac : TSyntax `tactic) : TacticM Unit := do
    let gs ← Tactic.run g (evalTactic tac)
    unless gs.isEmpty do throwError "tom_facts: leaf not closed"
  -- a pin on memory none of the `hs` is about: from the first, leaving the
  -- code-frame goal `∀ a ∈ code, m'[a]? = m[a]?` to the caller
  let pins (lem : Ident) : TacticM (List MVarId) := do
    let alts ← hs.mapM fun h => `(tacticSeq| exact $lem $h (by decide +kernel))
    let h0 := hs[0]!
    let fb ← `(tacticSeq| refine $lem (CodeAt.of_eq $h0 ?_) (by decide +kernel))
    Tactic.run g (evalTactic (← `(tactic| first $[| $alts]* | $fb:tacticSeq)))
  match ty.getAppFn.constName? with
  | some ``And =>
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``And.intro)
      let mut acc : List MVarId := []
      for g' in gs do acc := acc ++ (← tfSolve hs g')
      return acc
  | some ``BytePinsM => pins (mkIdent ``bytePinsM_of)
  | some ``BytePinsT => pins (mkIdent ``bytePinsT_of)
  | some ``DecodeFactM | some ``DecodeFactT =>
      run (← `(tactic| exact fun s h1 h2 h3 => decodeW s h1 h2 h3)); return []
  | some ``True => g.assign (mkConst ``True.intro); return []
  | some ``ChainFacts | some ``BBlockFacts | some ``ProgFactsM
  | some ``TermPins | some ``TermFactsO =>
      let g' ← g.change (← g.withContext (whnf ty))
      tfSolve hs g'
  | _ =>
      if ← g.withContext (isDefEq ty (mkConst ``True)) then
        g.assign (mkConst ``True.intro); return []
      else
        return [g]

open Lean Elab Tactic in
/-- Close the code-pin and decode leaves of a `ChainFacts` goal from the
`CodeAt` hypotheses `h₁, …` (tried in order; a pin on memory written inside
the segment falls back to `CodeAt.of_eq h₁ ?_`, leaving the code-frame goal);
leave the data-dependent leaves in program order. -/
elab "tom_facts " hs:term,+ : tactic => do
  let leftovers ← tfSolve hs.getElems (← getMainGoal)
  setGoals leftovers

end Tom.Machine
