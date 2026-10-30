import VsaIris.Vsa.SymExec

/-!
# The `Geom` of a run, and the run splitter

Lines 83–229 of ship-your-interpreter's `VsaIris/Interp/SymInterp.lean` at `fb07094c`, verbatim between the markers below: `geomOf` (the `Geom` a run needs, read
off its own obligations), the branch-premise lemmas `gF_*`, `sym_den`, `sym_hnorm`, `rawR_eq`,
`geom_nil`/`geom_cons`. That module is the WHILE interpreter's `IW` driver (`sym_run`) and
imports `VsaIris.Interp.ITac`; it is not copied.
-/

namespace VsaIris.SymExec.Interp

open VsaIris VsaIris.Sym VsaIris.SymExec Vsa.Sim Vsa.MemRepr VsaIris.MallocFast
open LeanRV64DExecutable (bop)

/-! ## The `Geom` of a run, from its obligations -/

def Tree.obs : Tree → List SOb
  | .leaf s => s.obs
  | .br _ _ _ _ o t f => o ++ Tree.obs t ++ Tree.obs f
  | .jr s _ => s.obs
  | .hv _ t => Tree.obs t
  | .raw _ _ _ _ t => Tree.obs t

/-- The undecided forwarding checks of one node's loads, with the load's pc (`obs` is newest
first). Checks over a havoc slot are left to the walk, where the slot has its value. -/
def rawCandsOf (obs : List SOb) : List (BitVec 64 × SOb) :=
  (obs.reverse.foldl (fun (acc : Option (BitVec 64) × List (BitVec 64 × SOb)) o =>
    match o, acc.1 with
    | .decM pc _, _ => (some pc, acc.2)
    | .disj a _ b _, some pc => if a.noHv && b.noHv then (acc.1, acc.2 ++ [(pc, o)]) else acc
    | _, _ => acc) (none, [])).2

def Tree.rawCands : Tree → List (BitVec 64 × SOb)
  | .leaf s => rawCandsOf s.obs
  | .br _ _ _ _ o t f => rawCandsOf o ++ Tree.rawCands t ++ Tree.rawCands f
  | .jr s _ => rawCandsOf s.obs
  | .hv _ t => Tree.rawCands t
  | .raw _ _ _ _ t => Tree.rawCands t

/-- The state a segment's straight line ends in, when it ends at a leaf (not at a fork or an
indirect jump). -/
def Tree.endLeaf? : Tree → Option SS
  | .leaf s => some s
  | .br _ op a b _ t f => match a, b with
    | .c u, .c v => if guardB op u v then Tree.endLeaf? t else Tree.endLeaf? f
    | _, _ => none
  | .jr _ _ => none
  | .hv _ t => Tree.endLeaf? t
  | .raw _ _ _ _ t => Tree.endLeaf? t

/-- Whether an obligation is the decode fact of a step (one per step). -/
def isDec : SOb → Bool
  | .decM .. | .decT .. | .decO .. => true
  | _ => false

/-- Merge a list of half-open ranges. -/
def mergeR (rs : List (Nat × Nat)) : List (Nat × Nat) :=
  let s := (rs.toArray.qsort fun a b => a.1 < b.1).toList
  s.foldl (fun acc r => match acc with
    | (l, h) :: t => if r.1 ≤ h then (l, max h r.2) :: t else r :: (l, h) :: t
    | [] => [r]) [] |>.reverse

/-- Kinds of address need: 0 owned read, 1 data-view read, 2 owned write, 3 alignment,
4 havoc read (access check only). -/
structure Need where
  atom : SE
  offs : List (BitVec 64 × Nat × Nat)

def needOf (o : SOb) : Option (SE × BitVec 64 × Nat × Nat) :=
  match o with
  | .ld e w => some ((base e).1, (base e).2, w, 0)
  | .ldD e w => some ((base e).1, (base e).2, w, 1)
  | .st e w => some ((base e).1, (base e).2, w, 2)
  | .ldH e w => some ((base e).1, (base e).2, w, 4)
  | _ => none

def addNeed (ns : List Need) (o : SOb) : List Need :=
  match needOf o with
  | none => ns
  | some (a, off, w, k) =>
    if a = .c 0 then ns else
    if ns.any (·.atom = a) then
      ns.map fun n => if n.atom = a then { n with offs := (off, w, k) :: n.offs } else n
    else ⟨a, [(off, w, k)]⟩ :: ns

def signedOf (o : BitVec 64) : Int := if o.toNat ≥ 2 ^ 63 then (o.toNat : Int) - 2 ^ 64 else o.toNat

def factOf (n : Need) : AFact :=
  let m := (n.offs.map fun e => signedOf e.1).foldl min 0
  let shift : BitVec 64 := BitVec.ofInt 64 m
  let rel (o : BitVec 64) : Nat := (o - shift).toNat
  let spans := (n.offs.filter (·.2.2 ≠ 3)).map fun e => (rel e.1, rel e.1 + e.2.1)
  let stores := (n.offs.filter (·.2.2 = 2)).map fun e => (rel e.1, rel e.1 + e.2.1)
  let al4 := n.offs.any (·.2.2 = 3)
  let maxRel := (n.offs.map fun e => rel e.1 + e.2.1).foldl max 0
  let omin := (spans.map (·.1)).foldl min (2 ^ 64)
  let omax := (spans.map (·.2)).foldl max 0
  let smin := (stores.map (·.1)).foldl min (2 ^ 64)
  let am0 := (stores.map fun r => r.2 - r.1).foldl max 1
  let am := if al4 then max am0 4 else am0
  let lo := if spans.isEmpty then 0 else
    max (0x80000000 - omin) (if stores.isEmpty then 0 else tohostAddr + 16 - smin)
  let hi := if spans.isEmpty then 2 ^ 64 - 1 - maxRel else 0x100000000 - omax
  { atom := n.atom, lo := lo, hi := hi, amod := am,
    sc := mergeR ((n.offs.filter fun e => e.2.2 = 0 ∨ e.2.2 = 2).map fun e => (rel e.1, rel e.1 + e.2.1)),
    dc := mergeR ((n.offs.filter (·.2.2 = 1)).map fun e => (rel e.1, rel e.1 + e.2.1)),
    gap := if spans.isEmpty then none else some (omax, 8 - omin), shift := shift }

def geomOf (obs : List SOb) : Geom :=
  (((obs.foldl addNeed []).map factOf).filter (·.atom.noHv)).reverse


/-- Atoms whose owned reads are needed. -/
def ownedReadAtoms (obs : List SOb) : List SE :=
  obs.filterMap fun o => match o with
    | .ld e _ => if (base e).1 = .c 0 then none else some (base e).1
    | _ => none

/-! ## Branch premises in step-lemma form -/

theorem gF_beq (a b : BitVec 64) : guardB .BEQ a b = false ↔ ¬ (a = b) := guard_false (guard_beq a b)
theorem gF_bne (a b : BitVec 64) : guardB .BNE a b = false ↔ ¬ (a ≠ b) := guard_false (guard_bne a b)
theorem gF_blt (a b : BitVec 64) : guardB .BLT a b = false ↔ ¬ (a.toInt < b.toInt) :=
  guard_false (guard_blt a b)
theorem gF_bge (a b : BitVec 64) : guardB .BGE a b = false ↔ ¬ (b.toInt ≤ a.toInt) :=
  guard_false (guard_bge a b)
theorem gF_bltu (a b : BitVec 64) : guardB .BLTU a b = false ↔ ¬ (a.toNat < b.toNat) :=
  guard_false (guard_bltu a b)
theorem gF_bgeu (a b : BitVec 64) : guardB .BGEU a b = false ↔ ¬ (b.toNat ≤ a.toNat) :=
  guard_false (guard_bgeu a b)

/-! ## The driver -/

open Lean Meta Elab Tactic

/-- Denotation normaliser: symbolic values, havoc slots, register and memory folds. -/
macro "sym_den" : tactic => `(tactic| simp (disch := decide) only [regsDen, memDen, SE.den, aluVal,
  Env.withH, hset_self, hset_ne, shamtOf, shamt5Of, imm20Of, BitVec.reduceExtractLsb'])

/-- `sx_norm` on the branch premise just introduced, while it is the last hypothesis (a
step-by-step run normalises it at the next step, before any later premise exists). -/
macro "sym_hnorm " h:ident : tactic =>
  `(tactic| simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, reduceIte,
        LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.reduceSignExtend,
        Sail.shift_bits_left, Sail.shift_bits_right, Sail.BitVec.extractLsb,
        BitVec.reduceExtractLsb, BitVec.reduceHShiftLeft, BitVec.reduceHShiftRight,
        BitVec.reduceShiftLeft, BitVec.reduceUShiftRight, BitVec.shiftLeft_eq',
        BitVec.ushiftRight_eq', BitVec.reduceToNat,
        BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceOfNat, VsaIris.ra, Nat.reduceAdd,
        BitVec.reduceAppend, not_true_eq_false] at $h:ident)

/-- Unfolding `rawR`, as a rewrite with a proof: a definitional change of a branch premise
leaves the kernel to compare the entry register chain against its unfolding. -/
theorem rawR_eq (R : Nat → BitVec 64) (i : Nat) : rawR R i = R i := Eq.trans rfl rfl

theorem geom_nil (ρ : Env) (S : Nat → Prop) (DA : List Nat) : Geom.holds ρ S DA [] :=
  fun _ h => nomatch h

theorem geom_cons {ρ : Env} {S : Nat → Prop} {DA : List Nat} {f : AFact} {Γ : Geom}
    (h1 : Geom.holds ρ S DA [f]) (h2 : Geom.holds ρ S DA Γ) : Geom.holds ρ S DA (f :: Γ) :=
  fun g hg => (List.mem_cons.1 hg).elim (fun e => h1 g (e ▸ List.mem_singleton.2 rfl)) (h2 g)


/-- The `Geom` of a run. -/
def geomRun (C : Cfg) (n : Nat) (s : SS) : Geom := geomOf (Tree.obs (symRun C n s))

open Lean Meta Elab Term in
/-- `geom% C n s` is the literal value of `geomRun C n s`, computed by compiled evaluation at
elaboration time: the kernel never evaluates `geomOf` (its `qsort` does not reduce there). -/
elab "geom% " t:term : term => do
  let e ← elabTerm t (some (mkConst ``Geom))
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let v ← unsafe evalExpr Geom (mkConst ``Geom) e
  return toExpr v

open Lean Meta Elab Tactic in
/-- Split a residual `Tree.WP` of a literal tree into its obligations, branch
sides (premise introduced) and continuations; decode facts close by `sym_dec`. -/
partial def symSplitGoal (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  if ty.isAppOfArity ``Tree.WP 5 then
    let t := ty.appArg!
    let lem := match t.getAppFn.constName? with
      | some ``Tree.leaf => some ``Tree.WP_leaf
      | some ``Tree.br => some ``Tree.WP_br
      | some ``Tree.jr => some ``Tree.WP_jr
      | _ => none
    let some lem := lem | return [g]
    let gs ← g.apply (← mkConstWithFreshMVarLevels lem)
    let mut out := []
    for g' in gs do
      let g'' ← if (← instantiateMVars (← g'.getType)).isForall then
          pure (← g'.intro1).2 else pure g'
      let g'' ← (do
        let r ← Lean.Elab.Tactic.evalTacticAt (← `(tactic| dsimp only)) g''
        match r with | [x] => pure x | _ => pure g'') <|> pure g''
      out := out ++ (← symSplitGoal g'')
    return out
  if ty.isAppOfArity ``ObsOK 4 then
    let l ← whnf ty.appArg!
    if l.isAppOfArity ``List.nil 1 then
      let _ ← g.apply (← mkConstWithFreshMVarLevels ``ObsOK_nil); return []
    if l.isAppOfArity ``List.cons 3 then
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``ObsOK_cons)
      let mut out := []
      for g' in gs do out := out ++ (← symSplitGoal g')
      return out
    return [g]
  if ty.isAppOfArity ``SOb.den 4 then
    let o := ty.appArg!
    if o.isAppOf ``SOb.decM || o.isAppOf ``SOb.decT || o.isAppOf ``SOb.decO then
      let gs ← evalTacticAt (← `(tactic| (simp only [SOb.den]; sym_dec))) g
      return gs
    return [g]
  return [g]

open Lean Elab Tactic in
elab "sym_split" : tactic => do
  let gs ← getGoals
  let mut out := []
  for g in gs do out := out ++ (← symSplitGoal g)
  setGoals out

end VsaIris.SymExec.Interp
