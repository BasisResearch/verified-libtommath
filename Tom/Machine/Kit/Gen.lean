import Tom.Machine.Kit.Auto
import Tom.Machine.Kit.AutoEq
import Tom.Machine.Kit.MulCall
import Tom.Machine.Kit.MemCopy
import Tom.Machine.Kit.Word
import Tom.Machine.Kit.Alu1
import Tom.Machine.Kit.GenAttr
import Tom.Machine.Repr
import Tom.Machine.Code

/-!
# One segment rule with pluggable closers, and loads answered by facts

`seg_go chain pc lds ks kk [defs] [post] [eqs] hc` is `seg_at'` with its four
goals closed by registries instead of by a family of tactic variants. `scripts/gen_rows.py` emits
it, one per annotated row; it is also the hand-written form.

* **leaves** by `seg_leaf [defs]`: a code frame (`seg_frame`); a load, store,
  return or guard (`seg_leaf_std`, word, doubleword and byte loads); a bare
  guard (`seg_leaf_guard`); a store through a loaded pointer; then the
  extension point `seg_leaf_ext` (every `macro_rules` alternative of it is
  tried). On failure the leaf is shown normalised.
* **values** by `seg_vnf [eqs]`: the load data folded back to total reads, every
  read answered by a fact (`load_fwd`), then `val_nf` and the `@[seg_val]`
  lemmas (Kit/GenAttr.lean) under `omega`.
* **equations** by `seg_close` (extensible: `macro_rules | `(tactic| seg_close) => …`),
  the sign-extension forms of `seg_stepx` included; `seg_go … using tac` runs
  `tac` on what is left (`seg_stepw`/`seg_stepu`).

`load_fwd`: a read `bytesT4 M e`, `bytesT8 M e` or byte
`(M[e]?).getD 0` (`bytesT1`) in the goal is answered by any hypothesis, or field
of a structure hypothesis three levels deep, `bytesT_w M a = v` with `e = a` by
`omega`. No prepared equations, address renormalisations or `.sx` theorems:
sign and zero extension are `val_nf`/`@[seg_val]` with the bound in context.

`seg_ctx hc` reads the code base and length from the type of `hc : CodeAt M base
code` (no per-file `*_ctx` macro) and puts the arithmetic fields of every
structure hypothesis in context (as `facts_ctx`, with `BitVec` alignment fields
such as `ra.toNat % 4 = 0`; never memory fields). Their disjunctions (`Ram`'s
HTIF window, code and region disjointness) go in as `OrH p q`, which `omega`
does not split: `omega_split` opens them one (then two) at a time when plain
`omega` fails. With every disjunction in sight, each `omega` of a segment split
them all (seconds per leaf, the heartbeat budget of a long chain).

`seg_facts hc` is `tom_facts hc` deciding by a syntactic test (a store word in
the chain memory, `storesIn`) whether a code pin goes through `CodeAt.of_eq`:
`tom_facts` first tries a default-transparency unification of the two memories,
which fails after a store at a cost of seconds per pin.
-/

namespace Tom.Machine

open Lean Elab Tactic Meta

/-- The byte at `a`: what an `lbu` reads (a fact `bytesT1 M a = v` answers it). -/
abbrev bytesT1 (m : Mem) (a : Nat) : BitVec 8 := (m[a]?).getD 0

/-- A disjunctive fact kept out of `omega`'s sight: `omega` splits every
disjunction in context, so `seg_ctx` wraps them, and `omega_split` opens the
few most relevant to the goal. -/
def OrH (p q : Prop) : Prop := p ∨ q

theorem OrH.mk {p q : Prop} (h : p ∨ q) : OrH p q := h

/-- The hypotheses relevant to `seed`: `r` rounds of sharing a free variable with it (facts
without free variables always). Wrapped disjunctions are left out. -/
def relHyps (seed : Expr) (r : Nat) : MetaM (List Expr) := do
  let mut S : FVarIdSet := (collectFVars {} seed).fvarSet
  let mut cand : Array (FVarId × Expr × FVarIdSet) := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    if ty.isAppOfArity ``Tom.Machine.OrH 2 then continue
    cand := cand.push (d.fvarId, d.toExpr, (collectFVars {} ty).fvarSet)
  let mut chosen : Std.HashSet FVarId := {}
  for _ in [0:r] do
    let mut S' := S
    for (id, _, fv) in cand do
      if chosen.contains id then continue
      if fv.isEmpty || fv.toList.any S.contains then
        chosen := chosen.insert id
        S' := fv.toList.foldl (fun s x => s.insert x) S'
    S := S'
  return (cand.filter fun (id, _, _) => chosen.contains id).toList.map (·.2.1)

/-- `omega` (as the tactic: `falseOrByContra`, the proof in an auxiliary theorem) over the
facts relevant to the goal (`some r`: `relHyps`; `none`: every hypothesis), with the wrapped
disjunctions `ors` opened. -/
def omegaCore (g : MVarId) (r : Option Nat) (ors : List LocalDecl) : MetaM Unit := do
  let seed ← instantiateMVars (← g.getType)
  let some g ← g.falseOrByContra | return ()
  g.withContext do
    let type ← g.getType
    let hs ← getLocalHyps
    let facts ← match r with
      | none => pure hs.toList
      | some k => do
        let fs ← relHyps seed k
        -- the negated goal (the last hypothesis after `falseOrByContra`)
        let last := hs.back!
        pure (if fs.contains last then fs else fs ++ [last])
    let os ← ors.mapM fun d => do
      let ty ← instantiateMVars d.type
      mkExpectedTypeHint d.toExpr (mkOr (ty.getArg! 0) (ty.getArg! 1))
    let g' ← mkFreshExprSyntheticOpaqueMVar type
    Lean.Elab.Tactic.Omega.omega (facts ++ os) g'.mvarId! {}
    let e ← mkAuxTheorem type (← instantiateMVars g') (zetaDelta := true)
    g.assign e

def tryOmegaCore (g : MVarId) (r : Option Nat) (ors : List LocalDecl) : MetaM Bool := do
  let s ← saveState
  try omegaCore g r ors; return true
  catch _ => s.restore; return false

/-- `omega` over the hypotheses that share a variable with the goal, else over all
(`omega` succeeds exactly when it does). Every fact `omega` is given costs elaboration and
kernel time in its certificate, so the few relevant ones go first. -/
def omegaRel (g : MVarId) : MetaM Bool := do
  if ← (try withReducibleAndInstances g.assumptionCore catch _ => pure false) then return true
  if ← tryOmegaCore g (some 1) [] then return true
  tryOmegaCore g none []

elab "omega_rel" : tactic => do
  if ← omegaRel (← getMainGoal) then replaceMainGoal [] else throwError "omega_rel: failed"

/-- A read in a term: its width, memory and address. -/
def readOf? (e : Expr) : Option (Nat × Expr × Expr) :=
  if e.isAppOfArity ``Vsa.Sim.bytesT4 2 then some (4, e.getArg! 0, e.getArg! 1)
  else if e.isAppOfArity ``Vsa.Sim.bytesT8 2 then some (8, e.getArg! 0, e.getArg! 1)
  else if e.isAppOfArity ``Tom.Machine.bytesT1 2 then some (1, e.getArg! 0, e.getArg! 1)
  else if e.isAppOfArity ``Option.getD 3 then
    let x := e.getArg! 1
    if x.isAppOfArity ``GetElem?.getElem? 7 then some (1, x.getArg! 5, x.getArg! 6) else none
  else none

/-- The memory reads `bytesT_w M a = v` among `e : ty` and its structure fields. -/
partial def memFactsOf (e ty : Expr) (d : Nat) : MetaM (Array (Expr × Nat × Expr × Expr)) := do
  let ty ← instantiateMVars ty
  if let some (_, lhs, _) := ty.eq? then
    if let some (w, m, a) := readOf? lhs then return #[(e, w, m, a)]
    return #[]
  let some sn := ty.getAppFn.constName? | return #[]
  let env ← getEnv
  unless isStructure env sn && d > 0 do return #[]
  let mut out := #[]
  for f in getStructureFields env sn do
    let e? : Option Expr ← try pure (some (← mkAppM (sn ++ f) #[e])) catch _ => pure none
    let some e' := e? | continue
    let fty ← instantiateMVars (← inferType e')
    unless ← isProp fty do continue
    out := out ++ (← memFactsOf e' fty (d - 1))
  return out

/-- Prove `a = b` (Nat) by `rfl` or `omega_rel` in the main goal's context. -/
def eqByOmega (a b : Expr) : TacticM (Option Expr) := withMainContext do
  if ← withReducible (isDefEq a b) then return some (← mkEqRefl a)
  let m ← mkFreshExprSyntheticOpaqueMVar (← mkEq a b)
  if ← omegaRel m.mvarId! then return some (← instantiateMVars m) else return none

elab "load_fwd" : tactic => withMainContext do
  let mut facts := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    facts := facts ++ (← memFactsOf d.toExpr ty 3)
  if facts.isEmpty then return
  let tgt ← instantiateMVars (← getMainTarget)
  let rs : IO.Ref (Array Expr) ← IO.mkRef #[]
  forEachExpr' tgt fun x => do
    if (readOf? x).isSome then
      rs.modify fun a => if a.contains x then a else a.push x
      return false
    return true
  let reads ← rs.get
  for r in reads do
    let some (w, m, e) := readOf? r | continue
    for (pf, w', m', a) in facts do
      unless w == w' do continue
      unless ← withReducible (isDefEq m m') do continue
      let some heq ← eqByOmega e a | continue
      -- pf : read m' a = v; heq : e = a
      let pfTy ← inferType pf
      let some (_, lhs, _) := pfTy.eq? | continue
      let fn := lhs.appFn!
      let h0 ← mkEqTrans (← mkCongrArg fn heq) pf
      let some (_, _, v) := (← inferType h0).eq? | continue
      let h ← mkExpectedTypeHint h0 (← mkEq r v)
      let g ← getMainGoal
      let res ← (try some <$> g.rewrite (← g.getType) h catch _ => pure none)
      let some res := res | continue
      let g' ← g.replaceTargetEq res.eNew res.eqProof
      replaceMainGoal (g' :: res.mvarIds)
      break

/-- `Ram lo len` as two bounds and the HTIF-window disjunction (wrapped). -/
theorem ram_bounds3 {lo len : Nat} (h : Ram lo len) :
    0x80000000 ≤ lo ∧ lo + len ≤ 0x100000000 ∧ OrH (lo + len + 8 ≤ 0x80018880) (0x80018890 ≤ lo) :=
  ⟨h.lo_ge, h.hi_le, h.off⟩

/-- `omega`, else `omega` after splitting one, then two, wrapped disjunctions (in context
order; `omega_split`'s last resort). -/
partial def omegaSplitCore (g : MVarId) (k : Nat) : TacticM Bool := do
  let s ← saveState
  let ok ← try
      let gs ← Tactic.run g (evalTactic (← `(tactic| omega)))
      pure gs.isEmpty
    catch _ => pure false
  if ok then return true
  s.restore
  if k == 0 then return false
  let ds ← g.withContext do
    return (← getLCtx).decls.toList.filterMap id |>.filter fun d =>
      (d.type.isAppOfArity ``Tom.Machine.OrH 2)
  for d in ds do
    let s ← saveState
    let p := d.type.getArg! 0
    let q := d.type.getArg! 1
    let g1 ← g.replaceLocalDeclDefEq d.fvarId (mkOr p q)
    let subs ← (try some <$> g1.cases d.fvarId catch _ => pure none)
    let some subs := subs | s.restore; continue
    let mut all := true
    for sg in subs do
      unless ← omegaSplitCore sg.mvarId (k - 1) do all := false; break
    if all then return true
    s.restore
  return false

/-- The atoms of `e` for relevance: free variables, constants, literals ≥ 2^16. -/
def splitAtoms (e : Expr) : MetaM (Std.HashSet String) := do
  let r : IO.Ref (Std.HashSet String) ← IO.mkRef {}
  forEachExpr' e fun x => do
    match x with
    | .fvar id => r.modify (·.insert s!"f{id.name}")
    | .const n _ =>
      unless n.isInternal || n.getPrefix == `Nat || n.getPrefix == `HAdd do
        r.modify (·.insert s!"c{n}")
    | .lit (.natVal k) => if k ≥ 65536 then r.modify (·.insert s!"n{k}")
    | _ => pure ()
    return true
  r.get

/-- The wrapped disjunctions of `g`, most relevant first: those that mention the target's
leading variable (an address's base: the region it lies in), then by the atoms they share
with the target and with the hypotheses after the last of them (a code-frame leaf's address
bounds); ties in context order. -/
def orHsOf (g : MVarId) : MetaM (List LocalDecl) := g.withContext do
  let mut ta ← splitAtoms (← instantiateMVars (← g.getType))
  let decls := (← getLCtx).decls.toList.filterMap id
  let ds := decls.filter fun d => d.type.isAppOfArity ``Tom.Machine.OrH 2
  if let some lastOr := ds.getLast? then
    for d in decls do
      if d.index > lastOr.index && !d.isImplementationDetail then
        let ty ← instantiateMVars d.type
        if ← isProp ty then
          for a in (← splitAtoms ty) do ta := ta.insert a
  -- the target's leading variable that some wrapped disjunction mentions (an address's base:
  -- the region it lies in)
  let orFv : FVarIdSet := ds.foldl (fun s d =>
    (collectFVars {} d.type).fvarSet.toList.foldl (fun s x => s.insert x) s) {}
  let lead : IO.Ref (Option FVarId) ← IO.mkRef none
  forEachExpr' (← instantiateMVars (← g.getType)) fun x => do
    if (← lead.get).isSome then return false
    if let .fvar id := x then
      if orFv.contains id then lead.set (some id)
    return true
  let lead ← lead.get
  let mut sc : Array (Nat × Nat × LocalDecl) := #[]
  let mut i := 0
  for d in ds do
    let a ← splitAtoms d.type
    let bonus := match lead with
      | some id => if d.type.containsFVar id then 10 else 0
      | none => 0
    sc := sc.push (bonus + a.fold (fun n x => if ta.contains x then n + 1 else n) 0, i, d)
    i := i + 1
  let sc2 := sc.qsort fun (n, i, _) (m, j, _) => n > m || (n == m && i < j)
  return (sc2.map (·.2.2)).toList

/-- `omega` with the one, two, three most relevant wrapped disjunctions opened (one call each:
`omega` splits an opened disjunction only when it needs it), over the relevant facts, then
over all; last, the old search (`omegaSplitCore`: any two opened, one at a time). -/
elab "omega_split" : tactic => do
  let g ← getMainGoal
  let ds ← orHsOf g
  for (k, r) in [(1, some 1), (2, some 1), (3, some 1), (3, none)] do
    if ← tryOmegaCore g r (ds.take k) then
      replaceMainGoal []; return
  if ← omegaSplitCore g 2 then replaceMainGoal [] else throwError "omega_split: failed"

/-- The context of a segment proof from `hc : CodeAt M base code`: `base = N`,
`code.length = n`, and the arithmetic facts of the structure hypotheses. -/
partial def ctxFactsOf (env : Environment) (memF : Array FVarId) (e ty : Expr) (d : Nat) :
    MetaM (Array Expr) := do
  let some sn := ty.getAppFn.constName? | return #[]
  unless isStructure env sn do return #[]
  if sn == ``Tom.Machine.Ram then
    let b ← mkAppM ``Tom.Machine.ram_bounds3 #[e]
    let b2 ← mkAppM ``And.right #[b]
    return #[← mkAppM ``And.left #[b], ← mkAppM ``And.left #[b2], ← mkAppM ``And.right #[b2]]
  let mut out := #[]
  for f in getStructureFields env sn do
    let e? : Option Expr ← try pure (some (← mkAppM (sn ++ f) #[e])) catch _ => pure none
    let some e' := e? | continue
    let fty ← instantiateMVars (← inferType e')
    unless ← isProp fty do continue
    let fsn := fty.getAppFn.constName?.getD .anonymous
    if isStructure env fsn then
      if d > 0 then out := out ++ (← ctxFactsOf env memF e' fty (d - 1))
    else if fsn != ``Tom.Machine.Disj && !(fty.hasAnyFVar memF.contains) &&
        !(fty.find? (fun x => x.isConstOf ``Std.ExtHashMap)).isSome then
      if fty.isAppOfArity ``Or 2 then out := out.push (← mkAppM ``Tom.Machine.OrH.mk #[e'])
      else out := out.push e'
  return out

elab "seg_ctx " h:term : tactic => withMainContext do
  let hE ← elabTerm h none
  let ty ← instantiateMVars (← inferType hE)
  unless ty.isAppOfArity ``Tom.Machine.CodeAt 3 do throwError "seg_ctx: expected a CodeAt hypothesis"
  let base := ty.getArg! 1
  let code := ty.getArg! 2
  let b ← whnfD base
  let bn? ← match b.rawNatLit? with
    | some n => pure (some n)
    | none => (Meta.evalNat b).run
  let some bn := bn? | throwError "seg_ctx: base {b} is not a literal"
  let mut n := 0
  let mut c ← whnfD code
  while c.isAppOfArity ``List.cons 3 do
    n := n + 1
    c ← whnfD (c.getArg! 2)
  let bs ← Term.exprToSyntax base
  let cs ← Term.exprToSyntax code
  evalTactic (← `(tactic| have : $bs = $(quote bn) := rfl))
  -- a long code list (`mp_div`: 370 words) exceeds the elaborator's recursion depth by `rfl`
  if n ≤ 256 then
    evalTactic (← `(tactic| have : List.length $cs = $(quote n) := rfl))
  else
    evalTactic (← `(tactic| have : List.length $cs = $(quote n) := by decide +kernel))
  -- the facts
  let g ← getMainGoal
  let env ← getEnv
  let facts ← g.withContext do
    let mut memF := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      if ← withReducible (isDefEq d.type (mkConst ``Tom.Machine.Mem)) then memF := memF.push d.fvarId
    let mut acc := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless ← isProp ty do continue
      acc := acc ++ (← ctxFactsOf env memF d.toExpr ty 3)
    pure acc
  let mut g := g
  for e in facts do
    let (_, g') ← (← g.assert `this (← g.withContext (inferType e)) e).intro1P
    g := g'
  replaceMainGoal [g]

/-- A zero extension (`lbu`, `lwu`, `zext.b`) as an `ofNat` of the value. -/
theorem zext_toNat {k : Nat} (x : BitVec k) (h : k ≤ 64) :
    LeanRV64DExecutable.zero_extend (m := 64) x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  have hx : x.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)
  simp [LeanRV64DExecutable.zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

attribute [seg_val] Tom.Machine.zext32_ofNat zext_toNat BitVec.toNat_ofNat Tom.Machine.ofNat_mul_ofNat

/-- A low mask (`zext.b`, `andi 255`). -/
theorem and255_mod (x : Nat) : BitVec.ofNat 64 x &&& 255#64 = BitVec.ofNat 64 (x % 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  rw [show (255 : Nat) % 2 ^ 64 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `slli rd, rs, 32; srli rd, rd, 32` of a sign-extended word: its zero extension. -/
theorem zext32_shifts {w : Nat} (hw : w = 32) (y : BitVec w) :
    Sail.shift_bits_right (Sail.shift_bits_left (BitVec.signExtend 64 y) 32#6) 32#6 =
      BitVec.ofNat 64 y.toNat := by
  subst hw
  unfold Sail.shift_bits_left Sail.shift_bits_right
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_ofNat, BitVec.toNat_ofNat]
  by_cases h : i < 32
  · simp [h, BitVec.getElem_signExtend, BitVec.testBit_toNat, BitVec.getLsbD_eq_getElem, show 32 + i < 64 by omega,
      show ¬ (32 + i < 32) by omega, show i < 64 by omega]
  · have : y.toNat < 2 ^ i := Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    simp [h, Nat.testBit_lt_two_pow this]
    omega

attribute [seg_val] and255_mod zext32_shifts

/-- A word of either sign whose 64-bit value is its sign extension (`addiw`
below zero: `omega` cannot close the `sext_ofNatW_div` form, which needs the
dark shadow). -/
theorem sext_ofNat_mod (X : Nat) (h : X % 2 ^ 64 < 2 ^ 31 ∨ 2 ^ 64 - 2 ^ 31 ≤ X % 2 ^ 64) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (X % 4294967296)) = BitVec.ofNat 64 X := by
  rw [sext_ofNatW_div rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have h1 : X % 4294967296 % 4294967296 = X % 2 ^ 64 % 4294967296 := by omega
  rcases h with h | h
  · have : X % 2 ^ 64 % 4294967296 = X % 2 ^ 64 := Nat.mod_eq_of_lt (by omega)
    omega
  · omega

attribute [seg_val] sext_ofNat_mod Nat.mod_mod BitVec.signExtend_eq

/-- Does a chain memory `m` (a nest of `stepMemM`/`writeLog … wlogM`) contain a
store instruction (`mkLine pc w` with opcode `0x23`)? -/
def storesIn (m : Expr) : MetaM Bool := do
  let found : IO.Ref Bool ← IO.mkRef false
  forEachExpr' m fun x => do
    if x.isAppOfArity ``Vsa.Sim.mkLine 2 then
      if let some ⟨_, w⟩ ← getBitVecValue? (x.getArg! 1) then
        if w.toNat % 128 == 0x23 then found.set true
      return false
    return true
  found.get

/-- `tom_facts h` (Kit/Code.lean) without its slow path: a byte pin on memory
other than `h`'s goes straight to `CodeAt.of_eq h ?_` (the failed `exact` costs
a default-transparency unification of two memories, seconds per pin after a
store). -/
partial def sfSolve (h : Term) (hm : Expr) (g : MVarId) : TacticM (List MVarId) := do
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  let run (tac : TSyntax `tactic) : TacticM Unit := do
    let gs ← Tactic.run g (evalTactic tac)
    unless gs.isEmpty do throwError "seg_facts: leaf not closed"
  let pins (lem : Ident) : TacticM (List MVarId) := do
    let m := ty.getArg! 0
    if !(← storesIn m) then
      Tactic.run g (evalTactic (← `(tactic| exact $lem $h (by decide +kernel))))
    else
      Tactic.run g (evalTactic (← `(tactic| refine $lem (CodeAt.of_eq $h ?_) (by decide +kernel))))
  match ty.getAppFn.constName? with
  | some ``And =>
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``And.intro)
      let mut acc : List MVarId := []
      for g' in gs do acc := acc ++ (← sfSolve h hm g')
      return acc
  | some ``Vsa.Sim.BytePinsM => pins (mkIdent ``Tom.Machine.bytePinsM_of)
  | some ``Vsa.Sim.BytePinsT => pins (mkIdent ``Tom.Machine.bytePinsT_of)
  | some ``Vsa.Sim.DecodeFactM | some ``Vsa.Sim.DecodeFactT =>
      run (← `(tactic| exact fun s h1 h2 h3 => Vsa.Sim.decodeW s h1 h2 h3)); return []
  | some ``True => g.assign (mkConst ``True.intro); return []
  | some ``Vsa.Sim.ChainFacts | some ``Vsa.Sim.BBlockFacts | some ``Vsa.Sim.ProgFactsM
  | some ``Vsa.Sim.TermPins | some ``Vsa.Sim.TermFactsO =>
      let g' ← g.change (← g.withContext (whnf ty))
      sfSolve h hm g'
  | _ =>
      if ← g.withContext (isDefEq ty (mkConst ``True)) then
        g.assign (mkConst ``True.intro); return []
      else
        return [g]

elab "seg_facts " h:term : tactic => withMainContext do
  let hE ← elabTerm h none
  let hT ← instantiateMVars (← inferType hE)
  unless hT.isAppOfArity ``Tom.Machine.CodeAt 3 do throwError "seg_facts: expected a CodeAt hypothesis"
  let leftovers ← sfSolve h (hT.getArg! 0) (← getMainGoal)
  setGoals leftovers

/-- Drop pins to a list drawn from the state's by lookup (`SubL`). -/
theorem At.weakenS {pc : BitVec 64} {L L' : Vsa.Sim.GRegs} {m : Tom.Machine.Mem} {keep : Vsa.Sim.GRegs}
    {outp : Array String}
    {c : Vsa.Machine.Config} (h : At pc L m keep outp c) (hs : SubL L' L) : At pc L' m keep outp c :=
  { h with regs := gholds_of_subL h.regs hs }

/-! The fixed lemma lists of the closers below, as the simp sets of `Kit/GenAttr.lean`
(indexed once, not at every call). `gleaf_nf`, `gseg_nfo` and `gval_nf` are `leaf_nf`,
`seg_nfo` (`Kit/At.lean`) and `val_nf` (`Kit/Auto.lean`) on these sets. -/

attribute [seg_dec] Vsa.Sim.mkLine Vsa.Sim.decodeM BitVec.reduceExtractLsb' BitVec.reduceToNat
  Nat.reduceEqDiff Option.some.injEq reduceCtorEq
attribute [seg_dec ↓] reduceIte

attribute [seg_lnf] Vsa.Sim.guardB Vsa.Sim.eaddrM Vsa.Sim.srcVal Vsa.Sim.lookupG
  Vsa.Sim.runGM Vsa.Sim.stepGM Vsa.Sim.stepLdsM Vsa.Sim.wvalM Vsa.Sim.eraseG
  Vsa.Sim.bytesVal Vsa.Sim.ldsRunM Nat.reduceAdd Nat.reduceEqDiff
  Option.getD_some List.headD List.tail_cons Tom.Machine.writeLog_nil List.append_nil
  Sail.BitVec.addInt LeanRV64DExecutable.Functions.sign_extend
  Sail.BitVec.signExtend Sail.BitVec.extractLsb Tom.Machine.bv_append_eq BitVec.reduceAppend
  BitVec.reduceSignExtend BitVec.signExtend_eq Tom.Machine.toNat_ofNat_add
  Tom.Machine.toNat_ofNat'
attribute [seg_lnf ↓] reduceIte

attribute [seg_fr1] Vsa.Sim.stepMemM Vsa.Sim.mkLine Vsa.Sim.decodeM
  BitVec.reduceExtractLsb' BitVec.reduceToNat Nat.reduceEqDiff reduceCtorEq
attribute [seg_fr1 ↓] reduceIte
attribute [seg_fr1 ←] Tom.Machine.writeLog_single

attribute [seg_fr2] Vsa.Sim.wlogM Vsa.Sim.mkLine Vsa.Sim.decodeM
  BitVec.reduceExtractLsb' BitVec.reduceToNat Nat.reduceEqDiff reduceCtorEq
attribute [seg_fr2 ↓] reduceIte

attribute [seg_fr3] Vsa.Sim.OutL Vsa.Sim.wlogM Vsa.Sim.wentryM Vsa.Sim.widthOfM
  Vsa.Sim.eaddrM Vsa.Sim.srcVal Vsa.Sim.lookupG Vsa.Sim.runGM Vsa.Sim.stepGM
  Vsa.Sim.stepLdsM Vsa.Sim.wvalM Vsa.Sim.eraseG Vsa.Sim.bytesVal
  Nat.reduceAdd Nat.reduceEqDiff Option.getD_some List.headD and_true
  LeanRV64DExecutable.Functions.sign_extend Sail.BitVec.signExtend
  Tom.Machine.bv_append_eq BitVec.reduceAppend BitVec.reduceSignExtend
  Tom.Machine.ofNat_add_ofNat Tom.Machine.toNat_ofNat_add Tom.Machine.toNat_ofNat'
attribute [seg_fr3 ↓] reduceIte

attribute [seg_rd5] Tom.Machine.rd4_bytesD Tom.Machine.rd8_bytesD Tom.Machine.rd4_bytes
  Tom.Machine.rd8_bytes Tom.Machine.rd8_bytesD'

attribute [seg_imm] Vsa.Sim.shamtOf Vsa.Sim.shamt5Of Vsa.Sim.imm20Of BitVec.reduceExtractLsb'
  BitVec.reduceExtractLsb BitVec.reduceAppend BitVec.reduceSignExtend BitVec.reduceAdd
  BitVec.reduceToNat Nat.reduceAdd Nat.reduceMod

attribute [seg_vset] Vsa.Sim.shamt5Of BitVec.reduceExtractLsb'
  Tom.Machine.signExtend_ofNat32 Tom.Machine.signExtend_ofNat32' Tom.Machine.signExtend_ofNatW
  Tom.Machine.extractLsb_ofNat32' Tom.Machine.sext_and_mask28W Tom.Machine.extractLsb_sextW
  Tom.Machine.ofNat_add_ofNat Tom.Machine.ofNat_add_ofNatW Tom.Machine.and_mask28
  Tom.Machine.srl32_ofNat Tom.Machine.srl32_ofNat' Tom.Machine.srl32_ofNatW Tom.Machine.srl64_ofNat
  Tom.Machine.shl_ofNat' Tom.Machine.ofNat_sub_ofNatW Nat.reducePow Nat.reduceSub Nat.reduceAdd
  Tom.Machine.toNat_ofNat_add Tom.Machine.toNat_ofNat'

attribute [seg_cmps] Tom.Machine.ofNat_add_ofNat Tom.Machine.blt_ofNat
  Tom.Machine.bltu_ofNat' Tom.Machine.bgeu_ofNat' Tom.Machine.bge_zero_ofNat Tom.Machine.bge_ofNat
  Tom.Machine.bge_zero_sextW Tom.Machine.ofNat_beq' bne decide_eq_true_eq decide_eq_false_iff_not
  Bool.not_eq_true' Bool.not_eq_false' beq_self_eq_true Bool.not_true

attribute [seg_n1] Vsa.Sim.evalBlocksPC Vsa.Sim.evalBlocks Vsa.Sim.evalBlock
  Vsa.Sim.SegEvalState.init Vsa.Sim.chainEndPC Vsa.Sim.endPCB Vsa.Sim.nextPC0
  Vsa.Sim.tgtPCT Vsa.Sim.tgtPC0 List.nil_append List.cons_append

attribute [seg_n3] Vsa.Sim.runGM Vsa.Sim.stepGM Vsa.Sim.stepLdsM Vsa.Sim.ldsRunM Vsa.Sim.wvalM
  Vsa.Sim.eraseG Vsa.Sim.lookupG Vsa.Sim.srcVal Vsa.Sim.wentryM Vsa.Sim.eaddrM
  Vsa.Sim.bytesVal Vsa.Sim.wlogM Vsa.Sim.widthOfM Vsa.Sim.shamtOf Vsa.Sim.endPCM
  Vsa.Sim.imm20Of
  Nat.reduceAdd Nat.reduceEqDiff Option.getD_some List.headD List.tail_cons List.head?_cons
  List.nil_append List.cons_append List.cons.injEq Prod.mk.injEq and_true true_and
  Sail.BitVec.addInt Sail.BitVec.extractLsb LeanRV64DExecutable.Functions.sign_extend
  Sail.BitVec.signExtend Tom.Machine.bv_append_eq BitVec.reduceAppend
  BitVec.reduceSignExtend BitVec.reduceExtractLsb BitVec.reduceExtractLsb' BitVec.signExtend_eq
  BitVec.zero_add BitVec.reduceAdd BitVec.reduceOfInt BitVec.add_zero
  Tom.Machine.toNat_ofNat_add Tom.Machine.toNat_ofNat'
attribute [seg_n3 ↓] reduceIte

attribute [seg_cls] Tom.Machine.sext_m1 Tom.Machine.sext_1m Tom.Machine.sra32_ofNatW
  Tom.Machine.shl32_ofNatW Tom.Machine.ofNat_add_ofNat Tom.Machine.extractLsb_ofNat32'
  Tom.Machine.signExtend_ofNatW Nat.reducePow Nat.reduceMod

/-- `leaf_nf` (Kit/At.lean) on the simp sets. -/
syntax "gleaf_nf" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| gleaf_nf [$ls,*]) => `(tactic|
      (simp only [Vsa.Sim.MemFacts, Vsa.Sim.TermFactsT, Vsa.Sim.TermFactsO]
       try simp only [$ls,*]
       try simp only [seg_dec]
       simp only [seg_lnf]))

/-- `seg_nfo` (Kit/At.lean) on the simp sets. -/
syntax "gseg_nfo" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| gseg_nfo [$ls,*]) => `(tactic|
      (try simp only [$ls,*]
       simp only [seg_n1]
       try simp only [seg_dec]
       simp only [seg_n3]))

/-- `val_nf` (Kit/Auto.lean) on the simp sets, side conditions by `omega_rel`. -/
syntax "gval_nf" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| gval_nf [$es,*]) => `(tactic|
     (try simp only [seg_rd5]
      try simp only [$es,*]
      try simp (disch := omega_rel) only [seg_vset]))

/-- Fold load data back to total reads. -/
macro "seg_rd" : tactic => `(tactic|
  (try simp only [seg_rd5, Tom.Machine.rd1, List.getD_cons_zero]))

/-- Values: reads by facts, then the value normal form and the `@[seg_val]` lemmas. -/
syntax "seg_vnf" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| seg_vnf [$es,*]) => `(tactic|
      (seg_rd
       load_fwd
       try simp only [$es,*]
       try gval_nf [$es,*]
       try simp (disch := omega_rel) only [seg_val, $es,*]
       try gval_nf [$es,*]))

/-- The compare lemmas of `Kit/Arith.lean`. -/
macro "seg_cmp" : tactic => `(tactic|
  (simp (disch := omega_rel) only [seg_cmps]))

/-- Branch-guard closer: the compare lemmas under `omega`; for a word of either
sign, `sext_ofNatW_div` first (one `ofNat`, no case split). -/
macro "seg_guard" : tactic => `(tactic|
  first
  | (seg_cmp; all_goals omega_split)
  | (simp only [Tom.Machine.sext_ofNatW_div rfl]
     try seg_vnf []
     seg_cmp
     all_goals omega_split))

/-- `code_frame` with `omega_split` (the disjunctions `seg_ctx` wrapped). -/
syntax "seg_frame" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| seg_frame [$ls,*]) => `(tactic|
      (intro a h1 h2
       try simp only [seg_fr1]
       repeat rw [Vsa.Sim.writeLog_out]
       all_goals try simp only [$ls,*]
       all_goals
         try simp only [seg_fr2]
         simp only [seg_fr3]
         try omega_split
       all_goals try exact rfl))

/-- The extension point of `seg_leaf` (a file adds an alternative with
`macro_rules | `(tactic| seg_leaf_ext [$ds,*]) => …`; all are tried). -/
syntax "seg_leaf_ext" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules | `(tactic| seg_leaf_ext [$_ds,*]) => `(tactic| fail "seg_leaf: no closer")

/-- A load, a store, a return or a guard (`leaf_auto` with `load_fwd` for its `eqs`). -/
syntax "seg_leaf_std" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| seg_leaf_std [$ds,*]) => `(tactic|
      (gleaf_nf [$ds,*]
       try simp only [seg_rd5]
       try simp only [Tom.Machine.ofNat_add_ofNat, Tom.Machine.toNat_ofNat_add, Tom.Machine.toNat_ofNat']
       try simp only [seg_imm]
       all_goals first
       | (simp only [Vsa.Sim.tohostAddr]
          first
          | (refine ⟨⟨by omega_rel, by omega_rel, by omega_split⟩, Tom.Machine.lpins4_rd4_frame (by omega_rel) ?_⟩
             seg_frame [$ds,*])
          | (refine ⟨⟨by omega_rel, by omega_rel, by omega_split⟩, Tom.Machine.lpins8_rd8_frame (by omega_rel) ?_⟩
             seg_frame [$ds,*])
          | (refine ⟨⟨by omega_rel, by omega_rel, by omega_split⟩, ?_⟩
             first
             | with_reducible exact Tom.Machine.lbu_pin (by omega_rel)
             | (refine Tom.Machine.lbu_pin_frame (by omega_rel) ?_
                seg_frame [$ds,*])))
       | (simp only [Vsa.Sim.StoreWin, Vsa.Sim.tohostAddr]; omega_split)
       | (load_fwd
          try simp only [BitVec.add_zero, Tom.Machine.ofNat_add_ofNat, Tom.Machine.toNat_ofNat_add,
            Tom.Machine.toNat_ofNat']
          simp only [Vsa.Sim.tohostAddr, Vsa.Sim.StoreWin]
          first
          | omega_split
          | (refine ⟨⟨by omega_rel, by omega_rel, by omega_split⟩, Tom.Machine.lpins4_rd4_frame (by omega_rel) ?_⟩
             seg_frame [$ds,*])
          | (refine ⟨⟨by omega_rel, by omega_rel, by omega_split⟩, Tom.Machine.lpins8_rd8_frame (by omega_rel) ?_⟩
             seg_frame [$ds,*]))
       | (seg_vnf []
          first
          | (rw [Tom.Machine.ret_target _ (by assumption)]; assumption)
          | (rw [Tom.Machine.ret_target' _ (by assumption)]; assumption)
          | seg_guard)))

/-- Fail unless the goal is a bare branch guard `guardB … = b`. -/
elab "is_guard" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some (_, l, _) := t.eq? | throwError "is_guard: not a guard"
  unless l.isAppOf ``Vsa.Sim.guardB do throwError "is_guard: not a guard"

/-- A bare guard (an empty block before the branch: no `TermFacts` wrapper). -/
syntax "seg_leaf_guard" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| seg_leaf_guard [$ds,*]) => `(tactic|
      (is_guard
       try simp only [$ds,*]
       try simp only [seg_dec]
       simp only [seg_lnf]
       seg_vnf []
       seg_guard))

/-- One leaf of a chain, by the closers in order: a code frame; a load, store,
return or guard; a bare guard; a store through a loaded pointer; the extensions. -/
syntax "seg_leaf" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| seg_leaf [$ds,*]) => `(tactic|
      first
      | (seg_frame [$ds,*]; done)
      | (seg_leaf_std [$ds,*]; done)
      | (seg_leaf_guard [$ds,*]; done)
      | (seg_frame [$ds,*]
         all_goals (seg_vnf []
                    try simp only [BitVec.add_zero, Tom.Machine.ofNat_add_ofNat, BitVec.toNat_ofNat]
                    omega_split)
         done)
      | seg_leaf_ext [$ds,*]
      | ((first | gleaf_nf [$ds,*] | skip)
         (try seg_vnf [])
         fail "seg_leaf: no closer for this leaf (normalised)"))

/-- Equal values give equal words (`seg_close` tries it before `gbv_nat`: an equation of
values has no `% 2^64` atoms for `omega`). -/
theorem ofNat_congr64 {a b : Nat} (h : a = b) : BitVec.ofNat 64 a = BitVec.ofNat 64 b := h ▸ rfl

/-- `bv_nat` (Kit/Arith.lean) with `omega_rel`. -/
macro "gbv_nat" : tactic => `(tactic|
  (apply BitVec.eq_of_toNat_eq
   simp only [Tom.Machine.toNat_add', Tom.Machine.toNat_sub', Tom.Machine.toNat_ofNat']
   omega_rel))

/-- A word equation as an equation of the values, else by `gbv_nat`. -/
macro "seg_bv" : tactic => `(tactic|
  first
  | ((with_reducible refine Tom.Machine.ofNat_congr64 ?_) <;> omega_rel)
  | gbv_nat)

/-- One register or write-log equation (extensible). -/
syntax "seg_close" : tactic
macro_rules | `(tactic| seg_close) => `(tactic| (first | exact True.intro | omega_rel | seg_bv))
macro_rules | `(tactic| seg_close) => `(tactic|
  (try simp (disch := omega_rel) only [seg_cls]
   try simp (disch := omega_rel) only [sext_ofNat_mod, Nat.mod_mod]
   first | omega_rel | seg_bv))

/-- Split the conjunction of equations, close each (what is left stays open). -/
macro "seg_eqs" : tactic => `(tactic| ((repeat' (apply And.intro)) <;> try seg_close))

/-- **The segment rule with pluggable closers** (`seg_go chain pc lds ks kk [defs]
[post] [eqs] hc`, optionally `using tac` for what the closers leave). -/
syntax "seg_go " term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max
  " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term:max (" using " tacticSeq)? : tactic
macro_rules
  | `(tactic| seg_go $bs $pc $lds $ks $kk [$ds,*] [$ps,*] [$es,*] $hc $[using $tac?]?) => do
      let b ← `(Lean.Parser.Tactic.simpLemma| $bs:term)
      let l1 : Array (Lean.TSyntax ``Lean.Parser.Tactic.simpLemma) := #[b] ++ ds.getElems
      let l2 := l1 ++ ps.getElems
      let fin ← match tac? with
        | some t => `(tactic| all_goals ($t))
        | none => `(tactic| skip)
      `(tactic|
        (refine Tom.Machine.seg_at' $bs (pc1 := $pc) $lds $ks $kk ?_ ?_ ?_ ?_
           (hwf := by decide +kernel) (hfr := by decide +kernel) (hkeys := by decide +kernel)
           (hwr := by decide +kernel)
         · seg_facts $hc
           all_goals seg_leaf [$ds,*]
         · gseg_nfo [$l1,*]
           try (seg_vnf [$es,*]
                exact Tom.Machine.ret_target' _ (by assumption))
         · (try simp only [$l2,*])
           simp only [Tom.Machine.SubL]
           gseg_nfo [$l2,*]
           try simp only [Option.some.injEq]
           try seg_vnf [$es,*]
           try seg_eqs
           $fin
         · gseg_nfo [$l1,*]
           try seg_vnf [$es,*]
           try seg_eqs
           $fin))

end Tom.Machine
