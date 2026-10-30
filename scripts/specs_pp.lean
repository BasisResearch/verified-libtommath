import Lean

/-!
The pretty printer of `scripts/gen_specs.py` (`python3 scripts/gen_specs.py --lean` prepends
SPECS.lean's imports to this file, runs it, and keeps its output in `experiments/specs_pp.jsonl`).

`#spec_pp name : stmt := proof` elaborates the statement (`#spec_pp_thm name := thm`: the theorem's
own type), unfolds the contract's wrappers (`Statement`, `Spec`, `SpecR`, ...) and its definitions
(`entry`, `args`, `rets`, `Q`, `Ret`, `hin`, ...) down to the `Triple`, expands its precondition
structures (`Res`, `Pre`, `StkRes`, ...) into one hypothesis per field and its witness bundle
(`Bundle (lay p) (kind p) m`) into one hypothesis per region, and prints one JSON line: the binders
and the conclusion, pretty printed, and the arguments that rebuild the original hypotheses.
-/

open Lean Meta Elab Command Term

namespace SpecsPP

/-- The machine plumbing, never unfolded: the regions, their layout and kinds, the stack depth. -/
def keep : List String :=
  ["lay", "kind", "out", "site'", "isW", "F", "R", "Iv", "Kind", "textIv", "gpV", "Ff", "Fm", "Fd",
   "Fn", "Fs", "Fk", "Ft", "Fa", "Fb", "Fc", "Fr", "Fq", "memBV", "depth", "base", "μ"]

def short (n : Name) : String := match n with
  | .str _ s => s
  | _ => ""

/-- A contract's own definitions (not the allocator's, not the shared kit). -/
def contractConst (n : Name) : Bool :=
  let s := short n
  ((`Tom.Machine.Api).isPrefixOf n || (`Tom.Machine.Fn).isPrefixOf n) && !keep.contains s &&
  -- of the allocator's own definitions, only its contracts' entry points, registers and results
  ((!(`Tom.Machine.Api.Alloc).isPrefixOf n && !(`Tom.Machine.Api.Heap).isPrefixOf n) ||
    ((`Tom.Machine.Api.Alloc).isPrefixOf n &&
      (s.endsWith "Entry" || s.endsWith "L" || s.endsWith "Ret")))

/-- Structures whose fields become hypotheses. -/
def expandable (env : Environment) (n : Name) : Bool :=
  isStructure env n && !isClass env n && (contractConst n || n == `Tom.Machine.Std.StkRes)

/-- A definition to unfold: a contract's own, not a structure, projection or matcher. -/
def unfoldable (c : Name) : MetaM Bool := do
  let env ← getEnv
  return contractConst c && !isStructure env c && !(← isMatcher c) && !(← isProjectionFn c) &&
    (env.find? c matches some (.defnInfo _))

/-- Unfold `c args` once (plain delta and beta, no smart unfolding). -/
def delta1? (e : Expr) : MetaM (Option Expr) := do
  let .const c lvls := e.getAppFn | return none
  let some (.defnInfo d) := (← getEnv).find? c | return none
  return some ((d.value.instantiateLevelParams d.levelParams lvls).betaRev e.getAppRevArgs)

/-- Unfold the contract definitions everywhere. -/
def unfoldContract (e : Expr) : MetaM Expr := do
  let e ← Meta.transform e (post := fun e => do
    let e := e.headBeta
    let .const c _ := e.getAppFn | return .done e
    unless ← unfoldable c do return .done e
    let some e' ← delta1? e | return .done e
    -- not a recursive definition (`brecOn`, `WellFounded.fix`)
    if (e'.find? fun x => x.isConstOf ``WellFounded.fix ||
        (x.constName?.map (short · == "brecOn")).getD false).isSome then return .done e
    return .visit e'.headBeta)
  return (← instantiateMVars e).headBeta

/-- Reduce matchers on constructors and projections of structure literals, everywhere. -/
def simpReduce (e : Expr) : MetaM Expr := do
  Meta.transform e (post := fun e => do
    let e' ← whnfCore e
    if e' != e then return .visit e'
    let .const f _ := e.getAppFn | return .done e
    let some info ← getProjectionFnInfo? f | return .done e
    if e.getAppNumArgs != info.numParams + 1 then return .done e
    let s ← whnfCore e.appArg!
    if s.isAppOf info.ctorName then return .visit (s.getArg! (info.numParams + info.i))
    return .done e)

structure St where
  vars : Array Expr := #[]
  used : NameSet := {}

abbrev M := StateRefT St TermElabM

/-- A binder name: `pref` if it is free (not used; for a hypothesis, not a global in scope either),
else `h_pref`, else numbered. -/
def pick (pref : String) (hyp : Bool) : M Name := do
  let ok (n : Name) : M Bool := do
    return !(← get).used.contains n && (!hyp || (← resolveGlobalName n).isEmpty)
  let mut n := Name.mkSimple pref
  if !(← ok n) && hyp && !pref.startsWith "h" then n := Name.mkSimple s!"h_{pref}"
  let mut i := 2
  while !(← ok n) do
    n := Name.mkSimple s!"{pref}{i}"
    i := i + 1
  modify fun s => { s with used := s.used.insert n }
  return n

def hname (n : Name) (dflt : String) : String :=
  if n.hasMacroScopes || n.isAnonymous || n == `self then dflt else
    n.toString (escape := false)

/-- A binder of the new statement; `k` gets it and its name. -/
def bind {α} (pref : String) (bi : BinderInfo) (d : Expr) (k : Expr → String → M α) : M α := do
  let n ← pick pref (← isProp d)
  withLocalDecl n bi d fun x => do
    modify fun s => { s with vars := s.vars.push x }
    k x n.toString

/-- A hypothesis kept whole. -/
def leaf {α} (nm : String) (d : Expr) (k : String → M α) : M α := do
  let d ← unfoldContract d
  bind nm .default d fun _ n => k n

mutual
/-- Expand a hypothesis `nm : d` (`nested`: a field of an expanded one); `k` gets the term that
rebuilds it from the new hypotheses. -/
partial def hyp {α} (nm : String) (nested : Bool) (d : Expr) (k : String → M α) : M α := do
  let env ← getEnv
  let d ← instantiateMVars d
  let .const c lvls := d.getAppFn | leaf nm d k
  if expandable env c then
    let ctor := getStructureCtor env c
    let ty ← instantiateForall (← inferType (.const ctor.name lvls)) d.getAppArgs[:ctor.numParams]
    fields nm nested ty #[] fun txts => k s!"⟨{", ".intercalate txts.toList}⟩"
  else if c == `Tom.Machine.Bundle && d.getAppNumArgs == 4 then
    bundle nm d k
  else if ← unfoldable c then
    match ← delta1? d with
    | some d' => hyp nm nested d'.headBeta k
    | none => leaf nm d k
  else leaf nm d k

partial def fields {α} (nm : String) (nested : Bool) (ty : Expr) (acc : Array String)
    (k : Array String → M α) : M α := do
  match ty with
  | .forallE fn d b _ =>
    if b.hasLooseBVars then throwError "dependent field {fn}"
    let f := hname fn "h"
    -- a parent structure's fields are flattened into this one's
    let (child, nest) :=
      if f.startsWith "to" then (nm, nested) else (if nested then s!"{nm}_{f}" else f, true)
    hyp child nest d fun t => fields nm nested b (acc.push t) k
  | _ => k acc

/-- `Bundle ρ κ m` over an enumeration of regions: one witness hypothesis per region. -/
partial def bundle {α} (nm : String) (d : Expr) (k : String → M α) : M α := do
  let args := d.getAppArgs
  let (ι, ρ, κ, m) := (args[0]!, args[1]!, args[2]!, args[3]!)
  let ι ← whnf ι
  let .const I _ := ι.getAppFn | leaf nm d k
  let some (.inductInfo ind) := (← getEnv).find? I | leaf nm d k
  if ind.numParams != 0 || ind.numIndices != 0 then return ← leaf nm d k
  for c in ind.ctors do
    unless (← inferType (.const c [])) == ι do return ← leaf nm d k
  let lay := ρ.getAppFn.constName?.getD .anonymous
  let kd := κ.getAppFn.constName?.getD .anonymous
  let red (e : Expr) : MetaM Expr := do
    let e ← deltaExpand e fun x => x == lay || x == kd || x == `Tom.Machine.Kind.Wit ||
      x == `Tom.Machine.Kind.Fits
    simpReduce e
  -- per region: the fits fact (or its proof when trivial), then the witness
  let mut goals : Array (Name × Expr × Option String) := #[]
  for c in ind.ctors do
    let r := Expr.const c []
    let fits ← red (mkApp2 (.const `Tom.Machine.Kind.Fits []) (κ.beta #[r]) (ρ.beta #[r]))
    let wit ← red (mkApp3 (.const `Tom.Machine.Kind.Wit []) (κ.beta #[r]) (ρ.beta #[r]) m)
    let triv ← if fits.isConstOf ``True then pure (some "trivial")
      else if fits.isAppOfArity `Tom.Machine.Iv.Sub 2 then do
        if ← isDefEq fits.appFn!.appArg! fits.appArg! then pure (some "Iv.sub_self _")
        else pure none
      else pure none
    goals := goals.push (c, fits, triv)
    goals := goals.push (c, wit, none)
  let rec go (i : Nat) (alts : Array String) (cur : String) : M α := do
    if h : i < goals.size then
      let (c, e, triv) := goals[i]
      if i % 2 == 0 then
        match triv with
        | some t => go (i + 1) alts t
        | none => leaf s!"fits_{short c}" e fun n => go (i + 1) alts n
      else
        leaf s!"w_{short c}" e fun n =>
          go (i + 1) (alts.push s!"| .{short c} => ⟨{cur}, {n}⟩") ""
    else
      k s!"(fun r => match r with {" ".intercalate alts.toList})"
  go 0 #[] ""
end

/-- A name for an anonymous hypothesis, from its head: `sound`, `heap`, `off`, `ra_al`, ... -/
def hypName (d : Expr) : String :=
  let b := d.getForallBody
  match b.getAppFn with
  | .const c _ =>
    if c == ``Eq && (b.getArg! 1).isAppOf ``HMod.hMod && ((b.getArg! 1).getArg! 4).isAppOf ``BitVec.toNat
    then "ra_al"
    else if [``Eq, ``LT.lt, ``LE.le, ``Ne, ``Not, ``And, ``Or, ``Iff, ``Exists, ``Membership.mem,
      ``True, ``False].contains c then "h"
    else
      let s := short c
      if s == "AHeap" then "heap" else s.decapitalize
  | _ => "h"

/-- The telescope of a contract: binders kept, hypotheses expanded; `k` gets the argument texts. -/
partial def tele {α} (e : Expr) (acc : Array String) (k : Array String → Expr → M α) : M α := do
  let e ← whnfCore e
  match e with
  | .forallE n d b bi =>
    if (← isProp d) then
      if b.hasLooseBVars then throwError "dependent hypothesis {n}"
      hyp (hname n (hypName d)) false d fun t => tele b (acc.push t) k
    else
      bind (hname n "x") bi d fun v x => tele (b.instantiate1 v) (acc.push x) k
  | _ =>
    let .const c _ := e.getAppFn | k acc e
    let wrapper := (short c).endsWith "Statement" || (short c).startsWith "Spec"
    if (← unfoldable c) || (wrapper && (← getEnv).find? c matches some (.defnInfo _)) then
      match ← delta1? e with
      | some e' => tele e'.headBeta acc k
      | none => k acc e
    else k acc e

def ppOpts (o : Options) : Options :=
  o |>.set `format.width (92 : Nat) |>.set `pp.fullNames false |>.set `pp.universes false
    |>.set `pp.funBinderTypes false |>.set `pp.mvars false

/-- Does `s` elaborate, here, to a term defeq to `e`? -/
def roundTrips (s : String) (e : Expr) : TermElabM Bool := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term s | return false
  try
    let saved ← saveState
    let ok ← (do
      let e' ← elabTerm stx none
      synthesizeSyntheticMVarsNoPostponing
      let e' ← instantiateMVars e'
      if e'.hasExprMVar then return false
      withTransparency .default (isDefEq e' e))
    saved.restore
    return ok
  catch _ => return false

/-- `e` pretty printed so that it reads back as itself: plainly if that works, else with the
annotations of `pp.analyze`, else fully explicit. -/
def ppBack (e : Expr) : TermElabM String := do
  for extra in [fun (o : Options) => o, fun o => o.set `pp.analyze true,
                fun o => (o.set `pp.analyze true).set `pp.structureInstances false,
                fun o => o.set `pp.explicit true] do
    let s := toString (← withOptions (fun o => extra (ppOpts o)) (ppExpr e))
    if ← roundTrips s e then return s
  throwError "no faithful print of {e}"

def run (name : Name) (stmt : Expr) (proof : String) (hasStmt : Bool) : TermElabM Unit := do
  let j ← (tele stmt #[] fun args body => do
    let body ← unfoldContract body
    let mut bs : Array Json := #[]
    for v in (← get).vars do
      let ld ← v.fvarId!.getDecl
      let ty ← ppBack ld.type
      let bi := match ld.binderInfo with
        | .implicit => "{" | .strictImplicit => "⦃" | .instImplicit => "[" | _ => "("
      bs := bs.push (Json.arr #[toJson bi, toJson ld.userName.toString, toJson ty,
        toJson (← isProp ld.type)])
    let concl ← ppBack body
    return Json.mkObj [("name", toString name), ("binders", Json.arr bs),
      ("concl", concl), ("args", toJson args), ("hasStmt", toJson hasStmt),
      ("proof", proof)]).run' {}
  IO.println j.compress

end SpecsPP

open SpecsPP in
elab "#spec_pp " n:ident " : " s:term " := " p:term : command => liftTermElabM do
  let st ← elabTerm s none
  synthesizeSyntheticMVarsNoPostponing
  run n.getId (← instantiateMVars st) (toString (p.raw.reprint.getD "").trimAscii) true

open SpecsPP in
elab "#spec_pp_thm " n:ident " := " p:ident : command => liftTermElabM do
  let c ← realizeGlobalConstNoOverload p
  run n.getId (← getConstInfo c).type (toString c) false
