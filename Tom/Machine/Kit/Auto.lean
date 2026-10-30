import Tom.Machine.Kit.Arith
import Tom.Machine.Kit.Mem

/-!
# Closing a segment's leaves and register equations

`leaf_auto [defs] [eqs]` closes one data-dependent leaf `tom_facts` leaves:
it normalises the leaf (`leaf_nf [defs]`), rewrites loaded values by the
caller's equations `eqs` (`bytesT4 m a = …`, `signExtend … = …`), then tries,
in order, a load (`Ram` bounds by `omega`, the byte pins by `lpins*_rd*_of`),
a store (`StoreWin` by `omega`), a `ret` (`ret_target` with the context's
`ra` alignment) and a branch guard (the compare lemmas of `Kit/Arith.lean`,
side conditions by `omega`, then `omega`). Code-frame leaves go to
`code_frame [defs]` first. The context must hold the `Ram` bounds as plain
inequalities (`ram_bounds`) and `hra : ra.toNat % 4 = 0`.

`regs_auto [defs] [eqs]` closes `seg_at`'s `hregs`/`hlog`: `seg_nf`, the
loaded values by `eqs`, then `regs_close`.
-/

namespace Tom.Machine

/-- `Ram` as plain bounds, for `omega`. -/
theorem ram_bounds {lo len : Nat} (h : Ram lo len) :
    0x80000000 ≤ lo ∧ lo + len ≤ 0x100000000 ∧ (lo + len + 8 ≤ 0x80018880 ∨ 0x80018890 ≤ lo) :=
  ⟨h.lo_ge, h.hi_le, h.off⟩

/-- The register-value normal form after `seg_nfo`: loaded values by the
caller's equations `eqs`, then 32/64-bit arithmetic on `ofNat`, side conditions
by `omega` (`val_nf [eqs]`). -/
syntax "val_nf" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| val_nf [$es,*]) => `(tactic|
     (try simp only [Tom.Machine.rd4_bytes, Tom.Machine.rd4_bytesD, Tom.Machine.rd8_bytes,
        Tom.Machine.rd8_bytesD, Tom.Machine.rd8_bytesD']
      try simp only [$es,*]
      try simp (disch := omega) only [Vsa.Sim.shamt5Of, BitVec.reduceExtractLsb',
        Tom.Machine.signExtend_ofNat32, Tom.Machine.signExtend_ofNat32', Tom.Machine.signExtend_ofNatW,
        Tom.Machine.extractLsb_ofNat32', Tom.Machine.sext_and_mask28W, Tom.Machine.extractLsb_sextW,
        Tom.Machine.ofNat_add_ofNat, Tom.Machine.ofNat_add_ofNatW, Tom.Machine.and_mask28,
        Tom.Machine.srl32_ofNat, Tom.Machine.srl32_ofNat', Tom.Machine.srl32_ofNatW, Tom.Machine.srl64_ofNat,
        Tom.Machine.shl_ofNat', Tom.Machine.ofNat_sub_ofNatW, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd,
        Tom.Machine.toNat_ofNat_add, Tom.Machine.toNat_ofNat']))

syntax "leaf_auto" " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| leaf_auto [$ds,*] [$es,*]) => `(tactic|
      first
      | (code_frame [$ds,*]; done)
      | (leaf_nf [$ds,*]
         try simp only [Tom.Machine.rd4_bytesD, Tom.Machine.rd8_bytesD, Tom.Machine.rd4_bytes,
           Tom.Machine.rd8_bytes, Tom.Machine.rd8_bytesD']
         try simp only [$es,*]
         try simp only [Tom.Machine.ofNat_add_ofNat, Tom.Machine.toNat_ofNat_add, Tom.Machine.toNat_ofNat']
         -- an equation in `eqs` may close the leaf outright (a branch guard on a symbolic value)
         all_goals first
         | (simp only [Vsa.Sim.tohostAddr]
            first
            | (refine ⟨⟨by omega, by omega, by omega⟩, Tom.Machine.lpins4_rd4_frame (by omega) ?_⟩
               code_frame [$ds,*])
            | (refine ⟨⟨by omega, by omega, by omega⟩, Tom.Machine.lpins8_rd8_frame (by omega) ?_⟩
               code_frame [$ds,*]))
         | (simp only [Vsa.Sim.StoreWin, Vsa.Sim.tohostAddr]; omega)
         | (rw [Tom.Machine.ret_target _ (by assumption)]; assumption)
         | (rw [Tom.Machine.ret_target' _ (by assumption)]; assumption)
         | (try val_nf [$es,*]
            all_goals simp (disch := omega) only [Tom.Machine.ofNat_add_ofNat, Tom.Machine.blt_ofNat,
              Tom.Machine.bltu_ofNat', Tom.Machine.bgeu_ofNat', Tom.Machine.bge_zero_ofNat, Tom.Machine.bge_ofNat, Tom.Machine.bge_zero_sextW,
              Tom.Machine.ofNat_beq', bne, decide_eq_true_eq, decide_eq_false_iff_not,
              Bool.not_eq_true', Bool.not_eq_false', beq_self_eq_true, Bool.not_true]
            all_goals omega)))

syntax "regs_auto" " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| regs_auto [$ds,*] [$es,*]) => `(tactic|
      (seg_nf [$ds,*]
       try simp only [Tom.Machine.rd4_bytesD, Tom.Machine.rd8_bytesD, Tom.Machine.rd4_bytes,
         Tom.Machine.rd8_bytes, $es,*]
       try regs_close))

/-- Close `seg_at'`'s `hsub` (`sub_auto [chain, defs] [eqs]`): the lookups by
`seg_nfo`, the values by `val_nf`, each equation by `regs_close`. -/
syntax "sub_auto" " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| sub_auto [$ds,*] [$es,*]) => `(tactic|
      (try simp only [$ds,*]
       simp only [Tom.Machine.SubL]
       seg_nfo [$ds,*]
       try simp only [Option.some.injEq]
       try val_nf [$es,*]
       try regs_close))

/-- One segment, end to end (`seg_step chain pc lds ks kk [defs] [post] [eqs] hc`):
`seg_at'` with the load data `lds` and key lists `ks`/`kk`; the leaves by
`tom_facts hc` + `leaf_auto [defs] [eqs]`; the end PC by `seg_nfo`; the post
registers (`SubL`, unfolding `post`) by `sub_auto`; the write log by
`val_nf` + `regs_close`. `defs` unfold the entry register list, `post` the
target's. -/
syntax "seg_step " term:max ppSpace term:max ppSpace term:max ppSpace term:max ppSpace term:max
  " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" ppSpace term:max : tactic
macro_rules
  | `(tactic| seg_step $bs $pc $lds $ks $kk [$ds,*] [$ps,*] [$es,*] $hc) => do
      let b ← `(Lean.Parser.Tactic.simpLemma| $bs:term)
      let l1 : Array (Lean.TSyntax ``Lean.Parser.Tactic.simpLemma) := #[b] ++ ds.getElems
      let l2 := l1 ++ ps.getElems
      `(tactic|
        (refine Tom.Machine.seg_at' $bs (pc1 := $pc) $lds $ks $kk ?_ ?_ ?_ ?_
         · tom_facts $hc
           all_goals leaf_auto [$ds,*] [$es,*]
         · seg_nfo [$l1,*]
           try (try val_nf [$es,*]
                exact Tom.Machine.ret_target' _ (by assumption))
         · sub_auto [$l2,*] [$es,*]
         · seg_nfo [$l1,*]
           try val_nf [$es,*]
           try regs_close))

/-- `[lo, lo + n)` and `[lo', lo' + n')` are disjoint. `facts_ctx` never adds
these (a disjunction each: `omega` splits them all, exponentially); bring the
ones a proof needs by name. -/
def Disj (lo n lo' n' : Nat) : Prop := lo + n ≤ lo' ∨ lo' + n' ≤ lo

open Lean Elab Tactic Meta in
/-- The `have`s `facts_ctx` adds for the proof term `e : ty` (a structure in
`Prop`), recursing into structure-valued fields up to depth `d`. -/
private partial def factsOf (env : Environment) (e : Expr) (ty : Expr) (d : Nat) :
    TacticM (Array Expr) := do
  let some sn := ty.getAppFn.constName? | return #[]
  unless isStructure env sn do return #[]
  if sn == ``Tom.Machine.Ram then
    return #[← mkAppM ``Tom.Machine.ram_bounds #[e]]
  let mut out := #[]
  for f in getStructureFields env sn do
    let e? : Option Expr ← try
        let e' ← mkAppM (sn ++ f) #[e]
        pure (some e')
      catch _ => pure none
    let some e' := e? | continue
    let fty ← instantiateMVars (← inferType e')
    unless (← isProp fty) do continue
    let fsn := fty.getAppFn.constName?.getD .anonymous
    if isStructure env fsn then
      if d > 0 then out := out ++ (← factsOf env e' fty (d - 1))
    else if fsn != ``Tom.Machine.Disj &&
        !(fty.find? (fun x => x.isConstOf ``BitVec || x.isConstOf ``Std.ExtHashMap)).isSome then
      out := out.push e'
  return out

open Lean Elab Tactic Meta in
/-- Put the facts of every structure hypothesis in context for `omega` and the
leaf closers (`facts_ctx`): a `Ram lo len` (field) becomes its three bounds
(`ram_bounds`), any other arithmetic `Prop` field becomes a hypothesis,
recursing into structure fields (three levels). Fields about memory or BitVec
values are not added (every `simp … at *` would rewrite them); pass those to
`leaf_auto`/`val_nf` by name. -/
elab "facts_ctx" : tactic => do
  let g ← getMainGoal
  let env ← getEnv
  let facts ← g.withContext do
    let mut acc := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless (← isProp ty) do continue
      acc := acc ++ (← factsOf env d.toExpr ty 3)
    pure acc
  let mut g := g
  for e in facts do
    let (_, g') ← (← g.assert `this (← g.withContext (inferType e)) e).intro1P
    g := g'
  replaceMainGoal [g]

end Tom.Machine
