import Tom.Machine.Kit.Run

/-!
# A callee's residue from the caller's

`res_from [defs] h`: the goal is a callee's residue structure (`SqrAlg.Base …`, `SqrFastRes …`);
`h` the caller's. Every field of `h` (and of its structure fields, `h.stk.lo` …) is put in context,
then each field of the goal is closed by one of: a field of `h` (`assumption`), a field applied or
weakened (`solve_by_elim` with `MpInt.Valid.toShape`), arithmetic after unfolding `defs` (the
callee's and caller's stack depths, `heapEnd`), a stack residue's three bounds the same way, or
`OffHeap` by `omega`. It replaces the per-function residue lemmas of `Fn/MpSqrG5K.lean` and
`Fn/MpMulG5K.lean` (`algBase`, `fastRes`: field by field, the same names and arithmetic each time).
-/

namespace Tom.Machine

open Lean Elab Tactic Meta

/-- Every field of `h` (two levels of structures) as a hypothesis. -/
partial def resFields (e : Expr) (depth : Nat) : TacticM Unit := withMainContext do
  if depth = 0 then return
  let ty ← whnfR (← inferType e)
  let some sn := ty.getAppFn.constName? | return
  let env ← getEnv
  unless isStructure env sn do return
  for f in getStructureFieldsFlattened env sn (includeSubobjectFields := false) do
    let some pr ← (try some <$> mkProjection e f catch _ => pure none) | continue
    let pty ← inferType pr
    unless ← isProp pty do continue
    liftMetaTactic fun g => do
      let g ← g.assert (`res_ ++ f) pty pr
      let (_, g) ← g.intro1P
      return [g]
    resFields pr (depth - 1)

elab "res_fields " h:term : tactic => withMainContext do
  let e ← Term.elabTerm h none
  resFields e 2

macro "res_from " "[" ls:Lean.Parser.Tactic.simpLemma,* "] " h:term : tactic =>
  `(tactic| (
    res_fields $h
    constructor <;> (try dsimp only) <;> first
      | assumption
      | (solve_by_elim (maxDepth := 3) [Tom.MpInt.Valid.toShape])
      | ((try simp only [$ls,*] at *) <;> (try dsimp only) <;> omega)
      | (constructor <;> (try simp only [$ls,*] at *) <;> (try dsimp only) <;> omega)
      | (unfold Tom.Machine.Api.Heap.OffHeap; omega)))

end Tom.Machine
