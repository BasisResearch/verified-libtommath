import Tom.Machine.Kit.MeetHeap
import Tom.Machine.Kit.Gen
import Tom.Machine.Kit.MulCall

/-!
# The meet, one control rule over `St`/`At` cuts, plus the pieces a
generated assembly needs

Stated over Meet's existing terms (`St`, `HP`, `At`, `Triple`); no new state datatype.
The function assemblies `Fn/*MainG.lean` are written by `scripts/gen_asm.py` from a
per-function annotation (`experiments/asm/<f>.asm.json`).

* **Cuts** (`Lbl`): a cut is a type of parameters `X` (the memory, the cut's variables),
  a measure `μ : X → ℕ³` (lexicographic, `Lt3`) and a body `B x cf` (a generated named
  structure: `St`, the heap checkpoint, `At pc L`, the value premise).
* **`run`**: if every cut's edges reach the post `Q` or a cut of smaller measure, every
  cut reaches `Q`. Loop exits are ordinary edges; a back edge is an edge to a cut of
  smaller measure (`n − i` in the last component, the outer loop's in the first).
* **`St.seqWs`**: a segment whose stores fall in several own-frame regions (`frz`): each
  snapshot takes the whole log (`Kind.logs`).
* **`call_mul`**: `jal __muldi3` inside a loop body, where the callee-saved registers are
  not all pinned (the rule keeps the caller's pinned `s`-registers).
* **`cfacts h`**: `facts h` per leaf, then the reads of a snapshot that is a cut variable
  (`St.frz` + `load_fwd` over the premise) and digit bounds from the premise's `∀ j < n`.
-/

namespace Tom.Machine

open Vsa.Sim Vsa.Logic

/-! ## The control rule -/

/-- Lexicographic order on `ℕ³`. -/
def Lt3 (a b : Nat × Nat × Nat) : Prop :=
  a.1 < b.1 ∨ a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)

theorem lt3_wf : WellFounded Lt3 := by
  have h : WellFounded (Prod.Lex (α := Nat) (β := Nat × Nat) (· < ·) (Prod.Lex (· < ·) (· < ·))) :=
    (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf
  refine Subrelation.wf (fun {a b} hab => ?_) h
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp only [Lt3] at hab
  rcases hab with h1 | ⟨rfl, h2 | ⟨rfl, h3⟩⟩
  · exact Prod.Lex.left _ _ h1
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ h2)
  · exact Prod.Lex.right _ (Prod.Lex.right _ h3)

/-- A cut: its parameters, measure, premise (the state: `St`, the heap checkpoint, the
value premise; a generated named structure) and machine state (`At pc L M K o`). -/
structure Lbl where
  X : Type
  μ : X → Nat × Nat × Nat
  P : X → Prop
  A : X → Vsa.Machine.Config → Prop

def Lbl.B (L : Lbl) (x : L.X) (cf : Vsa.Machine.Config) : Prop := L.P x ∧ L.A x cf

/-- What an edge from a cut reaches: the post, or another cut of smaller measure. -/
def Lbl.Next {Λ : Type} (L : Λ → Lbl) (Q : Vsa.Machine.Config → Prop) (n : Nat × Nat × Nat)
    (cf : Vsa.Machine.Config) : Prop :=
  Q cf ∨ ∃ l x, Lt3 ((L l).μ x) n ∧ (L l).B x cf

/-- The edges of a cut. -/
def Lbl.Edge {Λ : Type} (L : Λ → Lbl) (Q : Vsa.Machine.Config → Prop) (l : Λ) (x : (L l).X) : Prop :=
  Triple ((L l).B x) (Lbl.Next L Q ((L l).μ x))

/-- **The control rule.** -/
theorem run {Λ : Type} (L : Λ → Lbl) (Q : Vsa.Machine.Config → Prop)
    (edge : ∀ l x, Lbl.Edge L Q l x) : ∀ l x, Triple ((L l).B x) Q := by
  suffices h : ∀ n l x, (L l).μ x = n → Triple ((L l).B x) Q from fun l x => h _ l x rfl
  intro n
  induction n using lt3_wf.induction with
  | _ n ih =>
    intro l x hn c hc
    obtain ⟨c1, hs1, hq⟩ := edge l x c hc
    rcases hq with hq | ⟨l', x', hlt, hb⟩
    · exact ⟨c1, hs1, hq⟩
    · obtain ⟨c2, hs2, hq2⟩ := ih _ (hn ▸ hlt) l' x' rfl c1 hb
      exact ⟨c2, hs1.trans hs2, hq2⟩

/-- Enter a cut: its premise in context. -/
theorem Lbl.enter {L : Lbl} {x : L.X} {Q : Vsa.Machine.Config → Prop} (k : L.P x → Triple (L.A x) Q) :
    Triple (L.B x) Q := fun c hc => k hc.1 c hc.2

/-- Start at a cut. -/
theorem Lbl.start {L : Lbl} {x : L.X} {P Q : Vsa.Machine.Config → Prop} (h : Triple (L.B x) Q)
    (hp : L.P x) (ha : ∀ cf, P cf → L.A x cf) : Triple P Q := fun c hc => h c ⟨hp, ha c hc⟩

/-- An edge ends at a cut (zero steps). -/
theorem Lbl.jump {Λ : Type} {L : Λ → Lbl} {Q P : Vsa.Machine.Config → Prop} {n : Nat × Nat × Nat}
    (l : Λ) (x : (L l).X) (hlt : Lt3 ((L l).μ x) n) (hp : (L l).P x) (h : ∀ cf, P cf → (L l).A x cf) :
    Triple P (Lbl.Next L Q n) :=
  Triple.of_imp fun cf hc => Or.inr ⟨l, x, hlt, hp, h cf hc⟩

/-- An edge ends at the post. -/
theorem Lbl.exit {Λ : Type} {L : Λ → Lbl} {Q P : Vsa.Machine.Config → Prop} {n : Nat × Nat × Nat}
    (h : ∀ cf, P cf → Q cf) : Triple P (Lbl.Next L Q n) :=
  Triple.of_imp fun cf hc => Or.inl (h cf hc)

/-- An edge whose last triple reaches the post. -/
theorem Lbl.exitT {Λ : Type} {L : Λ → Lbl} {Q P R : Vsa.Machine.Config → Prop} {n : Nat × Nat × Nat}
    (h : Triple P R) (hr : ∀ cf, R cf → Q cf) : Triple P (Lbl.Next L Q n) :=
  Triple.rmap (fun cf hc => Or.inl (hr cf hc)) h

/-- `Lt3` on literal triples, by `omega`. -/
macro "lt3" : tactic => `(tactic| (simp only [Lt3]; omega))

/-! ## Stores into several own-frame regions -/

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}
  {pc pc' : BitVec 64} {L0 L L' K : GRegs} {o : Array String} {Q : Vsa.Machine.Config → Prop}

/-- A snapshot takes a write log. -/
def Kind.logK (log : List WEntry) : Kind → Kind
  | .frz m0 => .frz (writeLog m0 log)
  | k => k

def Kind.isFrz : Kind → Bool
  | .frz _ => true
  | _ => false

/-- Every snapshot of `rs` takes the log. -/
def Kind.logs (κ : ι → Kind) (rs : List ι) (log : List WEntry) : ι → Kind :=
  rs.foldr (fun r acc => Kind.set acc r ((κ r).logK log)) κ

theorem Kind.logs_eq (κ : ι → Kind) (log : List WEntry) (r : ι) :
    ∀ rs : List ι, Kind.logs κ rs log r = if r ∈ rs then (κ r).logK log else κ r
  | [] => by simp [Kind.logs]
  | r' :: rs => by
    have ih := Kind.logs_eq κ log r rs
    simp only [Kind.logs, List.foldr_cons, Kind.set] at ih ⊢
    by_cases h : r = r'
    · subst h; simp
    · rw [if_neg h, ih]; simp [h]

/-- Some region of `rs` holds the entry. -/
def AnySub (ρ : ι → Iv) : List ι → Nat → Nat → Prop
  | [], _, _ => False
  | r :: rs, a, n => Iv.Sub ⟨a, n⟩ (ρ r) ∨ AnySub ρ rs a n

/-- Every entry of the log lies in some region of `rs`. -/
def LogInAny (ρ : ι → Iv) (rs : List ι) : List WEntry → Prop
  | [] => True
  | e :: l => AnySub ρ rs e.1 e.2.1 ∧ LogInAny ρ rs l

theorem AnySub.exists : ∀ {rs : List ι} {a n : Nat}, AnySub ρ rs a n → ∃ r ∈ rs, Iv.Sub ⟨a, n⟩ (ρ r)
  | [], _, _, h => h.elim
  | _ :: _, _, _, Or.inl h => ⟨_, List.mem_cons_self .., h⟩
  | _ :: _, _, _, Or.inr h => let ⟨r, hr, hs⟩ := AnySub.exists h; ⟨r, List.mem_cons_of_mem _ hr, hs⟩

theorem Frm.storeAny {rs : List ι} : ∀ {log : List WEntry}, LogInAny ρ rs log → Frm ρ rs M (writeLog M log)
  | log, h => fun x hx => writeLog_out _ _ _ (by
      induction log with
      | nil => trivial
      | cons e l ih =>
        refine ⟨?_, ih h.2⟩
        obtain ⟨r, hr, hs⟩ := h.1.exists
        have : ¬ (ρ r).In x := fun hi => hx (InAny.of_mem hr hi)
        unfold Iv.Sub Iv.In at *; simp only at hs; omega)

/-- **Stores into own-frame regions** `rs`: each snapshot takes the log. -/
theorem St.storeWs (h : St ρ isW W κ m M) (rs : List ι) {log : List WEntry} (hlog : LogInAny ρ rs log)
    (hk : (rs.all fun r => (κ r).isFrz) = true) (hw : rs.all isW = true) (hW : SubN rs W = true) :
    St ρ isW W (Kind.logs κ rs log) m (writeLog M log) :=
  h.step (Frm.storeAny hlog) hw hW
    (fun r hr => by
      rw [Kind.logs_eq, if_pos hr]
      have hf := List.all_eq_true.1 hk r hr
      have hw0 := h.wit r
      revert hf hw0
      cases κ r with
      | frz m0 =>
        intro _ hw0
        simp only [Kind.logK, Kind.Fits, Kind.Wit, true_and] at hw0 ⊢
        exact ⟨hw0.1, fun x hx => writeLog_congr_at log (hw0.2 x hx)⟩
      | _ => intro hf; simp [Kind.isFrz] at hf)
    (fun r hr => by rw [Kind.logs_eq, if_neg hr])

end

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}

/-- A byte of a snapshot region (`frz`). -/
theorem St.frz1 (h : St ρ isW W κ m M) (r : ι) {m0 : Mem} (hk : κ r = .frz m0) {a : Nat}
    (hs : Iv.Sub ⟨a, 1⟩ (ρ r)) : bytesT1 M a = bytesT1 m0 a := by
  have hw := (h.wit r).2; rw [hk] at hw
  simp only [bytesT1]; rw [hw.2 a ⟨hs.1, by have := hs.2; simp only at this; omega⟩]

theorem St.frz1_fwd (h : St ρ isW W κ m M) (r : ι) {m0 : Mem} (hk : κ r = .frz m0) {a : Nat} {v : BitVec 8}
    (hs : Iv.Sub ⟨a, 1⟩ (ρ r)) (hv : bytesT1 m0 a = v) : bytesT1 M a = v := (h.frz1 r hk hs).trans hv

/-- A word of a snapshot region (`frz`). -/
theorem St.frz4 (h : St ρ isW W κ m M) (r : ι) {m0 : Mem} (hk : κ r = .frz m0) {a : Nat}
    (hs : Iv.Sub ⟨a, 4⟩ (ρ r)) : bytesT4 M a = bytesT4 m0 a := by
  have hw := (h.wit r).2; rw [hk] at hw
  exact bytesT4_congr fun x h1 h2 => hw.2 x ⟨by have := hs.1; simp only at this; omega,
    by have := hs.2; simp only at this; omega⟩

end

/-- A digit array's first word read at its base `dp` (not `dp + 4 * 0`: a callee's one-word out
slot, `mp_div_d`'s `*d`). -/
theorem Dig.arr0 {M : Mem} {dp n : Nat} {f : Nat → Nat} (d : Dig M dp n f) (hn : 0 < n) :
    bytesT4 M dp = BitVec.ofNat 32 (f 0) := by
  have h := d.arr 0 hn; rwa [Nat.mul_zero, Nat.add_zero] at h

/-- A region off the allocator is nonempty or outside the arena (the generated entry's
`pos3` for a contract region, possibly empty, from its `Off`). -/
theorem Off.pos {I : Iv} {H : List (Nat × Nat)} (h : Off I H) :
    0 < I.len ∨ I.base < Api.Alloc.heapStart ∨ Api.Alloc.heapEnd ≤ I.base := by
  rcases Nat.eq_zero_or_pos I.len with h0 | h0
  · exact .inr (h.edge h0)
  · exact .inl h0

/-- Two regions' disjointness, normalised to arithmetic and kept out of `omega`'s sight. -/
structure DisjH (P : Prop) : Prop where
  h : P

/-- A RAM fact kept out of `assumption`'s sight (`Ram (sp - 160) 160` against `Ram pa 24`
unfolds `Nat.sub` literal by literal); `cfacts` uses it for sub-ranges. -/
structure RamH (a n : Nat) : Prop where
  r : Ram a n

section Tac
open Lean Meta Elab Tactic

/-- One entry in some region (`iv_omega` per candidate). -/
syntax "any_sub" : tactic
macro_rules | `(tactic| any_sub) => `(tactic| first | exact Or.inl (by iv_omega) | exact Or.inr (by any_sub))

/-- `LogInAny ρ rs log` with a literal log. -/
elab "loginany" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let tgt ← whnfR tgt
  let_expr Tom.Machine.LogInAny ι ρ rs L := tgt | throwError "loginany: not a LogInAny goal {tgt}"
  let es ← listSpine L
  let lit ← mkListLit (mkConst ``Vsa.Sim.WEntry) es
  let g ← (← getMainGoal).replaceTargetDefEq (mkApp4 (mkConst ``Tom.Machine.LogInAny) ι ρ rs lit)
  replaceMainGoal [g]
  evalTactic (← `(tactic| simp only [Tom.Machine.LogInAny, Tom.Machine.AnySub, and_true]))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | any_sub)))

/-- Keep a tactic's effect if it does not fail. -/
def tryKeep (t : TacticM Unit) : TacticM Unit := do
  let s ← saveState
  try t catch _ => s.restore

/-- A read by a `∀ j, j ≤ n → ∀ x, x = b + j → read m x = v j` in context (a string's bytes, a
table of the image given its `Img`). -/
def fwdAll (img : Option Term := none) (pre : Option Term := none) : TacticM Unit := withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    unless (← instantiateMVars d.type).isForall do continue
    let ds ← Term.exprToSyntax d.toExpr
    let ok ← match img with
      | none => match pre with
        | none => tryTac (evalTactic (← `(tactic| exact $ds _ (by omega) _ (by omega))))
        | some q => tryTac (evalTactic (← `(tactic| exact ($q).trans ($ds _ (by omega) _ (by omega)))))
      | some i => do
        if ← tryTac (evalTactic (← `(tactic| exact $ds _ $i))) then pure true
        else tryTac (evalTactic (← `(tactic| exact $ds _ $i _ (by omega) _ (by omega))))
    if ok then return
  throwError "fwdAll: no fact"

/-- An address `a + k` / `a - k` (literals `k`, nested) as its atom `a` and its steps (`true`: an
addition). -/
partial def linShape? (e : Expr) : Option (Expr × List (Bool × Nat)) :=
  let lit (k : Expr) : Option Nat := k.nat? <|> k.rawNatLit?
  if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HSub.hSub 6 then
    match lit (e.getArg! 5) with
    | some k => (linShape? (e.getArg! 4)).map fun (a, o) => (a, o ++ [(e.isAppOfArity ``HAdd.hAdd 6, k)])
    | none => none
  else some (e, [])

/-- **Facts from the state**: a segment's fact record,
field by field, each leaf by a projection of a kind at an address (struct fields,
digits, the own frame's snapshot read through its write log or, for a snapshot that
is a cut variable, through the premise's facts by `load_fwd`), the RAM of a region,
the disjointness of two regions, or arithmetic over the kinds' alignment facts. Every
address is matched syntactically before a projection is tried (unifying `pa` with
`sp - 160` at default transparency unfolds `Nat.sub` literal by literal). -/
partial def cfactsCore (h ρ : Expr) (names : List Expr) (kinds : List (Expr × Expr)) (fuel : Nat) :
    TacticM Unit := withMainContext do
  if fuel = 0 then throwError "cfacts: out of fuel"
  let tgt0 ← instantiateMVars (← getMainTarget)
  let tgt ← whnfR tgt0
  if let some n := tgt.getAppFn.constName? then
    if isStructure (← getEnv) n && n != ``Ram then
      let gs ← (← getMainGoal).constructor
      for g in gs do
        setGoals [g]
        cfactsCore h ρ names kinds (fuel - 1)
      setGoals []
      return
  let hs ← Term.exprToSyntax h
  if tgt.isAppOf ``Ram then
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      if (← instantiateMVars d.type).isAppOf ``RamH then
        let ds ← Term.exprToSyntax d.toExpr
        if ← tryTac (evalTactic (← `(tactic| exact Ram.sub ($ds).r (by omega) (by omega)))) then return
    for (r, _) in kinds do
      let rs ← Term.exprToSyntax r
      if ← tryTac (evalTactic (← `(tactic| exact Ram.sub (St.ram $hs $rs) (by iv_omega) (by iv_omega)))) then return
    throwError "cfacts: cannot close {tgt}"
  if let some (_, lhs0, _) := tgt0.eq? then
    let lhs ← if (readOf? lhs0).isSome then pure lhs0 else whnfR lhs0
    if let some (w, _, x) := readOf? lhs then
      -- two addresses `a ± k` over one atom are compared by their spelling; an
      -- arithmetic equality of such addresses is the fast path below; others by `isDefEq`
      let same (y : Expr) : TacticM Bool := do
        match linShape? x, linShape? y with
        | some (a, sa), some (b, sb) =>
          if a == b && sa != sb then pure false else withReducible (isDefEq x y)
        | _, _ => withReducible (isDefEq x y)
      let addN (p : Expr) (k : Nat) : TacticM Expr := mkAppM ``HAdd.hAdd #[p, mkNatLit k]
      -- fast path: a struct field or a digit read at `a ± k` over the atom of the
      -- kind's base, spelled otherwise (`sp - 96` for the `sign` of a struct at `sp - 104`, `sp - 104`
      -- for the second word of an array at `sp - 108`): the offset decides the field, one `omega`
      -- the address. Before the region-by-region search, whose failing attempts (a snapshot's
      -- `iv_omega`, …) cost an edge near its budget the rest (r7a: `t.sign` timed out).
      if let some (ax, sx) := linShape? x then
        let offOf (l : List (Bool × Nat)) : Int := l.foldl (fun o (a, k) => if a then o + k else o - k) 0
        let xs ← Term.exprToSyntax x
        for (r, k) in kinds do
          let isS := k.isAppOf ``Kind.mpS
          unless isS || k.isAppOf ``Kind.mpD do continue
          let some (ab, sb) := linShape? (k.getArg! 0) | continue
          unless ab == ax && sb != sx do continue
          let d := offOf sx - offOf sb
          let rs ← Term.exprToSyntax r
          let ps ← Term.exprToSyntax (k.getArg! 0)
          if isS then
            let fld? : Option String := if w == 4 then (if d == 0 then some "used" else if d == 4 then some "alloc"
              else if d == 8 then some "sign" else none) else if w == 8 && d == 16 then some "dpv" else none
            let some fld := fld? | continue
            let offS : Term := Lean.quote d.toNat
            let fid := mkIdent (Name.mkStr ``Tom.Machine.Hdr fld)
            if ← tryTac (do
                evalTactic (← `(tactic| rw [show $xs = $ps + $offS by (try dsimp only); omega]))
                evalTactic (← `(tactic| exact $fid (St.hdr $hs $rs rfl)))) then return
          else if w == 4 && d ≥ 0 && d % 4 == 0 then
            let jS : Term := Lean.quote (d / 4).toNat
            if ← tryTac (do
                evalTactic (← `(tactic| rw [show $xs = $ps + 4 * $jS by (try dsimp only); omega]))
                evalTactic (← `(tactic| exact (St.dig $hs $rs rfl).arr $jS (by (try dsimp only); omega)))) then return
      for (r, k) in kinds do
        let rs ← Term.exprToSyntax r
        if k.isAppOf ``Kind.mpS then
          let p := k.getArg! 0
          if w == 4 then
            if ← same p then if ← tryTac (evalTactic (← `(tactic| exact (St.hdr $hs $rs rfl).used))) then return
            if ← same (← addN p 4) then if ← tryTac (evalTactic (← `(tactic| exact (St.hdr $hs $rs rfl).alloc))) then return
            if ← same (← addN p 8) then if ← tryTac (evalTactic (← `(tactic| exact (St.hdr $hs $rs rfl).sign))) then return
          if w == 8 then
            if ← same (← addN p 16) then if ← tryTac (evalTactic (← `(tactic| exact (St.hdr $hs $rs rfl).dpv))) then return
        if k.isAppOf ``Kind.mpD && w == 4 && x.isAppOf ``HAdd.hAdd then
          if ← withReducible (isDefEq (x.getArg! 4) (k.getArg! 0)) then
            if ← tryTac (evalTactic (← `(tactic| exact (St.dig $hs $rs rfl).arr _ (by omega)))) then return
            if ← tryTac (evalTactic (← `(tactic| exact ((St.dig $hs $rs rfl).arr _ (by omega)).trans
                (by simp only [ovl, Nat.lt_irrefl, if_false])))) then return
        -- a digit array's word at its base itself, spelled `dp` (a callee's one-word out slot at
        -- `sp - 108`)
        if k.isAppOf ``Kind.mpD && w == 4 then
          if ← same (k.getArg! 0) then
            if ← tryTac (evalTactic (← `(tactic| exact (St.dig $hs $rs rfl).arr0 (by omega)))) then return
        -- a one-word array at a literal address
        let natOf (e : Expr) : Option Nat := e.nat? <|> e.rawNatLit?
        if k.isAppOf ``Kind.mpD && w == 4 && (natOf x).isSome then
          if natOf (← whnfD (k.getArg! 0)) == natOf x then
            if ← tryTac (evalTactic (← `(tactic| exact (St.dig $hs $rs rfl).arr 0 (by decide)))) then return
        if k.isAppOf ``Kind.frz && (w == 8 || w == 1) then
          let ty ← mkAppM ``Iv.Sub #[← mkAppM ``Iv.mk #[x, mkNatLit w], mkApp ρ r]
          let mv ← mkFreshExprSyntheticOpaqueMVar ty
          let st ← saveState
          let ok ← try
              let gs ← Tactic.run mv.mvarId! (evalTactic (← `(tactic| iv_omega)))
              pure gs.isEmpty
            catch _ => pure false
          unless ok do st.restore; continue
          let pf ← Term.exprToSyntax (← instantiateMVars mv)
          if ← tryTac (do
              if w == 8 then evalTactic (← `(tactic| rw [St.frz $hs $rs rfl $pf]))
              else evalTactic (← `(tactic| rw [St.frz1 $hs $rs rfl $pf]))
              evalTactic (← `(tactic| first | rd_log | (load_fwd; rfl)))) then return
          if w == 1 then
            let s1 ← saveState
            try
              let pfE ← instantiateMVars mv
              let hk ← mkExpectedTypeHint (← mkEqRefl k) (← mkEq (mkApp (← whnfR (← inferType h)).getAppArgs[5]! r) k)
              let e ← mkAppM ``Tom.Machine.St.frz1 #[h, r, hk, pfE]
              let some (_, _, rhs) := (← inferType e).eq? | throwError "frz1"
              let some (_, _, v) := tgt0.eq? | throwError "frz1"
              let g2 ← mkFreshExprSyntheticOpaqueMVar (← mkEq rhs v)
              let prf ← mkEqTrans e g2
              (← getMainGoal).assign prf
              setGoals [g2.mvarId!]
              fwdAll
              return
            catch _ => s1.restore
        -- a word of a snapshot region: its snapshot's, by a fact about it
        if k.isAppOf ``Kind.frz && w == 4 then
          let ty ← mkAppM ``Iv.Sub #[← mkAppM ``Iv.mk #[x, mkNatLit 4], mkApp ρ r]
          let mv ← mkFreshExprSyntheticOpaqueMVar ty
          let st ← saveState
          let ok ← try
              let gs ← Tactic.run mv.mvarId! (evalTactic (← `(tactic| iv_omega)))
              pure gs.isEmpty
            catch _ => pure false
          unless ok do st.restore; continue
          let pf ← Term.exprToSyntax (← instantiateMVars mv)
          if ← tryTac (do
              evalTactic (← `(tactic| rw [St.frz4 $hs $rs rfl $pf]))
              evalTactic (← `(tactic| first | (load_fwd; rfl) | assumption))) then return
          st.restore
        if k.isAppOf ``Kind.code then
          if ← tryTac (fwdAll (some (← `(term| St.img $hs $rs)))) then return
      if ← tryTac (evalTactic (← `(tactic| rd_log))) then return
      -- a struct field at an address equal to the field's only by arithmetic (`sp - 40` for the
      -- `dp` of a struct at `sp - 56`, also through a projection `{ pa := sp - 56, … }.pa`)
      let xs ← Term.exprToSyntax x
      for (r, k) in kinds do
        unless k.isAppOf ``Kind.mpS do continue
        let rs ← Term.exprToSyntax r
        let ps ← Term.exprToSyntax (k.getArg! 0)
        let cands : List (Nat × String) :=
          if w == 4 then [(0, "used"), (4, "alloc"), (8, "sign")] else if w == 8 then [(16, "dpv")] else []
        for (off, fld) in cands do
          let offS : Term := Lean.quote off
          let fid := mkIdent (Name.mkStr ``Tom.Machine.Hdr fld)
          if ← tryTac (evalTactic (← `(tactic| (rw [show $xs = $ps + $offS by (try dsimp only); omega]; exact $fid (St.hdr $hs $rs rfl))))) then
            return
      throwError "cfacts: cannot close {tgt}"
  -- a disjointness: arithmetic, a hoisted pair (`DisjH`), else two regions' `Sep`
  if tgt.isAppOf ``Or then
    if ← tryTac (evalTactic (← `(tactic| omega))) then return
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      unless (← instantiateMVars d.type).isAppOf ``DisjH do continue
      let ds ← Term.exprToSyntax d.toExpr
      if ← tryTac (evalTactic (← `(tactic| (have := ($ds).h; omega)))) then return
    for (r, _) in kinds do
      for (t, _) in kinds do
        let rs ← Term.exprToSyntax r
        let ts ← Term.exprToSyntax t
        if ← tryTac (do
            evalTactic (← `(tactic| have $(mkIdent `hd):ident := St.disj $hs $rs $ts))
            withMainContext do
              let some ld := (← getLCtx).findFromUserName? `hd | throwError "no hd"
              ivNormAt (some ld.fvarId)
            withMainContext do
              let some ld := (← getLCtx).findFromUserName? `hd | throwError "no hd"
              ivNormAt (some ld.fvarId)
            evalTactic (← `(tactic| (iv_norm; omega)))) then return
    throwError "cfacts: cannot close {tgt}"
  -- arithmetic: `omega`, a digit bound from a `∀ j, j < n → f j < c` in context, the kinds' alignment
  if ← tryTac (evalTactic (← `(tactic| ((try dsimp only); omega)))) then return
  if tgt.isAppOf ``LT.lt then
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let n ← forallTelescopeReducing ty fun xs body => pure (if body.isAppOf ``LT.lt then xs.size else 0)
      let ds ← Term.exprToSyntax d.toExpr
      if n == 2 then
        if ← tryTac (evalTactic (← `(tactic| exact Nat.lt_of_lt_of_le ($ds _ (by omega)) (Nat.le_refl _)))) then return
      if n == 1 then
        if ← tryTac (evalTactic (← `(tactic| exact Nat.lt_of_lt_of_le ($ds _) (Nat.le_refl _)))) then return
  let s0 ← saveState
  for (r, k) in kinds do
    let rs ← Term.exprToSyntax r
    if k.isAppOf ``Kind.mpS then
      tryKeep (evalTactic (← `(tactic| have := (St.hdr $hs $rs rfl).geom.st_al)))
    if k.isAppOf ``Kind.mpD then
      tryKeep (evalTactic (← `(tactic| have := (St.dig $hs $rs rfl).al)))
      tryKeep (evalTactic (← `(tactic| have := (St.dig $hs $rs rfl).ram.hi_le)))
  if ← tryTac (evalTactic (← `(tactic| ((try dsimp only at *); omega)))) then return
  s0.restore
  throwError "cfacts: cannot close {tgt}"

/-- `disj_hoist n h r t`: `n : DisjH (…)`, the disjointness of regions `r`, `t` of the state `h`
in arithmetic (`St.disj`, normalised by `iv_norm`). -/
elab "disj_hoist " n:ident h:term:max r:term:max t:term:max : tactic => withMainContext do
  let hd := mkIdent `hdH
  evalTactic (← `(tactic| have $hd:ident := St.disj $h $r $t))
  for _ in [0, 1] do
    withMainContext do
      let some ld := (← getLCtx).findFromUserName? `hdH | throwError "disj_hoist"
      ivNormAt (some ld.fvarId)
  evalTactic (← `(tactic| have $n:ident := DisjH.mk $hd:ident))
  evalTactic (← `(tactic| clear $hd:ident))

elab "cfacts " h:term : tactic => withMainContext do
  let hE ← Term.elabTerm h none
  let hT ← whnfR (← instantiateMVars (← inferType hE))
  unless hT.isAppOf ``St do throwError "cfacts: expected a St hypothesis"
  let args := hT.getAppArgs
  let names ← regionNames args[0]!
  let kinds ← names.mapM fun r => do return (r, ← whnfD (mkApp args[5]! r))
  cfactsCore hE args[2]! names kinds 4

end Tac

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}
  {pc pc' : BitVec 64} {L0 L L' K : GRegs} {o : Array String} {Q : Vsa.Machine.Config → Prop}

/-- A segment that stores into the own-frame regions `rs`, then the rest. -/
theorem St.seqWs (h : St ρ isW W κ m M) (rs : List ι) {log : List WEntry}
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M log) K o))
    (k : ∀ M', St ρ isW W (Kind.logs κ rs log) m M' → Triple (At pc' L' M' K o) Q)
    (hlog : LogInAny ρ rs log := by loginany) (hk : (rs.all fun r => (κ r).isFrz) = true := by exact rfl)
    (hw : rs.all isW = true := by decide) (hW : SubN rs W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q :=
  (Triple.seq hseg (k _ (h.storeWs rs hlog hk hw hW))).pre hL

theorem mul_lt_2_56 {x y : Nat} (hx : x < 268435456) (hy : y < 268435456) : x * y < 2 ^ 56 :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (by omega)) (by decide)

/-- A segment storing an `mp_int`'s `sign` (`r` its struct). -/
theorem St.seqS {pc pc' : BitVec 64} {L0 L L' K : GRegs} {o : Array String} {Q : Vsa.Machine.Config → Prop}
    (h : St ρ isW W κ m M) (r : ι) {p dp s : Nat} {a : MpInt} (hk : κ r = .mpS p dp a)
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M [(p + 8, 4, BitVec.ofNat 64 s)]) K o)) (hs : s < 2 ^ 32)
    (k : ∀ M', St ρ isW W (Kind.set κ r (.mpS p dp { a with sign := s })) m M' → Triple (At pc' L' M' K o) Q)
    (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q :=
  h.seqH r hk hseg (fun hf => ⟨Iv.Sub.trans (J := ⟨p, 24⟩) ⟨by simp only; omega, by simp only; omega⟩ hf, trivial⟩)
    (fun e => e.setS s hs) k hw hW hL

/-- Re-state a digit array's kind by equal length and digits (after `mp_clamp`). -/
theorem St.reD (h : St ρ isW W κ m M) (r : ι) {dp n n' : Nat} {f f' : Nat → Nat} (hk : κ r = .mpD dp n f)
    (hn : n' = n) (hf : f' = f) : St ρ isW W (Kind.set κ r (.mpD dp n' f')) m M := by
  subst hn hf
  refine h.congrK fun r' => ?_
  unfold Kind.set; split
  · subst_vars; exact hk
  · rfl

/-- Re-state a region's kind by an equal one. -/
theorem St.reK (h : St ρ isW W κ m M) (r : ι) {k k' : Kind} (hk : κ r = k) (e : k' = k) :
    St ρ isW W (Kind.set κ r k') m M := by
  subst e
  refine h.congrK fun r' => ?_
  unfold Kind.set; split
  · next heq => rw [heq]; exact hk
  · rfl

theorem St.digEq (h : St ρ isW W κ m M) (r : ι) {dp n n' : Nat} {f f' : Nat → Nat} (hk : κ r = .mpD dp n f)
    (hn : n = n') (hf : f = f') : Dig M dp n' f' := by subst hn hf; exact h.dig r hk

end

/-- A side condition of a segment: arithmetic, a fact from the state, a product bound. -/
macro "side " h:term : tactic =>
  `(tactic| first | omega | ((try dsimp only) <;> omega) | cfacts $h | (apply mul_lt_2_56 <;> cfacts $h))

/-- `omega` after reducing the projections of a cut's parameter record. -/
macro "om" : tactic => `(tactic| ((try dsimp only) <;> omega))

/-- A callee's scalar residue: its fields by arithmetic or from the state. -/
macro "res_tac " h:term : tactic =>
  `(tactic| (constructor <;> (try dsimp only) <;> first | omega | (exact ⟨by (try dsimp only); omega,
      by (try dsimp only); omega, by (try dsimp only); omega⟩) | (unfold Tom.Machine.Api.Heap.OffHeap; omega) | cfacts $h))

/-! ## `jal __muldi3` in a loop body -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
open Sail.ConcurrencyInterfaceV1.PreSail Tom.Machine.Api.Libgcc

/-- The keys `__muldi3` keeps that a caller may pin: `sp`, `gp`, `tp`, `s0`–`s11`. -/
abbrev sKeys : List Nat := [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The caller's pins `__muldi3` keeps. -/
def mulKeep (L : GRegs) : GRegs := L.filter (fun q => sKeys.contains q.1)

theorem keepOK_sKeys {K : GRegs} (h : ∀ n ∈ keysG K, n ∈ sKeys) : KeepOK mulWrites K := by
  have key : ∀ k ∈ sKeys, (1 ≤ k ∧ k ≤ 31) ∧ (∀ rr ∈ noiseRegs, (rr == gprReg k) = false) ∧
      (∀ m ∈ mulWrites, (gprReg m == gprReg k) = false) := by decide
  exact fun n hn => key n (h n hn)

theorem lookupG_mem {n : Nat} {v : BitVec 64} : ∀ {L : GRegs}, lookupG n L = some v → (n, v) ∈ L
  | [], h => by simp [lookupG] at h
  | (k, w) :: L, h => by
    simp only [lookupG] at h
    split at h
    · subst_vars; simp at h; subst h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (lookupG_mem h)

theorem keysG_mulKeep : ∀ (L : GRegs), ∀ n ∈ keysG (mulKeep L), n ∈ sKeys
  | [], _, h => by simp [mulKeep, keysG] at h
  | (k, w) :: L, n, h => by
    simp only [mulKeep, List.filter_cons] at h
    split at h
    · simp only [keysG, List.mem_cons] at h
      rcases h with rfl | h
      · rename_i hk; simpa using hk
      · exact keysG_mulKeep L n h
    · exact keysG_mulKeep L n h

theorem lookupG_append_some {n : Nat} {v : BitVec 64} : ∀ {X : GRegs} (Y : GRegs), lookupG n X = some v →
    lookupG n (X ++ Y) = some v
  | [], _, h => by simp [lookupG] at h
  | (k, w) :: X, Y, h => by
    simp only [lookupG, List.cons_append] at h ⊢
    split
    · split at h <;> simp_all
    · split at h
      · simp_all
      · exact lookupG_append_some Y h

theorem keysG_append : ∀ (X Y : GRegs), keysG (X ++ Y) = keysG X ++ keysG Y
  | [], _ => rfl
  | (_, _) :: X, Y => by simp only [List.cons_append, keysG, keysG_append X Y]

theorem SubR.append {L X : GRegs} (Y : GRegs) (h : SubR L X) : SubR L (X ++ Y) := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    simp only [SubR, List.map_cons, List.cons.injEq] at h ⊢
    exact ⟨lookupG_append_some Y h.1, ih h.2⟩

/-- **`jal __muldi3`** at `pc` with `a0 = x`, `a1 = y`: the caller's pinned
`sp`/`s`-registers kept, `a0 = x * y` at `ret = pc + 4`. -/
theorem call_mul {pc : BitVec 64} {w : BitVec 32} {imm : BitVec 21} {base : Nat} {code : List (BitVec 32)}
    {L K : GRegs} (L2 : GRegs) {M : Mem} {o : Array String} {Q : Vsa.Machine.Config → Prop} (x y : Nat)
    (himg : Img M) (hc : CodeAt M base code) (ret : BitVec 64)
    (k : Triple (At ret L2 M K o) Q)
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
    (htgt : pc + Functions.sign_extend (m := 64) imm = muldi3Entry := by decide)
    (hret : Sail.BitVec.addInt pc 4 = ret := by decide) (hra : ret.toNat % 4 = 0 := by decide)
    (hfe : 0x80000000 ≤ pc.toNat ∧ FetchOK pc.toNat ∧ pc.toNat % 4 = 0 :=
      by exact ⟨by decide, fetchOK_of_le (by simp [tohostAddr]), by decide⟩)
    (hx : lookupG 10 L = some (BitVec.ofNat 64 x) := by exact rfl)
    (hy : lookupG 11 L = some (BitVec.ofNat 64 y) := by exact rfl)
    (hK : (keysG K).all (fun n => sKeys.contains n) = true := by exact rfl)
    (hL2 : SubR L2 ((1, ret) :: (10, BitVec.ofNat 64 (x * y)) :: mulKeep L) := by exact rfl) :
    Triple (At pc L M K o) Q := by
  have hKs : ∀ n ∈ keysG K, n ∈ sKeys := fun n hn => by
    have := List.all_eq_true.1 hK n hn; simpa using this
  have hj := muldi3_call (L := L) (Lk := mulKeep L) (L2 := (1, Sail.BitVec.addInt pc 4) ::
      (10, BitVec.ofNat 64 x * BitVec.ofNat 64 y) :: mulKeep L) (keep := K) (outp := o)
    (x := BitVec.ofNat 64 x) (y := BitVec.ofNat 64 y) himg hc hwd hword hnotrvc hdec hfe htgt (by rw [hret]; exact hra)
    (fun p hp => by
      simp only [List.mem_cons] at hp
      rcases hp with rfl | rfl | hp
      · exact lookupG_mem hx
      · exact lookupG_mem hy
      · exact (List.mem_filter.1 hp).1)
    (fun n hn => by
      simp only [keysG, List.mem_cons] at hn
      rcases hn with rfl | rfl | hn
      · decide
      · decide
      · have := keysG_mulKeep L n hn; revert this; generalize n = k; decide +revert)
    (fun n hn => by have := hKs n hn; revert this; generalize n = k; decide +revert)
    (keepOK_sKeys fun n hn => by
      rw [keysG_append, List.mem_append] at hn
      rcases hn with hn | hn
      · exact keysG_mulKeep L n hn
      · exact hKs n hn)
    (fun p hp => hp)
  rw [hret, ofNat_mul_ofNat] at hj
  exact Triple.seq (Triple.rmap (fun _ h => h.subL (SubR.append K hL2)) hj) k


/-! ## A tail call as a step; the own frame given back before a whole-stack tail call -/

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι}

/-- **A tail call as a step**: the callee runs from its entry and returns to the caller's
`ra`; the rest of the edge starts there (`At ra (C.rets ++ keep)`), with the caller's kinds
updated along `σ` (side conditions as `tail_std`). -/
theorem tail_seq (C : Contract) (p : C.P) (σ : C.R → ι) {κ : ι → Kind} {m M : Mem}
    (hSt : St ρ isW W κ m M) {L K K' : GRegs} {outp : Array String} {ra : BitVec 64}
    {Q : Vsa.Machine.Config → Prop} (hres : C.Res p) (hra : ra.toNat % 4 = 0)
    (k : ∀ x M', C.Q p x → St ρ isW W (Kind.push σ C.ws κ (C.out p x)) m M' →
      Triple (At ra (C.rets p ra ++ (Abi.ofL (L ++ K)).keep) M' K' outp) Q)
    (hsub : ∀ r, (C.lay p r).Sub (ρ (σ r)) := by intro r; cases r <;> iv_omega)
    (hk : ∀ r, C.kind p r = κ (σ r) := by intro r; cases r <;> rfl)
    (hsep : SepPres isW C.isW σ C.all = true := by decide) (hw : (C.ws.map σ).all isW = true := by decide)
    (hW : SubN (C.ws.map σ) W = true := by decide)
    (hargs : SubR ((1, ra) :: C.args p) (L ++ K) := by exact rfl)
    (hkeys : abiKeys.all (fun n => (lookupG n (L ++ K)).isSome) = true := by exact rfl)
    (hK' : SubR K' (C.rets p ra ++ (Abi.ofL (L ++ K)).keep) := by exact rfl) :
    Triple (At C.entry L M K outp) Q :=
  Triple.ex (A := fun _ M' => At ra (C.rets p ra ++ (Abi.ofL (L ++ K)).keep) M' K' outp)
    (Φ := fun x M' => C.Q p x ∧ St ρ isW W (Kind.push σ C.ws κ (C.out p x)) m M')
    (C.run p σ hSt hres hra hsub hk hsep hw hW hargs hkeys hK') fun x M' h => k x M' h.1 h.2

/-- Every byte of the generated pieces lies in a contract region (a site holds none). -/
theorem InAny.site {R Y : Type} {ρ : Y → Iv} {σ : R → Iv} [DecidableEq R] (f : Y → R)
    (hsub : ∀ y, (ρ y).Sub (σ (f y))) {W : List (Option Y)} {ws : List R}
    (hW : SubN ((W.filterMap id).map f) ws = true := by decide) :
    ∀ a, InAny (Site.lay ρ) W a → InAny σ ws a := fun a h => by
  obtain ⟨x, hx, hin⟩ := h.exists
  cases x with
  | none => simp only [Site.lay, Iv.nil, Iv.In] at hin; omega
  | some y =>
    have hm : f y ∈ (W.filterMap id).map f := List.mem_map_of_mem (List.mem_filterMap.2 ⟨_, hx, rfl⟩)
    have := hsub y
    exact InAny.of_mem (of_decide_eq_true (List.all_eq_true.1 hW _ hm))
      (by simp only [Site.lay] at hin; unfold Iv.Sub Iv.In at *; omega)

/-- As `InAny.site`, without a site. -/
theorem InAny.push {R Y : Type} {ρ : Y → Iv} {σ : R → Iv} [DecidableEq R] (f : Y → R)
    (hsub : ∀ y, (ρ y).Sub (σ (f y))) {W : List Y} {ws : List R}
    (hW : SubN (W.map f) ws = true := by decide) :
    ∀ a, InAny ρ W a → InAny σ ws a := fun a h => by
  obtain ⟨y, hy, hin⟩ := h.exists
  have := hsub y
  exact InAny.of_mem (of_decide_eq_true (List.all_eq_true.1 hW _ (List.mem_map_of_mem hy)))
    (by unfold Iv.Sub Iv.In at *; omega)

/-- **The state over the contract's layout** (before a tail call that runs on the whole
stack): the frame since the entry, the stack region `s` by its entry witness, every
other region `r` by the generated region `e r` (same interval, same kind). -/
theorem St.flat {R : Type} [DecidableEq R] {κ : ι → Kind} {m M : Mem} (h : St ρ isW W κ m M)
    {lay : R → Iv} {isWR : R → Bool} {ws : List R} {kd : R → Kind} (s : R) (e : R → ι)
    (hS : Sound lay isWR) (hs : (kd s).Fits (lay s) ∧ (kd s).Wit (lay s) M)
    (hin : ∀ a, InAny ρ W a → InAny lay ws a)
    (hlay : ∀ r, r ≠ s → ρ (e r) = lay r := by intro r hr; cases r <;> first | exact absurd rfl hr | rfl)
    (hk : ∀ r, r ≠ s → κ (e r) = kd r := by intro r hr; cases r <;> first | exact absurd rfl hr | rfl) :
    St lay isWR ws kd m M := by
  refine ⟨hS, fun r => ?_, fun x hx => h.frm x fun h' => hx (hin x h')⟩
  by_cases hr : r = s
  · subst hr; exact hs
  · have hw := h.wit (e r)
    rw [hk r hr, hlay r hr] at hw
    exact hw

end


/-! ## A store into digit 0 written as a scalar cell -/

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}
  {pc pc' : BitVec 64} {L0 L L' K : GRegs} {o : Array String} {Q : Vsa.Machine.Config → Prop}

/-- `St.seqS` with the store's address given as any term equal to `p + 8` (a frame struct
at `sp - 56` has its `sign` at `sp - 48`). -/
theorem St.seqS2 (h : St ρ isW W κ m M) (r : ι) {p dp s q : Nat} {a : MpInt} (hk : κ r = .mpS p dp a)
    (hq : q = p + 8)
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M [(q, 4, BitVec.ofNat 64 s)]) K o)) (hs : s < 2 ^ 32)
    (k : ∀ M', St ρ isW W (Kind.set κ r (.mpS p dp { a with sign := s })) m M' → Triple (At pc' L' M' K o) Q)
    (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q := by
  subst hq; exact h.seqS r hk hseg hs k hw hW hL

/-- `St.seqD` at index 0 with the store's address the array's base (`dp`, not `dp + 4 * 0`). -/
theorem St.seqD0 (h : St ρ isW W κ m M) (r : ι) {dp n v : Nat} {f : Nat → Nat} (hk : κ r = .mpD dp n f)
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M [(dp, 4, BitVec.ofNat 64 v)]) K o))
    (hi : 0 < n) (hv : v < 2 ^ 32)
    (k : ∀ M', St ρ isW W (Kind.set κ r (.mpD dp n (fun j => if j = 0 then v else f j))) m M' →
      Triple (At pc' L' M' K o) Q)
    (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q :=
  h.seqD r hk (i := 0) (by simpa only [Nat.mul_zero, Nat.add_zero] using hseg) hi hv k hw hW hL

end


/-! ## Several allocation sites: `Site.lay` over `Site.lay` -/

section
variable {R : Type} {ρ : R → Iv} {w : R → Bool}

theorem Site.lo_all (h : ∀ y, 0x80000000 ≤ (ρ y).base) : ∀ x, 0x80000000 ≤ (Site.lay ρ x).base
  | none => Nat.le_refl _
  | some y => h y

theorem Site.off_all {H : List (Nat × Nat)} (h : ∀ y, Off (ρ y) H) : ∀ x, Off (Site.lay ρ x) H
  | none => Off.nil H
  | some y => h y

theorem Site.cov_all {Q : Nat → Prop} (h : ∀ y, w y = true → ∀ a, (ρ y).In a → Q a) :
    ∀ x, Site.wr w x = true → ∀ a, (Site.lay ρ x).In a → Q a
  | none, _, _, ha => by simp only [Site.lay, Iv.nil, Iv.In] at ha; omega
  | some y, hw, a, ha => h y hw a ha

theorem Site.ram_all (h : ∀ y, w y = true → Ram (ρ y).base (ρ y).len) :
    ∀ x, Site.wr w x = true → Ram (Site.lay ρ x).base (Site.lay ρ x).len
  | none, _ => Ram.nil
  | some y, hw => h y hw

end


/-!
* `St.refz`, `St.seqR`: a written plain-RAM region (`"Rk"` kind `"R"`, store rule `"w"`);
  its one-word store read back as a one-digit array by `Dig.of_frz1`;
* `HPost.keep`, `HPost.inplace`: the contract's post when nothing is written / a callee
  wrote the site in place (no allocation);
* `HContract.runP`, `tail_heap`, `HP.flatE`: a tail call to an allocating contract
  (`"tail"` with a heap callee), at a checkpoint or over the contract's layout (`"flat"`);
* `St.flat1`: `"flat"` for the style `"pre"` (one frame piece);
* `cmp_lt`, `cmp_ge`: `mp_cmp_mag`'s result word as the `ofNat` the rows compare.
-/

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι} {κ : ι → Kind} {m M : Mem}
  {pc pc' : BitVec 64} {L0 L L' K : GRegs} {o : Array String} {Q : Vsa.Machine.Config → Prop}

/-- A plain-RAM region snapshots the current memory. -/
theorem St.refz (h : St ρ isW W κ m M) (r : ι) (hk : κ r = .ram) :
    St ρ isW W (Kind.set κ r (.frz M)) m M := by
  refine ⟨h.sound, fun r' => ?_, h.frm⟩
  unfold Kind.set
  by_cases hr : r' = r
  · subst hr
    have := (h.wit r').2; rw [hk] at this
    simp only [ite_true]; exact ⟨trivial, this, fun _ _ => rfl⟩
  · simp only [hr, ite_false]; exact h.wit r'

/-- **A store into a written plain-RAM region** `r` (kind `.ram`, an out-parameter slot):
afterwards a snapshot of the memory before the store with the log applied. -/
theorem St.seqR (h : St ρ isW W κ m M) (r : ι) (hk : κ r = .ram) {log : List WEntry}
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M log) K o))
    (k : ∀ M', St ρ isW W (Kind.set κ r (.frz (writeLog M log))) m M' → Triple (At pc' L' M' K o) Q)
    (hlog : LogIn ρ r log := by login) (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q :=
  (Triple.seq hseg (k _ (h.step (Frm.store hlog) (by simp [hw]) hW
    (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      have hw0 := (h.wit r').2; rw [hk] at hw0
      simp only [Kind.set, if_true, Kind.Fits, Kind.Wit, true_and]
      exact ⟨hw0, fun _ _ => trivial⟩)
    (fun r' hr' => by simp only [List.mem_singleton] at hr'; simp [Kind.set, hr'])))).pre hL

/-- A digit array whose region is exactly its digits, re-kinded as a snapshot. -/
theorem St.frzD (h : St ρ isW W κ m M) (r : ι) {dp n : Nat} {f : Nat → Nat} (hk : κ r = .mpD dp n f)
    (hl : ρ r = ⟨dp, 4 * n⟩) : St ρ isW W (Kind.set κ r (.frz M)) m M := by
  refine ⟨h.sound, fun r' => ?_, h.frm⟩
  unfold Kind.set
  by_cases hr : r' = r
  · subst hr; rw [if_pos rfl]
    have hw := (h.wit r').2; rw [hk] at hw
    refine ⟨trivial, ?_, fun _ _ => rfl⟩
    rw [hl]; exact hw.ram
  · rw [if_neg hr]; exact h.wit r'

/-- **A store into a written slot modelled as a digit array** whose region is exactly its
digits (`Rk` "D", store rule "w"): afterwards a snapshot, as `St.seqR`. -/
theorem St.seqRD (h : St ρ isW W κ m M) (r : ι) {dp n : Nat} {f : Nat → Nat} (hk : κ r = .mpD dp n f)
    (hl : ρ r = ⟨dp, 4 * n⟩) {log : List WEntry}
    (hseg : Triple (At pc L M K o) (At pc' L' (writeLog M log) K o))
    (k : ∀ M', St ρ isW W (Kind.set κ r (.frz (writeLog M log))) m M' → Triple (At pc' L' M' K o) Q)
    (hlog : LogIn ρ r log := by login) (hw : isW r = true := by decide) (hW : SubN [r] W = true := by decide)
    (hL : SubR L (L0 ++ K) := by exact rfl) : Triple (At pc L0 M K o) Q :=
  (h.frzD r hk hl).seqW r (m0 := M) (by simp [Kind.set]) hseg (fun M' h' => k M' (h'.congrK fun r' => by
    unfold Kind.set; by_cases hr : r' = r <;> simp [hr])) hlog hw hW hL

/-- A one-word slot's current word as a one-digit `mp_int` (a callee that models its slot so). -/
def slotInt (x : Nat) : MpInt := ⟨1, 1, 0, [x]⟩

/-- **A plain-RAM slot read as a one-digit array**. -/
theorem St.slot1 (h : St ρ isW W κ m M) (r : ι) {pd : Nat} (hk : κ r = .ram) (hl : ρ r = ⟨pd, 4⟩)
    (hal : pd % 4 = 0) : St ρ isW W (Kind.set κ r (.mpD pd 1 (slotInt (bytesT4 M pd).toNat).digit)) m M := by
  refine ⟨h.sound, fun r' => ?_, h.frm⟩
  unfold Kind.set
  by_cases hr : r' = r
  · subst hr; rw [if_pos rfl]
    have hw := (h.wit r').2; rw [hk, hl] at hw
    refine ⟨by rw [hl]; exact Iv.sub_self _, ?_⟩
    exact { ram := hw, al := hal
            arr := fun j hj => by
              have : j = 0 := by omega
              subst this
              simp [slotInt, MpInt.digit] }
  · rw [if_neg hr]; exact h.wit r'

end

/-- A one-word slot after `*pd := r`, as the one-digit array `v`. -/
theorem Dig.of_frz1 {M m0 : Mem} {pd r v : Nat} (hal : pd % 4 = 0) (hr : r < 2 ^ 32) (he : r = v)
    (h : (Kind.frz (writeLog m0 [(pd, 4, BitVec.ofNat 64 r)])).Wit ⟨pd, 4⟩ M) : Dig M pd 1 (fun _ => v) := by
  subst he
  refine ⟨h.1, hal, fun j hj => ?_⟩
  have : j = 0 := by omega
  subst this
  rw [Nat.mul_zero, Nat.add_zero, bytesT4_congr (m := writeLog m0 [(pd, 4, BitVec.ofNat 64 r)])
    (fun x h1 h2 => h.2 x ⟨h1, by simp only; omega⟩), bytesT4_sw_self _ _ _ hr]

/-- The slot `⟨pd, 4 * n⟩` (`n = 1`) after `*pd := r`: the out kind `.mpD pd 1 (fun _ => v)`. -/
theorem Kind.frz1W {M m0 : Mem} {pd n r v : Nat} (hal : pd % 4 = 0) (hn : n = 1) (hr : r < 2 ^ 32) (he : r = v)
    (h : (Kind.frz (writeLog m0 [(pd, 4, BitVec.ofNat 64 r)])).Wit ⟨pd, 4 * n⟩ M) :
    (Kind.mpD pd 1 fun _ => v).Fits ⟨pd, 4 * n⟩ ∧ (Kind.mpD pd 1 fun _ => v).Wit ⟨pd, 4 * n⟩ M := by
  subst hn; exact ⟨Iv.sub_self _, Dig.of_frz1 hal hr he h⟩

section
open Tom.Machine.Api.Heap
variable {R : Type} {lay : R → Iv} {isW : R → Bool} {ws : List R} {site : R}

/-- **Nothing written** (an early return): the contract's post with every kind kept. -/
theorem HPost.keep {out kd : R → Kind} {hin : List (Nat × Nat)} {m : Mem} (hB : Bundle lay kd m)
    (hH : AHeap m hin) (hoff : Off (lay site) hin) (he : ∀ r, out r = kd r := by intro r; rfl) :
    HPost lay ws site out (lay site) hin hin m m where
  wit r _ _ := by rw [he]; exact hB r
  wsite := by rw [he]; exact hB site
  place := .keep
  frame := HFrm.refl _ _ _
  heap := hH
  foot _ h := .inl h
  off := hoff

/-- **The site written in place** (a tail-called routine that does not allocate): the
contract's post from the state over its layout, the heap unchanged. -/
theorem HPost.inplace [DecidableEq R] {out κ : R → Kind} {J : Iv} {hin hout : List (Nat × Nat)} {m M : Mem}
    (h : St lay isW ws κ m M) (hH : AHeap m hin) (hoff : ∀ r, Off (lay r) hin) (hJ : J = lay site)
    (hh : hout = hin) (hwit : ∀ r, r ∈ ws → r ≠ site → (out r).Fits (lay r) ∧ (out r).Wit (lay r) M)
    (hsite : (out site).Fits J ∧ (out site).Wit J M) : HPost lay ws site out J hin hout m M := by
  subst hJ hh
  exact { wit := hwit, wsite := hsite, place := .keep, frame := HFrm.of_frm h.frm
          heap := hH.frame fun a ha => h.frm a fun hx => by
            obtain ⟨r, _, hxr⟩ := hx.exists
            exact (hoff r).pt a hxr ha
          foot := fun _ h => .inl h, off := hoff site }

/-- The heap checkpoint over the contract's own layout at the entry (before a tail call to
an allocating routine on the whole stack, `"tail" … "flat"`). -/
theorem HP.flatE {H : List (Nat × Nat)} {m : Mem} (hH : AHeap m H) (hoff : ∀ r, Off (lay r) H)
    (hram : ∀ r, isW r = true → Ram (lay r).base (lay r).len) (hws : ∀ r, isW r = true → r ∈ ws) :
    HP lay isW H H (InAny lay ws) m m :=
  HP.entry hH hoff (fun r hr _ ha => InAny.of_mem (hws r hr) ha) hram

end

section
variable {ι : Type} [DecidableEq ι] {ρ : ι → Iv} {isW : ι → Bool} {W : List ι}

/-- `HContract.run` with the callee's post kept (a tail call: its placement and footprint
become the caller's), and the keep list after given (`K'`). -/
theorem HContract.runP (C : HContract) (p : C.P) (σ : C.R → ι) {κ : ι → Kind}
    {H0 : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m M : Mem}
    (hSt : St ρ isW W κ m M) (hp : HP ρ isW H0 (C.hin p) Wr0 m0 m) {L K K' : GRegs} {outp : Array String}
    {ra : BitVec 64} (hres : C.Res p) (hra : ra.toNat % 4 = 0)
    (hsub : ∀ r, (C.lay p r).Sub (ρ (σ r))) (hk : ∀ r, C.kind p r = κ (σ r))
    (hsep : SepPres isW C.isW σ C.all = true) (hw : (C.ws.map σ).all isW = true) (hWw : W.all isW = true)
    (hargs : SubR ((1, ra) :: C.args p) (L ++ K))
    (hkeys : abiKeys.all (fun n => (lookupG n (L ++ K)).isSome) = true)
    (hK' : ∀ x, SubR K' (C.rets p x ra ++ (Abi.ofL (L ++ K)).keep)) :
    Triple (At C.entry L M K outp)
      (fun cf => ∃ x M', At ra (C.rets p x ra ++ (Abi.ofL (L ++ K)).keep) M' K' outp cf ∧ C.Q p x ∧
        St (Iv.upd ρ (σ C.site) (C.site' p x)) isW W (Kind.pushH σ C.ws κ (C.out p x)) M' M' ∧
        HP (Iv.upd ρ (σ C.site) (C.site' p x)) isW H0 (C.hout p x) Wr0 m0 M' ∧
        HPost (C.lay p) C.ws C.site (C.out p x) (C.site' p x) (C.hin p) (C.hout p x) M M') := by
  intro c hc
  have hall : GHolds c.σ (L ++ K) := gholds_append.2 ⟨hc.regs, hc.keep⟩
  have hc' : At C.entry ((1, ra) :: C.args p) M (Abi.ofL (L ++ K)).keep outp c :=
    { hc with regs := hargs.gholds hall, keep := gholds_ofL hall hkeys }
  obtain ⟨c', hs, x, M', hat, hq, hpo⟩ := C.spec hra hres (hSt.sound.pull σ C.all C.hall hsub hsep)
    (hSt.wit.pull σ hsub hk (C.fits p)) (hp.heapAt hSt)
    (fun r => (hp.off (σ r)).sub (hsub r) (C.pos p hres r)) c hc'
  obtain ⟨h1, h2⟩ := C.after p x σ hSt hp hsub hsep hw hWw hpo
  exact ⟨c', hs, x, M', hat.cat (hK' x), hq, h1, h2, hpo⟩

/-- **A tail call to an allocating contract**: the callee runs from its entry at the
checkpoint `hp` and returns to the caller's `ra`; the rest of the edge (an exit) starts
there with the callee's result, the updated state and checkpoint, and the callee's post. -/
theorem tail_heap (C : HContract) (p : C.P) (σ : C.R → ι) {κ : ι → Kind}
    {H0 : List (Nat × Nat)} {Wr0 : Nat → Prop} {m0 m M : Mem}
    (hSt : St ρ isW W κ m M) (hp : HP ρ isW H0 (C.hin p) Wr0 m0 m) {L K K' : GRegs} {outp : Array String}
    {ra : BitVec 64} {Q : Vsa.Machine.Config → Prop} (hres : C.Res p) (hra : ra.toNat % 4 = 0)
    (k : ∀ x M', C.Q p x →
      St (Iv.upd ρ (σ C.site) (C.site' p x)) isW W (Kind.pushH σ C.ws κ (C.out p x)) M' M' →
      HP (Iv.upd ρ (σ C.site) (C.site' p x)) isW H0 (C.hout p x) Wr0 m0 M' →
      HPost (C.lay p) C.ws C.site (C.out p x) (C.site' p x) (C.hin p) (C.hout p x) M M' →
      Triple (At ra (C.rets p x ra ++ (Abi.ofL (L ++ K)).keep) M' K' outp) Q)
    (hsub : ∀ r, (C.lay p r).Sub (ρ (σ r)) := by intro r; cases r <;> iv_omega)
    (hk : ∀ r, C.kind p r = κ (σ r) := by intro r; cases r <;> rfl)
    (hsep : SepPres isW C.isW σ C.all = true := by decide) (hw : (C.ws.map σ).all isW = true := by decide)
    (hWw : W.all isW = true := by decide)
    (hargs : SubR ((1, ra) :: C.args p) (L ++ K) := by exact rfl)
    (hkeys : abiKeys.all (fun n => (lookupG n (L ++ K)).isSome) = true := by exact rfl)
    (hK' : ∀ x, SubR K' (C.rets p x ra ++ (Abi.ofL (L ++ K)).keep) := by intro _; exact rfl) :
    Triple (At C.entry L M K outp) Q :=
  Triple.ex (C.runP p σ hSt hp hres hra hsub hk hsep hw hWw hargs hkeys hK')
    fun x M' ⟨hq, h1, h2, h3⟩ => k x M' hq h1 h2 h3

end

/-- **Forget a one-piece frame split**: the stack region is plain RAM again, the
other regions keep their kinds, the frame since the entry (`"tail" … "flat"`, style `"pre"`). -/
theorem St.flat1 {R : Type} [DecidableEq R] {ρ : R → Iv} {isW : R → Bool} {s : R} {f : Nat}
    {W : List (Option R)} {κ : Option R → Kind} {m M : Mem} {ws : List R}
    (h : St (Split.lay ρ s f) (Split.wr isW) W κ m M) (hf : f ≤ (ρ s).len) (hS : Sound ρ isW)
    (hram : Ram (ρ s).base (ρ s).len) (hws : SubN (W.map (fun o => o.getD s)) ws = true := by decide) :
    St ρ isW ws (fun r => if r = s then .ram else κ (some r)) m M where
  sound := hS
  wit r := by
    by_cases hr : r = s
    · subst hr; simp only [if_true]; exact ⟨trivial, hram⟩
    · simp only [if_neg hr]
      have hw := h.wit (some r)
      simp only [Split.lay, if_neg hr] at hw
      exact hw
  frm := h.unsplit hf hws

/-- `mp_cmp_mag`'s result word (`ordCode` as `BitVec.ofInt`) for `x < y`: `MP_LT` as the
rows' `ofNat`. -/
theorem cmp_lt {x y : Nat} (h : x < y) :
    BitVec.ofInt 64 (Tom.ordCode (compare x y)) = BitVec.ofNat 64 18446744073709551615 := by
  rw [Nat.compare_eq_lt.2 h]; rfl

/-- `mp_cmp_mag`'s result word for `x ≥ y`: `MP_EQ` or `MP_GT`. -/
theorem cmp_ge {x y : Nat} (h : ¬ x < y) :
    BitVec.ofInt 64 (Tom.ordCode (compare x y)) = BitVec.ofNat 64 (if x = y then 0 else 1) := by
  by_cases he : x = y
  · rw [if_pos he, he, Nat.compare_eq_eq.2 rfl]; rfl
  · rw [if_neg he, Nat.compare_eq_gt.2 (by omega)]; rfl

end Tom.Machine
