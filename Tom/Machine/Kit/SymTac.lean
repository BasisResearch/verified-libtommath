import Tom.Machine.Kit.Sym
import Tom.Machine.Kit.Arith

/-!
# Closing an executor run's residual

After `refine sym_at … ?_ ?_` (`Tom/Machine/Kit/Sym.lean`) the second goal is the residual of a
literal tree. These tactics close it:

* `sym_norm [facts]`: `sym_eval` (the tree, by compiled evaluation, one kernel conversion),
  `sym_split` (obligations, branch sides, leaves), then the denotations (`SE.den`, `regsDen`,
  `memDen`, loads by `ldv_lw`/`ldv_ld`), the caller's `facts` (entry registers, loaded values,
  address `toNat`s), 32/64-bit arithmetic on `ofNat` values and the branch guards (the compare
  lemmas of `Kit/Arith.lean`), everywhere;
* `sym_close [post] [entry] [facts]`: `sym_norm`, then every goal by `omega` (an infeasible side,
  an alignment) or as the leaf (`swp_leaf`): the post's pins (`post` unfolds the end register
  list; a pin is the entry value `hL` gives, by `entry`, or `ofNat` arithmetic by `omega`), the
  kept registers (none tracked), no owned bytes;
* `sym_close_st …`: the same for a leaf whose owned bytes are one store (`imgM_wl1`);
* `sym_close_any [post] [entry] [facts]`: the leaf is one of up to four `Exit`s (`swp_leaf_any`;
  the first whose PC, guard and pins check).

The hypotheses `hL`/`hK` of `triple_of_swp`'s `intro R hL hK` are named by the caller (hygiene
is off for these macros).
-/

namespace Tom.Machine.Sym

open Vsa.Sim

theorem imgM_wl1 {M : Mem} {A A' w : Nat} {v v' : BitVec 64} {a : Nat} (h1 : A = A') (h2 : v = v') :
    VsaIris.MallocFast.imgM (writeLog M [(A, w, v)]) a =
      VsaIris.MallocFast.imgM (writeLog M [(A', w, v')]) a := by rw [h1, h2]

end Tom.Machine.Sym

syntax "sym_norm" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| sym_norm [$es,*]) => `(tactic| (
    sym_eval
    sym_split
    all_goals try simp only [VsaIris.SymExec.SE.den, VsaIris.SymExec.regsDen, VsaIris.SymExec.memDen,
      VsaIris.SymExec.SOb.den, VsaIris.SymExec.aluVal, Tom.Machine.Sym.ldv_lw, Tom.Machine.Sym.ldv_ld,
      VsaIris.SymExec.rawR, BitVec.add_zero, $es,*] at *
    all_goals try simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend,
      Sail.BitVec.extractLsb, Vsa.Sim.shamt5Of, Vsa.Sim.shamtOf, BitVec.reduceExtractLsb',
      BitVec.reduceExtractLsb] at *
    all_goals try simp (disch := omega) only [Tom.Machine.extractLsb_ofNat32',
      Tom.Machine.ofNat_add_ofNatW, Tom.Machine.ofNat_add_ofNat, Tom.Machine.signExtend_ofNatW,
      Tom.Machine.signExtend_ofNat32, Tom.Machine.signExtend_ofNat32', Tom.Machine.sext_and_mask28W,
      Tom.Machine.and_mask28, Tom.Machine.srl32_ofNatW, Tom.Machine.srl32_ofNat', Tom.Machine.shl_ofNat',
      Tom.Machine.toNat_ofNat', Nat.reducePow, Nat.reduceAdd, Nat.reduceMod] at *
    all_goals try simp (disch := omega) only [Vsa.Sim.guardB, Tom.Machine.blt_ofNat,
      Tom.Machine.bge_ofNat, Tom.Machine.bge_zero_ofNat, Tom.Machine.bltu_ofNat',
      Tom.Machine.bgeu_ofNat', Tom.Machine.ofNat_beq', bne, decide_eq_true_eq, decide_eq_false_iff_not,
      Bool.not_eq_true', Bool.not_eq_false', beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.not_false, Nat.reduceMod] at *))

/-- The leaf's pins: each `p.1 ∈ rs`, `p.1 ≠ PC`, and its value (the entry value by `hL`, or
`ofNat` arithmetic by `omega`). -/
syntax "sym_regs" " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sym_regs [$ds,*] [$ls,*]) => `(tactic| (
    have hLc := hL
    simp only [$ls,*, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true] at hLc
    simp only [$ds,*, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    repeat' apply And.intro
    all_goals first
      | (show _ ∈ _; decide)
      | (show _ ≠ VsaIris.PC; decide)
      | (simp only [VsaIris.Sym.upd, Nat.reduceEqDiff, ↓reduceIte, hLc]; done)
      | (simp only [VsaIris.Sym.upd, Nat.reduceEqDiff, ↓reduceIte]
         apply BitVec.eq_of_toNat_eq
         try simp only [Tom.Machine.toNat_add', Tom.Machine.toNat_sub', Tom.Machine.toNat_ofNat']
         all_goals omega)))

/-- The kept registers: none is tracked (`p.1 ∈ rs` is false for each). -/
macro "sym_keep" : tactic => `(tactic|
  simp [Tom.Machine.Abi.keep, Tom.Machine.Abi.keepR, Tom.Machine.Abi.keepR1, Vsa.Sim.sKeepL])

syntax "sym_close" " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sym_close [$ds,*] [$ls,*] [$es,*]) => `(tactic| (
    sym_norm [$es,*]
    all_goals first
      | omega
      | (refine Tom.Machine.Sym.swp_leaf rfl ?_ ?_ (fun _ h => h.elim)
         · sym_regs [$ds,*] [$ls,*]
         · sym_keep)))

syntax "sym_close_st" " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sym_close_st [$ds,*] [$ls,*] [$es,*]) => `(tactic| (
    sym_norm [$es,*]
    all_goals first
      | omega
      | (refine Tom.Machine.Sym.swp_leaf rfl ?_ ?_ (fun _ _ => Tom.Machine.Sym.imgM_wl1 (by omega)
           (by apply BitVec.eq_of_toNat_eq; (try simp only [Tom.Machine.toNat_ofNat']); all_goals omega))
         · sym_regs [$ds,*] [$ls,*]
         · sym_keep)))

syntax "sym_close_any" " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sym_close_any [$ds,*] [$ls,*] [$es,*]) => `(tactic| (
    sym_norm [$es,*]
    all_goals first
      | omega
      | (refine Tom.Machine.Sym.swp_leaf_any List.mem_cons_self ?_ rfl ?_ ?_ (fun _ h => h.elim)
         · (dsimp only; omega)
         · sym_regs [$ds,*] [$ls,*]
         · sym_keep)
      | (refine Tom.Machine.Sym.swp_leaf_any (List.mem_cons_of_mem _ List.mem_cons_self) ?_ rfl ?_ ?_
           (fun _ h => h.elim)
         · (dsimp only; omega)
         · sym_regs [$ds,*] [$ls,*]
         · sym_keep)
      | (refine Tom.Machine.Sym.swp_leaf_any
           (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) ?_ rfl ?_ ?_
           (fun _ h => h.elim)
         · (dsimp only; omega)
         · sym_regs [$ds,*] [$ls,*]
         · sym_keep)
      | (refine Tom.Machine.Sym.swp_leaf_any (List.mem_cons_of_mem _
           (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) ?_ rfl ?_ ?_
           (fun _ h => h.elim)
         · (dsimp only; omega)
         · sym_regs [$ds,*] [$ls,*]
         · sym_keep)))
