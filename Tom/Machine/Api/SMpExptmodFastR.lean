import Tom.Machine.Api.Exptmod
import Tom.Machine.Kit.Tab

/-!
# `s_mp_exptmod_fast`'s regions: the contract's, `res`'s digits and the table family

The region type of `s_mp_exptmod_fast`'s generated assembly (`experiments/asm/sef.asm.json`): the
contract's regions (`Api/Exptmod.lean`), `res`'s digit array `rD` (placed by
`mp_init_size(&res, P->alloc)`), and the table `M[]` as two families indexed by the entry
(`Kit/Tab.lean`): the structs `tS j` (24-byte slots of the own frame, laid out by `Iv.spread` at the
entry) and the digit arrays `tD j` (placed by `mp_init_size(&M[j], P->alloc)`). All are written; at
the entry the new regions are at `Iv.nil` and RAM (`layG`, `kindG`), sound beside the contract's
(`soundG`). `GPre` is the Statement's hypotheses.
-/

namespace Tom.Machine.Api.SMpExptmodFastR

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.Exptmod (P)

inductive R | stk | gS | gD | xS | xD | nS | nD | yS | yD | ks | ts | kc | tc | code | rD
  | tS (j : Nat) | tD (j : Nat)
  deriving DecidableEq

/-- The contract's region of each of ours (`rD` and the families: none). -/
def emb : R → Option Exptmod.R
  | .stk => some .stk | .gS => some .gS | .gD => some .gD | .xS => some .xS | .xD => some .xD
  | .nS => some .nS | .nD => some .nD | .yS => some .yS | .yD => some .yD | .ks => some .ks
  | .ts => some .ts | .kc => some .kc | .tc => some .tc | .code => some .code
  | .rD | .tS _ | .tD _ => none

def layG (p : P) (r : R) : Iv :=
  match emb r with
  | some c => Exptmod.lay (SMpExptmodFast.F p) p c
  | none => Iv.nil

def kindG (p : P) (_ : Mem) (r : R) : Kind :=
  match emb r with
  | some .stk => .ram
  | some c => Exptmod.kind p c
  | none => .ram

def isWG : R → Bool
  | .stk | .yS | .yD | .rD | .tS _ | .tD _ => true
  | _ => false

theorem layG_stk (p : P) : layG p .stk = ⟨p.sp - SMpExptmodFast.F p, SMpExptmodFast.F p⟩ := rfl

/-- The contract's regions as ours. -/
def unemb : Exptmod.R → R
  | .stk => .stk | .gS => .gS | .gD => .gD | .xS => .xS | .xD => .xD | .nS => .nS | .nD => .nD
  | .yS => .yS | .yD => .yD | .ks => .ks | .ts => .ts | .kc => .kc | .tc => .tc | .code => .code

theorem emb_some {r : R} {c : Exptmod.R} (h : emb r = some c) : r = unemb c ∧ isWG r = Exptmod.isW c := by
  cases r <;> simp only [emb, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> exact ⟨rfl, rfl⟩

/-- The new regions are at `Iv.nil`, below every contract region: sound beside them. -/
theorem soundG {p : P} (hS : Sound (Exptmod.lay (SMpExptmodFast.F p) p) Exptmod.isW)
    (hlo : ∀ c, 0x80000000 ≤ (Exptmod.lay (SMpExptmodFast.F p) p c).base) : Sound (layG p) isWG := by
  intro r t h
  cases hr : emb r with
  | none =>
    rw [show layG p r = Iv.nil by simp [layG, hr]]
    cases ht : emb t with
    | none =>
      rw [show layG p t = Iv.nil by simp [layG, ht]]
      unfold Iv.Disj Tom.Machine.Disj Iv.nil; dsimp only; omega
    | some c =>
      rw [show layG p t = Exptmod.lay (SMpExptmodFast.F p) p c by simp [layG, ht]]
      exact Iv.nil_disj (hlo c)
  | some c =>
    rw [show layG p r = Exptmod.lay (SMpExptmodFast.F p) p c by simp [layG, hr]]
    cases ht : emb t with
    | none =>
      rw [show layG p t = Iv.nil by simp [layG, ht]]
      exact Disj.symm (Iv.nil_disj (hlo c))
    | some d =>
      rw [show layG p t = Exptmod.lay (SMpExptmodFast.F p) p d by simp [layG, ht]]
      obtain ⟨er, wr⟩ := emb_some hr
      obtain ⟨et, wt⟩ := emb_some ht
      refine hS c d ?_
      have hne : c ≠ d := fun e => by subst e; rw [er, et] at h; simp [Sep] at h
      simp only [Sep, wr, wt] at h
      simp only [Sep, hne, decide_false, Bool.not_false, Bool.true_and]
      simp at h; simpa using h.2

/-- The Statement's hypotheses and the extended layout's soundness. -/
structure GPre (p : P) (m : Mem) (ra : BitVec 64) : Prop where
  ra4 : ra.toNat % 4 = 0
  res : SMpExptmodFast.Res p
  sound : Sound (Exptmod.lay (SMpExptmodFast.F p) p) Exptmod.isW
  bund : Bundle (Exptmod.lay (SMpExptmodFast.F p) p) (Exptmod.kind p) m
  heap : AHeap m (Exptmod.hin p)
  off : ∀ r, Off (Exptmod.lay (SMpExptmodFast.F p) p r) (Exptmod.hin p)
  lay : Sound (layG p) isWG

end Tom.Machine.Api.SMpExptmodFastR
