import Tom.Machine.Kit.At

/-!
# From `CodeAt` to byte pins, and keep-sets across a register frame

Relocated sibling proofs state "the code is
loaded" as a conjunction of literal byte pins `m[a]? = some b` (their
generated `…Loaded` predicates). `CodeAt.byte` gives each pin from the
`CodeAt` field of `Img m` by one `decide` on `byteAt` (the byte of the word
list at `a`), so `loaded_of h` closes a whole `…Loaded` goal.

Their posts state the register frame as "every register outside the
callee's write set reads as at entry". `keep_of_frame` carries any pin list
`K` across such a frame when its keys avoid the write set `wrs`
(`KeepOK wrs K`, a `decide` on literal keys).
-/

namespace Tom.Machine

open LeanRV64DExecutable Vsa Vsa.Sim
open Vsa.Machine (Config MState)

/-- The byte of the words `ws` (little-endian at `base`) at address `a`. -/
def byteAt (base : Nat) (ws : List (BitVec 32)) (a : Nat) : Option (BitVec 8) :=
  if base ≤ a then (ws[(a - base) / 4]?).map (fun w => w.extractLsb' (8 * ((a - base) % 4)) 8)
  else none

theorem CodeAt.byte {m : Mem} {base : Nat} {ws : List (BitVec 32)} (h : CodeAt m base ws)
    {a : Nat} {b : BitVec 8} (hb : byteAt base ws a = some b) : m[a]? = some b := by
  unfold byteAt at hb
  split at hb
  · rename_i hle
    cases hw : ws[(a - base) / 4]? with
    | none => rw [hw] at hb; cases hb
    | some w =>
      rw [hw, Option.map_some, Option.some.injEq] at hb
      subst hb
      obtain ⟨h0, h1, h2, h3⟩ := h _ w hw
      have ha : a = base + 4 * ((a - base) / 4) + (a - base) % 4 := by omega
      have hr : (a - base) % 4 < 4 := Nat.mod_lt _ (by decide)
      generalize (a - base) / 4 = q at ha h0 h1 h2 h3
      generalize (a - base) % 4 = r at ha hr ⊢
      subst ha
      match r, hr with
      | 0, _ => exact h0
      | 1, _ => exact h1
      | 2, _ => exact h2
      | 3, _ => exact h3
  · cases hb

/-- Close a conjunction of literal byte pins `m[a]? = some b` from
`h : CodeAt m base ws` (after unfolding the `…Loaded`/`…Chunk` definitions). -/
syntax "loaded_of " term : tactic
macro_rules
  | `(tactic| loaded_of $h) => `(tactic|
      (repeat' apply And.intro
       all_goals exact CodeAt.byte $h (by decide)))

/-- The keys of `K` are GPRs `x1`–`x31` outside the write set `wrs`. -/
def KeepOK (wrs : List Nat) (K : GRegs) : Prop :=
  ∀ n ∈ keysG K, (1 ≤ n ∧ n ≤ 31) ∧ (∀ rr ∈ noiseRegs, (rr == gprReg n) = false) ∧
    (∀ m ∈ wrs, (gprReg m == gprReg n) = false)

instance (wrs : List Nat) (K : GRegs) : Decidable (KeepOK wrs K) :=
  inferInstanceAs (Decidable (∀ n ∈ keysG K, _))

/-- Pins of `K` survive a run whose frame keeps every register that is neither
noise (PC, counters) nor written (`wrs`). -/
theorem keep_of_frame {σ σ' : MState} {wrs : List Nat} {K : GRegs} (hok : KeepOK wrs K)
    (hframe : ∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
      (∀ m ∈ wrs, (gprReg m == R) = false) → σ'.regs.get? R = σ.regs.get? R)
    (hK : GHolds σ K) : GHolds σ' K :=
  gholds_keep_of_frame K hok hframe hK

/-- The ABI keep-set avoids the argument and scratch registers `a0`–`a3`, `ra`, `t0`. -/
theorem keepOK_abi (v : Abi) : KeepOK [1, 5, 10, 11, 12, 13] v.keep := by
  unfold KeepOK
  rw [show keysG v.keep = abiKeys from rfl]
  decide

theorem keepOK_sub {wrs wrs' : List Nat} {K : GRegs} (h : KeepOK wrs K) (hs : ∀ m ∈ wrs', m ∈ wrs) :
    KeepOK wrs' K := fun n hn =>
  ⟨(h n hn).1, (h n hn).2.1, fun m hm => (h n hn).2.2 m (hs m hm)⟩

end Tom.Machine
