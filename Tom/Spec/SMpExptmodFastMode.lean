import Tom.Spec.SMpExptmodFastStep

/-!
# `s_mp_exptmod_fast` by mode: the run, `redux`'s relation and the result

`Tom/Spec/SMpExptmodFastStep.lean` states the three reductions (`rx_mont`, `rx_dr`, `rx_2k`) and the
three results (`fin_mont`, `fin_dr`, `fin_2k`); the machine's loop is one for all modes (`redux` a
function pointer), so its invariants are stated once over the mode `md`:

* `redRel md x n d x'`: what `redux(x, n, d)` leaves in mode `md` (the routine `s8` points to);
* `redF P md`, `m1F G P md`, `res0F P md`, `runF G X P md`: the run of `Tom/Spec/WindowStep.lean`;
* `rxF`: `redux` as a transfer in every mode, from the mode's conditions (`Cond`);
* `finF`: the result `SExptFastPost` from the run's `Done` and (Montgomery) the last `redux`.
-/

namespace Tom.SMpExptmodFastStep

open MpInt Ledger Window WindowStep Exptmod Mont Reduce

/-- What `redux(x, n, d)` leaves in mode `md`. -/
def redRel : Nat → MpInt → MpInt → Nat → MpInt → Prop
  | 0, x, n, d, x' => MontRedFastGStep.RedcV x n d x'
  | 1, x, n, d, x' => DrReducePost x n d x'
  | _, x, n, d, x' => Reduce2kPost x n d x'

/-- `redux`'s value function in mode `md`. -/
def redF (P : MpInt) : Nat → Nat → Nat
  | 0 => redMont P
  | 1 => redDrC P
  | _ => red2kC P

/-- `M[1]` before the table: `G R mod P` (Montgomery), `G mod P` else. -/
def m1F (G P : MpInt) : Nat → Nat
  | 0 => (base G P * (radix ^ P.used % P.mag)) % P.mag
  | _ => base G P

/-- `res` before the loop: `R mod P` (Montgomery), `1` else. -/
def res0F (P : MpInt) : Nat → Nat
  | 0 => radix ^ P.used % P.mag
  | _ => 1

/-- The run in mode `md`. -/
def runF (G X P : MpInt) (md : Nat) : Run := run (redF P md) X (m1F G P md) (res0F P md)

/-- The modulus and the setup digit `d` in mode `md` (what `mp_exptmod` and the setups give). -/
structure Cond (P : MpInt) (md d : Nat) : Prop where
  valid : P.Valid
  gt1 : 1 < P.mag
  mont : md = 0 → P.mag % 2 = 1 ∧ d = setupRho (P.digit 0)
  dr : md = 1 → IsDrModulus P ∧ d = drSetupDigit P
  r2k : 2 ≤ md → Setup2kPost P d

/-- **`redux` in every mode** is a transfer on residues below `P`. -/
theorem rxF {P : MpInt} {md d : Nat} (h : Cond P md d) :
    Rx (fun x x' => redRel md x P d x') (redF P md) P.mag P.used := by
  rcases md with _ | _ | md
  · obtain ⟨ho, hd⟩ := h.mont rfl; subst hd; exact rx_mont h.valid ho
  · obtain ⟨hdr, hd⟩ := h.dr rfl; subst hd; exact rx_dr h.valid hdr
  · exact rx_2k h.valid (by have := h.gt1; omega) (h.r2k (by omega))

/-- **The result** (`Y` after `mp_exch(&res, Y)`): for Montgomery after one more `redux`. -/
theorem finF {G X P res res' : MpInt} {md d : Nat} (h : Cond P md d)
    (hd : Done (runF G X P md) P.mag P.used res) (hfix : md = 0 → redRel 0 res P d res')
    (hres : md ≠ 0 → res' = res) : SExptmodFastPost G X P res' md := by
  rcases md with _ | _ | md
  · obtain ⟨ho, hdd⟩ := h.mont rfl; subst hdd; exact fin_mont h.valid ho hd (hfix rfl)
  · rw [hres (by decide)]; exact fin_dr hd
  · rw [hres (by omega)]; exact fin_2k (by omega) hd

/-- `res`'s start is a residue (`res_mont`, `res_one` give it). -/
theorem res0F_lt {P : MpInt} {md : Nat} (h1 : 1 < P.mag) : res0F P md < P.mag := by
  rcases md with _ | md
  · exact Nat.mod_lt _ (by omega)
  · exact h1

theorem res0F_ne {P : MpInt} {md : Nat} (h : md ≠ 0) : res0F P md = 1 := by
  rcases md with _ | md
  · exact absurd rfl h
  · rfl

theorem m1F_ne {G P : MpInt} {md : Nat} (h : md ≠ 0) : m1F G P md = base G P := by
  rcases md with _ | md
  · exact absurd rfl h
  · rfl

end Tom.SMpExptmodFastStep
