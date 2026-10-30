import Tom.Machine.Api.Exptmod
import Tom.Machine.Api.Invmod
import Tom.Machine.Api.MpInitMulti
import Tom.Machine.Api.MpClearMulti
import Tom.Spec.MpExptmodStep

/-!
# `mp_exptmod(G, X, P, Y)`: the allocating contract

`Api/Exptmod.lean`'s regions and effect (`Y` written, its block re-placed by the worker), without
`redmode` (`a0`–`a3` only). The stack: for `X ≥ 0` the 96-byte frame and the three predicates
(no stack), then the worker called by `j` (the frame popped): **its** reservation,
`SMpExptmodFast.F` or `SMpExptmod.F` by the dispatch (`Fd`); for `X < 0` the frame and the
deepest of `mp_init_multi`, `mp_invmod`, `mp_abs`, `mp_clear_multi` and the recursive call (on
`G⁻¹ mod P`, at most `P->used` digits: `Fn`).

`Res`: `Exptmod.Base` and `Arith`, the workers' arithmetic residues for the mode the dispatch
picks (every multiplier and reduction of both workers grows its destination): `P > 1`,
the C's `int`s on a product of two residues (no room for Montgomery's normalization, which grows
`res`, `Api/MontNormG.lean`), and the `2^k`
setup's exact digit. No DR clause: a DR modulus is a `2^k - L` one
(`isReduce2kL_of_dr`), so `redmode == 1` never reaches `s_mp_exptmod_fast`. For
`X < 0` nothing more: `mp_invmod` and `mp_abs` grow their destinations (`MpInvmodG`,
`Api/MpAbsG.lean`).

`Q`: `MP_MEM` or `ExptmodPost` (the Spec's dispatch, `Tom/Spec/MpExptmodStep.lean`).
`StatementOf` carries the callees' statements in its residue, and for `X < 0` the recursive
call's (`StatementNN`, the case `X ≥ 0`): `Fn/MpExptmod.lean` closes both.
-/

namespace Tom.Machine.Api.MpExptmod

open LeanRV64DExecutable Vsa Vsa.Sim Vsa.Logic
open Tom.Machine Tom.Machine.Code Tom.Machine.Api.Alloc Tom.Machine.Api.Heap Tom.Machine.Std
open Tom.Machine.Api.Exptmod (P R lay kind out isW ws site' hin hout rets Base Out)
open Tom Tom.Exptmod Tom.MpExptmodStep

def entry : BitVec 64 := 0x80000e94#64

/-- The arguments: `a0 = G`, `a1 = X`, `a2 = P`, `a3 = Y`. -/
def args (p : P) : GRegs :=
  [(2, BitVec.ofNat 64 p.sp), (3, gpV), (10, BitVec.ofNat 64 p.pg), (11, BitVec.ofNat 64 p.px),
   (12, BitVec.ofNat 64 p.pn), (13, BitVec.ofNat 64 p.py)]

/-- The dispatch of `X ≥ 0` to `s_mp_exptmod_fast` (`MP_IS_ODD(P) || dr != 0`, not `2^k-L`). -/
def IsFast (n : MpInt) : Prop := isReduce2kL n ≠ 1 ∧ ((0 < n.used ∧ n.digit 0 % 2 = 1) ∨ drC n ≠ 0)

instance (n : MpInt) : Decidable (IsFast n) := by unfold IsFast; infer_instance

/-- The worker's reservation (`X ≥ 0`). -/
def Fd (p : P) : Nat := if IsFast p.n then SMpExptmodFast.F p else SMpExptmod.F p

/-- The negative exponent's callees and the recursive call (its `G` at most `P->used` digits). -/
def Fn (n : MpInt) : Nat :=
  max Invmod.F (max MpInitMulti.F (max 64 (max MpClearMulti.F
    (max (SMpExptmodFast.Ff n n) (SMpExptmod.Fs n n)))))

def F (p : P) : Nat := if p.x.sign = Layout.mpNeg then 96 + Fn p.n else Fd p

/-- The arithmetic the workers need for the mode the dispatch picks. -/
structure Arith (n x : MpInt) : Prop where
  gt1 : 1 < n.mag
  bits : Layout.digitBits * (2 * n.used + 1) < 2 ^ 31
  r2k : isReduce2k n = 1 → SMpExptmodFast.Exact2k n

structure Res (p : P) : Prop extends Base (F p) p where
  arith : Arith p.n p.x

/-- `MP_MEM` (`Y` as it was), or `ExptmodPost`. -/
def Q (p : P) : Out → Prop
  | .err r => r = Layout.mpMem ∨ ExptmodPost p.g p.x p.n p.y p.y r
  | .ok _ y' => ExptmodPost p.g p.x p.n p.y y' Layout.mpOkay

/-- A run from `entry` with residue `Res'`. -/
def Spec (Res' : P → Prop) : Prop :=
  ∀ {p : P} {m : Mem} {v : Abi} {outp : Array String} {ra : BitVec 64}, ra.toNat % 4 = 0 → Res' p →
    Sound (lay (F p) p) isW → Bundle (lay (F p) p) (kind p) m → AHeap m (hin p) →
    (∀ r, Off (lay (F p) p r) (hin p)) →
    Triple (At entry ((1, ra) :: args p) m v.keep outp)
      (fun cf => ∃ x M, At ra (rets p x ra) M v.keep outp cf ∧ Q p x ∧
        HPost (lay (F p) p) ws .yD (out p x) (site' (F p) p x) (hin p) (hout p x) m M)

/-- **`mp_exptmod(G, X, P, Y)` on the machine.** -/
def Statement : Prop := Spec Res

/-- The nonnegative exponent (the recursive call's case). -/
def StatementNN : Prop := Spec fun p => Res p ∧ p.x.sign ≠ Layout.mpNeg

/-- The residue with the callees' contracts as premises (`Fn/MpExptmodMainG.lean` proves
`StatementOf`; `Fn/MpExptmod.lean` closes it). -/
structure ResOf (p : P) : Prop extends Res p where
  fast : SMpExptmodFast.Statement
  slow : SMpExptmod.Statement
  inv : MpInvmodG.Statement
  nn : p.x.sign = Layout.mpNeg → StatementNN

def StatementOf : Prop := Spec ResOf

/-! ## The outcomes, by path -/

section
variable {p : P}

theorem Q_pneg (h : p.n.sign = Layout.mpNeg) : Q p (.err Layout.mpVal) := .inr (post_pneg h)

/-- `mp_reduce_is_2k_l(P) == MP_YES`: the tail call `s_mp_exptmod(…, 1)`. -/
theorem Q_l2k {x : Out} (hP : p.n.Valid) (hps : p.n.sign ≠ Layout.mpNeg) (hxs : p.x.sign ≠ Layout.mpNeg)
    (hl : isReduce2kL p.n = 1) (h : SMpExptmod.Q { p with mode := 1 } x) : Q p x := by
  cases x with
  | err r => exact h.imp_right fun hs => post_xpos hps hxs (nn_l2k hP hl hs)
  | ok q y' => exact post_xpos hps hxs (nn_l2k hP hl h)

/-- `MP_IS_ODD(P) || dr != 0`: the tail call `s_mp_exptmod_fast(…, dr)`. -/
theorem Q_fast {x : Out} (hP : p.n.Valid) (hps : p.n.sign ≠ Layout.mpNeg) (hxs : p.x.sign ≠ Layout.mpNeg)
    (hf : IsFast p.n) (h : SMpExptmodFast.Q { p with mode := drC p.n } x) : Q p x := by
  cases x with
  | err r => exact .inl h
  | ok q y' => exact post_xpos hps hxs (nn_fast hP hf.1 hf.2 ⟨rfl, h⟩)

/-- Else: the tail call `s_mp_exptmod(…, 0)` (Barrett). -/
theorem Q_barrett {x : Out} (hP : p.n.Valid) (hps : p.n.sign ≠ Layout.mpNeg) (hxs : p.x.sign ≠ Layout.mpNeg)
    (hl : isReduce2kL p.n ≠ 1) (hf : ¬ ((0 < p.n.used ∧ p.n.digit 0 % 2 = 1) ∨ drC p.n ≠ 0))
    (h : SMpExptmod.Q { p with mode := 0 } x) : Q p x := by
  cases x with
  | err r => exact h.imp_right fun hs => post_xpos hps hxs (nn_barrett hP hl hf hs)
  | ok q y' => exact post_xpos hps hxs (nn_barrett hP hl hf h)

end

/-! ## The stack -/

theorem F_nn {p : P} (h : p.x.sign ≠ Layout.mpNeg) : F p = Fd p := by simp [F, h]

theorem F_neg {p : P} (h : p.x.sign = Layout.mpNeg) : F p = 96 + Fn p.n := by simp [F, h]

theorem Fd_fast {p : P} (h : IsFast p.n) : Fd p = SMpExptmodFast.F p := by simp [Fd, h]

theorem Fd_slow {p : P} (h : ¬ IsFast p.n) : Fd p = SMpExptmod.F p := by simp [Fd, h]

/-- The worker's reservation holds the 96-byte frame. -/
theorem frame_le_Fd (p : P) : 96 ≤ Fd p := by
  unfold Fd; split
  · show 96 ≤ SMpExptmodFast.Ff p.g p.n; unfold SMpExptmodFast.Ff; omega
  · show 96 ≤ SMpExptmod.Fs p.g p.n; unfold SMpExptmod.Fs; omega

/-- The recursive call's reservation, for a `G` of at most `P->used` digits. -/
theorem Fd_le_Fn {p : P} (hg : p.g.used ≤ p.n.used) : Fd p ≤ Fn p.n := by
  have h1 : SMpExptmodFast.Ff p.g p.n ≤ SMpExptmodFast.Ff p.n p.n := by
    unfold SMpExptmodFast.Ff; omega
  have h2 : SMpExptmod.Fs p.g p.n ≤ SMpExptmod.Fs p.n p.n := by
    unfold SMpExptmod.Fs; omega
  unfold Fd Fn; split
  · show SMpExptmodFast.Ff p.g p.n ≤ _; omega
  · show SMpExptmod.Fs p.g p.n ≤ _; omega

theorem frame_le_F (p : P) : 96 ≤ F p := by
  unfold F; split
  · omega
  · exact frame_le_Fd p

theorem invF_le_Fn (n : MpInt) : Invmod.F ≤ Fn n := by unfold Fn; omega
theorem initF_le_Fn (n : MpInt) : MpInitMulti.F ≤ Fn n := by unfold Fn; omega
theorem absF_le_Fn (n : MpInt) : 64 ≤ Fn n := by unfold Fn; omega
theorem clearF_le_Fn (n : MpInt) : MpClearMulti.F ≤ Fn n := by unfold Fn; omega

theorem frame_lt_F (p : P) : 112 ≤ F p := by
  have h : 112 ≤ Fd p := by
    unfold Fd; split
    · show 112 ≤ SMpExptmodFast.Ff p.g p.n; unfold SMpExptmodFast.Ff; omega
    · show 112 ≤ SMpExptmod.Fs p.g p.n; unfold SMpExptmod.Fs; omega
  unfold F; split
  · have := absF_le_Fn p.n; omega
  · exact h


/-! ## The predicates' words -/

theorem is2kL_lt (n : MpInt) : isReduce2kL n < 2 ^ 64 := by
  unfold isReduce2kL; split
  · decide
  · split
    · decide
    · split <;> decide

theorem is2k_lt (n : MpInt) : isReduce2k n < 2 ^ 64 := by
  unfold isReduce2k; split
  · decide
  · split
    · decide
    · split <;> decide

theorem dr_lt (n : MpInt) : (if IsDrModulus n then 1 else 0) < 2 ^ 64 := by split <;> decide

theorem drC_dr {n : MpInt} (h : IsDrModulus n) : drC n = 1 := by simp [drC, h]

theorem drC_2k {n : MpInt} (h : ¬ IsDrModulus n) (h2 : isReduce2k n = 1) : drC n = 2 := by simp [drC, h, h2]

theorem drC_0 {n : MpInt} (h : ¬ IsDrModulus n) (h2 : ¬ isReduce2k n = 1) : drC n = 0 := by simp [drC, h, h2]

/-! ## The negative exponent -/

section
variable {p : P}

/-- `mp_invmod` failed (`MP_VAL`/`MP_MEM`): returned, `Y` as it was. -/
theorem Q_inv_err {c : MpInt} {r : Int} (hps : p.n.sign ≠ Layout.mpNeg) (hX : p.x.sign = Layout.mpNeg)
    (hq : r = Layout.mpMem ∨ InvmodPost p.g p.n c c r) (hr : r ≠ Layout.mpOkay) : Q p (.err r) := by
  rcases hq with h | h
  · exact .inl h
  · exact .inr (post_xneg hps hX h (fun _ => ⟨rfl, rfl⟩) (fun e => absurd e hr))

/-- `mp_invmod` succeeded, `mp_abs(X, &tmpX)`, the recursive call's outcome. -/
theorem Q_rec {c Gi tX : MpInt} {x : Out} (hxs : p.x.Shape) (hps : p.n.sign ≠ Layout.mpNeg)
    (hX : p.x.sign = Layout.mpNeg) (hi : InvmodPost p.g p.n c Gi Layout.mpOkay)
    (ha : AbsPost p.x (copyIn p.x (MpInt.zeroN defPrec)) tX) (hr : Q { p with g := Gi, x := tX } x) : Q p x := by
  have key : ∀ {y' : MpInt} {ret : Int}, ExptmodPost Gi tX p.n p.y y' ret →
      ExptmodPost p.g p.x p.n p.y y' ret := fun h =>
    post_xneg hps hX hi (fun e => absurd rfl e) (fun _ => neg_rec hxs hps ha h)
  cases x with
  | err r => exact hr.imp_right key
  | ok q y' => exact key hr

end

end Tom.Machine.Api.MpExptmod

namespace Tom.Machine.Api.MpExptmodOf

/-- `mp_exptmod`'s assembly's statement (the callees' contracts in the residue). -/
abbrev Statement : Prop := MpExptmod.StatementOf
abbrev hin : Exptmod.P → List (Nat × Nat) := Exptmod.hin

end Tom.Machine.Api.MpExptmodOf
