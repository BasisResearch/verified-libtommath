import Tom.Spec.WindowStep
import Tom.Spec.ReduceStepG

/-!
# `s_mp_exptmod`: the model steps over the Ledger

`bn_s_mp_exptmod.c` at `0x8000261c`: `winsize` from `mp_count_bits(X)` (`winsize_eq`, the chain
as in `s_mp_exptmod_fast`), `mp_init(&M[1])` and the upper half (`MP_PREC` digits each),
`mp_init(&mu)`; by `redmode`:

* `0` (Barrett): `mp_reduce_setup(&mu, P)` (`ReduceSetupOut`: `MP_VAL` for `P = 0`, which
  `mp_exptmod` reaches), `redux = mp_reduce` (`rx_barrett`);
* else (`1`): `mp_reduce_2k_setup_l(P, &mu)` (`Setup2kLPost`), `redux = mp_reduce_2k_l`
  (`rx_2kL`; `Reduce2kPost _ P |mu|`).

Both reduce modulo `P` (`redP`), on residues below `B = max(P, 2)`. Then
`mp_mod(G, P, &M[1])` (`m1_mod`), the table, `mp_init(&res)`, `mp_set(&res, 1)` (`res_one`), the
loop and the tail of `Tom/Spec/WindowStep.lean` over `run (redP P) X (base G P) 1`,
`mp_exch(&res, Y)`: `fin` → `Exptmod.SExptmodPost`; `Out` is what `mp_exptmod` consumes.

Callee Posts as the frozen contracts give them: `CountBits`, `Reduce2kSetupL` (`LPost`'s
`Setup2kLPost`), `MpSet`, `MpCopy`, `MpSqrA`, `MpMulA`/`MpMul`. No contract yet, stated over the
Spec Post: `mp_reduce_setup` (`ReduceSetupPost`, with its `P = 0` error added here as
`ReduceSetupOut`), `mp_reduce` (`ReducePost`), `mp_reduce_2k_l` (`Reduce2kPost`), `mp_mod`
(`ModPost`).
-/

namespace Tom.SMpExptmodStep

open MpInt Ledger Window WindowStep Exptmod Mont Reduce

variable {G X P Y Y' mu res : MpInt}

/-! ## The setups -/

/-- What `mp_reduce_setup(&mu, P)` returns (allocations not failing): `mp_2expt`, then
`mp_div(mu, P, mu, NULL)`, which is `MP_VAL` for `P = 0`; for `P > 0` `ReduceSetupPost`. -/
structure ReduceSetupOut (b a' : MpInt) (ret : Int) : Prop where
  zero : b.mag = 0 → ret = Layout.mpVal
  pos : 0 < b.mag → ret = Layout.mpOkay ∧ ReduceSetupPost b a'

/-- The residue bound: `max(P, 2)`. -/
abbrev bnd (P : MpInt) : Nat := max P.mag 2

theorem bnd_fit (hP : P.Valid) (hP0 : 0 < P.mag) : bnd P ≤ radix ^ P.used := by
  have h1 := MpInt.mag_lt hP.toShape
  have h2 : radix ≤ radix ^ P.used := by
    have := Nat.pow_le_pow_right radix_pos (used_pos hP0); rwa [Nat.pow_one] at this
  have : 2 ≤ radix := by decide
  unfold bnd; omega

/-- A product of two residues is below `radix^(2U)` (`mp_reduce`'s range). -/
theorem sq_lt {B U v : Nat} (hBU : B ≤ radix ^ U) (hv : v ≤ (B - 1) * (B - 1)) : v < radix ^ (2 * U) := by
  rcases Nat.eq_zero_or_pos B with h0 | h0
  · rw [h0] at hv; have := Nat.pow_pos (n := 2 * U) radix_pos; simp at hv; omega
  · have : (B - 1) * (B - 1) < radix ^ U * radix ^ U :=
      Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (Nat.pow_pos radix_pos)
    rw [Nat.two_mul, Nat.pow_add]; omega

/-- Barrett (`mp_reduce`, `mu` from `mp_reduce_setup`). -/
theorem rx_barrett (hP : P.Valid) (hP0 : 0 < P.mag) (hmu : ReduceSetupPost P mu) :
    Rx (fun x x' => ReducePost x P mu x') (redP P.mag) (bnd P) P.used where
  fit := bnd_fit hP hP0
  lt := fun v _ => by have := Nat.mod_lt v hP0; unfold redP bnd; omega
  xfer := fun h hv hp => xfer_reduce h hP (used_pos hP0) hmu (sq_lt (bnd_fit hP hP0) hv) hp

/-- `2^k - L` (`mp_reduce_2k_l`, `mu` from `mp_reduce_2k_setup_l`: `P + |mu| = 2^p`). -/
theorem rx_2kL (hP : P.Valid) (hP0 : 0 < P.mag) (hs : Setup2kLPost P mu) :
    Rx (fun x x' => Reduce2kPost x P mu.mag x') (redP P.mag) (bnd P) P.used where
  fit := bnd_fit hP hP0
  lt := fun v _ => by have := Nat.mod_lt v hP0; unfold redP bnd; omega
  xfer := fun h _ hp => by
    have := xfer_reduce2k h hp
    rwa [redLoop_spec _ _ hP0 _ _ _ (fold2k_ok _ _ _ _ hs.spec) (Nat.le_refl _) (Nat.lt_succ_self _)] at this

/-! ## The redux calls' residues

A redux call reduces a product of two residues (`mp_sqr(&x, &x)`, `mp_mul(&x, &M[i], &x)`): at most
`2 P->used` digits (`prod_used`), Barrett's range (`mp_reduce`'s `Res.xu`) and `mp_reduce_2k_l`'s
quotient bound (`MpReduce2kLG.Res.small`). Barrett's `mu` from `mp_reduce_setup` has `P->used` to
`P->used + 2` digits (`mu_used`, `mp_reduce`'s `Res.mul`/`muh`); `mp_reduce_2k_setup_l`'s `mu` makes
`P = 2^p - |mu|` (`Setup2kLPost.spec`, `mp_reduce_2k_l`'s `Res.hd`). -/

theorem prod_used (hP : P.Valid) (hP0 : 0 < P.mag) {x : MpInt} {v : Nat} (h : Settled x x.alloc v Layout.mpZpos)
    (hv : v ≤ (bnd P - 1) * (bnd P - 1)) : x.used ≤ 2 * P.used :=
  used_le_of_lt h.valid (by rw [h.mag]; exact sq_lt (bnd_fit hP hP0) hv)

theorem mu_used (hP : P.Valid) (hP0 : 0 < P.mag) (h : ReduceSetupPost P mu) : P.used ≤ mu.used ∧ mu.used ≤ P.used + 2 :=
  ReduceStepG.setup_used hP hP0 h

/-! ## `M[1]`, `res` -/

/-- `mp_mod(G, P, &M[1])`. -/
theorem m1 {M1 : MpInt} (hG : G.Valid) (hP : P.Valid) (hPs : P.sign = Layout.mpZpos) (hP0 : 0 < P.mag)
    (h : ModPost G P M1) : Rs (bnd P) P.used M1 (base G P) :=
  m1_mod hG hP hPs hP0 (by unfold bnd; omega) (bnd_fit hP hP0) h

/-- `mp_init(&res)`, `mp_set(&res, 1uL)`. -/
theorem res1 {res' : MpInt} (hP : P.Valid) (hP0 : 0 < P.mag) (h : SetPost (MpInt.zeroN defPrec) (1 % radix) res') :
    Rs (bnd P) P.used res' 1 :=
  res_one (MpInt.zeroN_valid (by decide)).toShape (by decide) (by unfold bnd; omega) (bnd_fit hP hP0) h

/-! ## The result -/

/-- `mp_exch(&res, Y)`: `Y` gets `res`. -/
theorem fin (h : Done (run (redP P.mag) X (base G P) 1) (bnd P) P.used res) : SExptmodPost G X P res :=
  have a := h.winRes
  ⟨a.valid, a.magN, a.zpos (by omega)⟩

/-- What `s_mp_exptmod(G, X, P, Y, redmode)` returns (allocations not failing), as `mp_exptmod`
consumes it: for `redmode = 0` and `P = 0`, `MP_VAL` from `mp_reduce_setup`, `Y` untouched; for
`P > 0`, `MP_OKAY` and the Post. -/
structure Out (G X P Y Y' : MpInt) (redmode : Nat) (ret : Int) : Prop where
  zero : redmode = 0 → P.mag = 0 → ret = Layout.mpVal ∧ Y' = Y
  pos : 0 < P.mag → ret = Layout.mpOkay ∧ SExptmodPost G X P Y'

/-- `P > 0`: the run, `MP_OKAY`. -/
theorem out_ok {redmode : Nat} (hP0 : 0 < P.mag) (h : SExptmodPost G X P Y') :
    Out G X P Y Y' redmode Layout.mpOkay :=
  ⟨fun _ e => absurd e (by omega), fun _ => ⟨rfl, h⟩⟩

/-- `redmode == 0`, `P = 0`: `mp_reduce_setup` fails, `goto LBL_MU` (`Y` untouched). -/
theorem out_setup {ret : Int} (hz : P.mag = 0) (hs : ReduceSetupOut P mu ret) : Out G X P Y Y 0 ret :=
  ⟨fun _ _ => ⟨hs.zero hz, rfl⟩, fun h => absurd hz (by omega)⟩

end Tom.SMpExptmodStep
