import Tom.Spec.SMpExptmodStep
import Tom.Spec.CopyGStep

/-!
# `s_mp_exptmod` by mode: `redux`'s relation, `mu`, the run and the result

`Tom/Spec/SMpExptmodStep.lean` states the two reductions (`rx_barrett`, `rx_2kL`); the machine's loop
is one for both modes (`redux` a function pointer, `s6`), so its invariants are stated once over the
mode `md`:

* `rxRP md x n mu x'`: what `redux(x, n, mu)` leaves in mode `md` (`mp_reduce` / `mp_reduce_2k_l`);
* `MuOk P md mu`: `mu` from the mode's setup; `rxS`: `redux` a transfer on residues below
  `bnd P` in both modes (both reduce modulo `P`: one value function `redP P`);
* `runS G X P`: the run of `Tom/Spec/WindowStep.lean` (`M[1] = G mod P`, `res = 1`); `finS`: the
  result `Out … MP_OKAY` from the run's `Done`.
-/

namespace Tom.SMpExptmodStep

open MpInt Ledger Window WindowStep Exptmod Mont Reduce

/-- What `redux(x, n, mu)` leaves in mode `md`. -/
def rxRP : Nat → MpInt → MpInt → MpInt → MpInt → Prop
  | 0, x, n, mu, x' => ReducePost x n mu x'
  | _, x, n, mu, x' => Reduce2kPost x n mu.mag x'

/-- `mu` as the mode's setup leaves it. -/
structure MuOk (P : MpInt) (md : Nat) (mu : MpInt) : Prop where
  b0 : md = 0 → ReduceSetupPost P mu
  b1 : md ≠ 0 → Setup2kLPost P mu

theorem MuOk.valid {P mu : MpInt} {md : Nat} (h : MuOk P md mu) : mu.Valid := by
  rcases md with _ | md
  · exact (h.b0 rfl).valid
  · exact (h.b1 (by omega)).valid

/-- `mu` is positive (Barrett's `radix^(2 um) / P ≥ radix^um`, `2^p - P > 0`). -/
theorem MuOk.mag_pos {P mu : MpInt} {md : Nat} (h : MuOk P md mu) (hP : P.Valid) (hP0 : 0 < P.mag) : 0 < mu.mag := by
  rcases md with _ | md
  · have := ReduceSetupPost.ge hP.toShape hP0 (h.b0 rfl)
    exact Nat.lt_of_lt_of_le (Nat.pow_pos radix_pos) this
  · have := (h.b1 (by omega)).mag; have := nbits_lt P.mag; omega

/-- **`redux` in both modes** is a transfer on residues below `bnd P`. -/
theorem rxS {P mu : MpInt} {md : Nat} (hP : P.Valid) (hP0 : 0 < P.mag) (h : MuOk P md mu) :
    Rx (fun x x' => rxRP md x P mu x') (redP P.mag) (bnd P) P.used := by
  rcases md with _ | md
  · exact rx_barrett hP hP0 (h.b0 rfl)
  · exact rx_2kL hP hP0 (h.b1 (by omega))

/-- A product of two residues as `redux` takes it: valid, nonnegative, at most `2 P->used` digits. -/
structure Prd (P x : MpInt) : Prop where
  valid : x.Valid
  sign : x.sign = Layout.mpZpos
  used : x.used ≤ 2 * P.used

theorem Prd.of {P x : MpInt} {v : Nat} (hP : P.Valid) (hP0 : 0 < P.mag) (h : Settled x x.alloc v Layout.mpZpos)
    (hv : v ≤ (bnd P - 1) * (bnd P - 1)) : Prd P x :=
  ⟨h.valid, by rw [h.sign]; split <;> rfl, prod_used hP hP0 h hv⟩

/-- `mp_sqr(&x, &x)` of a residue. -/
theorem Prd.sqr {P x x1 : MpInt} {v : Nat} (hP : P.Valid) (hP0 : 0 < P.mag) (h : Rs (bnd P) P.used x v)
    (hs : SqrPost x x1) : Prd P x1 :=
  Prd.of hP hP0 (xfer_sqr h.val hs) (mul_le_sq h.aux h.aux)

/-- `mp_mul(&x, &e, &x1)` of two residues. -/
theorem Prd.mul {P x e x1 : MpInt} {v m : Nat} (hP : P.Valid) (hP0 : 0 < P.mag) (h : Rs (bnd P) P.used x v)
    (he : Rs (bnd P) P.used e m) (hm : MulPost x e x1) : Prd P x1 :=
  Prd.of hP hP0 (xfer_mul h.val he.val hm) (mul_le_sq h.aux he.aux)

/-- `mp_copy(&M[1], &M[2^(w-1)])` into `mp_init`'s `M[2^(w-1)]`, grown to `M[1]`'s size: the squarings
start (`tab_copy` for the growing copy). -/
theorem tab_copyG {B U v : Nat} {red : Nat → Nat} {m1 e : MpInt} (h1 : Rs B U m1 v)
    (hc : CopyPost m1 (copyIn m1 (MpInt.zeroN defPrec)) e) : Rs B U e (sqIter red 0 v) := by
  obtain ⟨hv, -, hval⟩ := hc.specG h1.valid (MpInt.zeroN_valid (by decide)).toShape
  exact ⟨hv, Nat.zero_le _, by rw [hc.used]; exact h1.used, hval.trans h1.val, h1.aux⟩

/-- The upper half below `x` does not see entry `x` (`M[x]` written before its `redux`). -/
theorem TUp.set_hi {B U w v x : Nat} {red : Nat → Nat} {Mt : Nat → MpInt} {e : MpInt}
    (h : TUp B U w v red Mt x) : TUp B U w v red (setT Mt x e) x where
  one := by
    have := h.lo; have : 1 ≤ 2 ^ (w - 1) := Nat.one_le_two_pow
    show Rs B U (if 1 = x then e else Mt 1) v
    rw [if_neg (by omega)]; exact h.one
  done j hj1 hj2 := by
    show Rs B U (if j = x then e else Mt j) _
    rw [if_neg (by omega)]; exact h.done j hj1 hj2
  lo := h.lo
  hi := h.hi

/-- The run of `s_mp_exptmod`: `M[1] = G mod P`, `res = 1`. -/
abbrev runS (G X P : MpInt) : Run := run (redP P.mag) X (base G P) 1

/-- **The result** (`Y` after `mp_exch(&res, Y)`). -/
theorem finS {G X P Y res : MpInt} {md : Nat} (hP0 : 0 < P.mag) (h : Done (runS G X P) (bnd P) P.used res) :
    Out G X P Y res md Layout.mpOkay :=
  out_ok hP0 (fin h)

end Tom.SMpExptmodStep
