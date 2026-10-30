import Tom.Spec.Canon
import Tom.Spec.Reduce
import Tom.Spec.Init
import Tom.Spec.SMpSqrG5Step

/-!
# `s_mp_mul_high_digs`'s rows: the model steps

The slow path of `bn_s_mp_mul_high_digs.c` over the temporary `t`'s digit function `f`
(`D = a->used + b->used + 1` digits used): row `ix` adds `a_ix * Σ_{digs - ix ≤ iy < b->used}
b_iy radix^(ix + iy)` column by column from position `digs` (the inner loop), then stores its
carry at `max digs (ix + b->used)` (`*tmpt = u`; the slot is still zero). After the rows `t`
holds `Reduce.highRows` (`Reduce.highProd_rows`: the high product). The three cuts' value
premises (`OH` outer head, `IH` inner head, `PH` the carry store), one lemma per row that
changes them, in the forms the rows (`mhdigsg.rows.json`) write, and the result after
`mp_clamp` (`MulHighPost`).
-/

namespace Tom.MulHighStep

open MpInt
open Mont (upd natUpTo_upd)
open Reduce (highRows rowHigh)
open SqrStepG5 (store)

theorem eR : radix = 268435456 := rfl

/-! ## The cuts' value premises -/

/-- At the outer head (`ix`): rows below `ix` added; zero from the next carry slot on. -/
structure OH (da db : Nat → Nat) (ub dg D : Nat) (f : Nat → Nat) (ix : Nat) : Prop where
  dig : ∀ j, f j < radix
  zero : ∀ j, max dg (ix + ub) ≤ j → f j = 0
  val : natUpTo f D = highRows da db ub dg ix

/-- At the inner head (`ix`, `iy` from `digs - ix`, the carry `c` into position `ix + iy`). -/
structure IH (da db : Nat → Nat) (ub dg D : Nat) (f : Nat → Nat) (ix iy c : Nat) : Prop where
  dig : ∀ j, f j < radix
  zero : ∀ j, ix + ub ≤ j → f j = 0
  val : natUpTo f D + radix ^ (ix + iy) * c = highRows da db ub dg ix + radix ^ ix * (da ix * rowHigh db iy (dg - ix))
  c_lt : c < radix

/-- At the carry store (`*tmpt = u` into position `k`). -/
structure PH (da db : Nat → Nat) (ub dg D : Nat) (f : Nat → Nat) (ix k c : Nat) : Prop where
  dig : ∀ j, f j < radix
  zero : ∀ j, k ≤ j → f j = 0
  val : natUpTo f D + radix ^ k * c = highRows da db ub dg (ix + 1)
  c_lt : c < radix
  k_lt : k < D
  k_le : k ≤ max dg (ix + ub)
  /-- A carry at or above the next slot is the empty rows' zero. -/
  cz : max dg (ix + 1 + ub) ≤ k → c = 0

section
variable {da db : Nat → Nat} {ub dg D : Nat} {f : Nat → Nat}

theorem rowHigh_self (s : Nat) : rowHigh db s s = 0 := by
  unfold rowHigh
  rw [natUpTo_congr s (e := fun _ => 0) (fun j hj => if_neg (by omega)), natUpTo_zero_fun]

theorem rowHigh_succ {s iy : Nat} (h : s ≤ iy) : rowHigh db (iy + 1) s = rowHigh db iy s + radix ^ iy * db iy := by
  unfold rowHigh; simp only [natUpTo, if_pos h]

theorem rowHigh_le {s ub : Nat} (h : ub ≤ s) : rowHigh db ub s = 0 := by
  unfold rowHigh
  rw [natUpTo_congr ub (e := fun _ => 0) (fun j hj => if_neg (by omega)), natUpTo_zero_fun]

theorem OH.zeroN (N : Nat) : OH da db ub dg D (MpInt.zeroN N).digit 0 :=
  { dig := fun j => by rw [MpInt.zeroN_digit]; exact radix_pos
    zero := fun j _ => MpInt.zeroN_digit N j
    val := by
      rw [natUpTo_congr D (e := fun _ => 0) (fun j _ => MpInt.zeroN_digit N j), natUpTo_zero_fun]; rfl }

theorem OH.cast {i j : Nat} (h : OH da db ub dg D f i) (e : i = j) : OH da db ub dg D f j := e ▸ h

/-- No columns (`o0`: `digs - ix ≥ b->used`): the row's carry `0` into position `digs`. -/
theorem OH.skip {ix : Nat} (h : OH da db ub dg D f ix) (hn : ub ≤ dg - ix) (hix : ix ≤ dg) (hD : dg < D) :
    PH da db ub dg D f ix dg 0 :=
  { dig := h.dig, c_lt := radix_pos, k_lt := hD, k_le := by omega, cz := fun _ => rfl
    zero := fun j hj => h.zero j (by omega)
    val := by
      show _ = highRows da db ub dg ix + radix ^ ix * (da ix * rowHigh db ub (dg - ix))
      rw [rowHigh_le hn, h.val]; simp }

/-- The inner loop's set-up (`o1`: `digs - ix < b->used`). -/
theorem OH.row {ix : Nat} (h : OH da db ub dg D f ix) (hn : dg - ix < ub) (hix : ix ≤ dg) :
    IH da db ub dg D f ix (dg - ix) 0 :=
  { dig := h.dig, c_lt := radix_pos
    zero := fun j hj => h.zero j (by omega)
    val := by rw [rowHigh_self, h.val]; simp }

/-- One column (`iw`, `ib`): `r := t[ix + iy] + a_ix b_iy + u`, `t[ix + iy] := r mod R`, `u := r / R`. -/
theorem IH.step {ix iy c : Nat} (h : IH da db ub dg D f ix iy c) (hda : ∀ j, da j < radix)
    (hdb : ∀ j, db j < radix) (hk : ix + iy < D) (hs : dg - ix ≤ iy) (hiy : iy < ub) :
    IH da db ub dg D (upd f (ix + iy) ((db iy * da ix + f (ix + iy) + c) % 268435456)) ix (iy + 1)
      ((db iy * da ix + f (ix + iy) + c) / 268435456) :=
  { dig := fun j => by
      unfold upd; split
      · exact Nat.mod_lt _ (by decide)
      · exact h.dig j
    zero := fun j hj => by rw [Mont.upd_ne f _ (by omega)]; exact h.zero j hj
    val := by
      have hs' := store f hk (db iy * da ix + c)
      have hv := h.val
      have e1 : radix ^ ix * (da ix * rowHigh db (iy + 1) (dg - ix)) =
          radix ^ ix * (da ix * rowHigh db iy (dg - ix)) + radix ^ (ix + iy) * (db iy * da ix) := by
        rw [rowHigh_succ hs, Nat.mul_add, Nat.mul_add, Nat.pow_add]; congr 1; ac_rfl
      have e2 : radix ^ (ix + iy) * (db iy * da ix + c) =
          radix ^ (ix + iy) * (db iy * da ix) + radix ^ (ix + iy) * c := Nat.mul_add _ _ _
      rw [show db iy * da ix + f (ix + iy) + c = f (ix + iy) + (db iy * da ix + c) by omega,
        show ix + (iy + 1) = ix + iy + 1 by omega, e1]
      rw [Nat.mul_comm ((f (ix + iy) + (db iy * da ix + c)) / radix)] at hs'
      rw [eR] at hs' hv e2 ⊢
      omega
    c_lt := by
      have e1 := hdb iy; have e2 := h.dig (ix + iy); have e3 := hda ix; have e4 := h.c_lt
      rw [eR] at e1 e2 e3 e4 ⊢
      have e5 : db iy * da ix ≤ 268435455 * 268435455 := Nat.mul_le_mul (by omega) (by omega)
      exact (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega) }

/-- The row's last column (`ix`): its carry goes to position `ix + b->used`. -/
theorem IH.exit {ix iy c : Nat} (h : IH da db ub dg D f ix iy c) (hda : ∀ j, da j < radix)
    (hdb : ∀ j, db j < radix) (hk : ix + iy < D) (hs : dg - ix ≤ iy) (hiy : iy + 1 = ub) (hD : ix + ub < D) :
    PH da db ub dg D (upd f (ix + iy) ((db iy * da ix + f (ix + iy) + c) % 268435456)) ix (ix + ub)
      ((db iy * da ix + f (ix + iy) + c) / 268435456) :=
  have h' := IH.step h hda hdb hk hs (by omega)
  { dig := h'.dig, c_lt := h'.c_lt, k_lt := hD, k_le := by omega, cz := fun h => absurd h (by omega)
    zero := h'.zero
    val := by
      have := h'.val; rw [hiy] at this; rw [this]; rfl }

/-- `*tmpt = u` (`s1`, `s2`): the next row. -/
theorem PH.store {ix k c : Nat} (h : PH da db ub dg D f ix k c) : OH da db ub dg D (upd f k c) (ix + 1) :=
  { dig := fun j => by
      unfold upd; split
      · exact h.c_lt
      · exact h.dig j
    zero := fun j hj => by
      unfold upd; split
      · next he => subst he; exact h.cz hj
      · exact h.zero j (by have := h.k_le; omega)
    val := by
      have e := natUpTo_upd f k c D h.k_lt
      rw [h.zero k (Nat.le_refl _), Nat.mul_zero, Nat.add_zero] at e
      have := h.val; omega }

end

/-! ## The result -/

/-- `t` as `mp_clamp` is handed it: `used = D`, the digits `f`. -/
def tOf (D N : Nat) (f : Nat → Nat) : MpInt := MpInt.ofDigits D N Layout.mpZpos f

theorem tOf_shape {da db : Nat → Nat} {ub dg D N ix : Nat} {f : Nat → Nat} (h : OH da db ub dg D f ix)
    (hD : dg ≤ D) (hix : ix + ub ≤ D) (hN : D ≤ N) (hN' : N < 2 ^ 31) : (tOf D N f).Shape :=
  ofDigits_shape hN hN' (fun j _ => h.dig j) fun j hj _ => h.zero j (by omega)

/-- **The high product**: after the last row and `mp_clamp`. -/
theorem high_fin {a b t' : MpInt} {dg N : Nat} {f : Nat → Nat}
    (h : OH a.digit b.digit b.used dg (a.used + b.used + 1) f a.used) (hdg : dg ≤ a.used + b.used)
    (hN : a.used + b.used + 1 ≤ N) (hN' : N < 2 ^ 31) (hc : ClampPost (tOf (a.used + b.used + 1) N f) t') :
    Reduce.MulHighPost a b t' dg ∧ t'.alloc = N := by
  have hs := tOf_shape h (by omega) (by omega) hN hN'
  obtain ⟨hv, hm⟩ := hc.spec hs (Or.inl rfl)
  have hmag : (tOf (a.used + b.used + 1) N f).mag = highRows a.digit b.digit b.used dg a.used := by
    show natUpTo (tOf _ N f).digit (a.used + b.used + 1) = _
    rw [natUpTo_congr _ (e := f) (fun j hj => by
        show (MpInt.ofDigits _ N _ f).digit j = f j; rw [MpInt.ofDigits_digit, if_pos (by omega)]), h.val]
  refine ⟨⟨hv, hm.trans hmag, ?_⟩, hc.alloc⟩
  rw [hc.sign]; split <;> rfl

end Tom.MulHighStep
