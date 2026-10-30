import Tom.Spec.Canon
import Tom.Spec.Mont
import Tom.Spec.Init
import Tom.Spec.MpIntU

/-!
# `s_mp_mul_digs`'s loops: the model steps

The truncated schoolbook product (`bn_s_mp_mul_digs.c`, HAC 14.12) over `t`'s digit
function `f` (`N` digits allocated, `digs` computed): `Spec/Mul.lean`'s row model
(`schoolT`: the temporary after `ix` rows, `rowStep`: one row, `schoolT_val`: its value)
read column by column. Row `ix` after `iy` columns holds `rowF` (the row's digits
`combaD` at `ix ..< ix + iy`, the earlier rows elsewhere) and carries `combaW`; the
three cuts' value premises (`OH`, `IH`, `PH`) and one lemma per segment that changes
them, stated in the forms the rows (`smdigsg.rows.json`) write.
-/

namespace Tom.MulDigsStep

open MpInt
open Mont (upd)

/-- Row `ix` after `iy` columns over the temporary `T` of the rows before. -/
def rowF (T : Nat → Nat) (x : Nat) (db : Nat → Nat) (ix iy : Nat) : Nat → Nat := fun j =>
  if ix ≤ j ∧ j < ix + iy then combaD (rowCl T x db ix) (j - ix) else T j

/-- At the outer head (`ix`): the rows below `ix` done. -/
structure OH (da db : Nat → Nat) (ub dg N : Nat) (f : Nat → Nat) (ix : Nat) : Prop where
  dig : ∀ j, j < N → f j < radix
  eq : ∀ j, j < N → f j = schoolT da db ub dg ix j

/-- At the inner head (`ix`, `iy`, carry `c`). -/
structure IH (da db : Nat → Nat) (ub dg N : Nat) (f : Nat → Nat) (ix iy c : Nat) : Prop where
  dig : ∀ j, j < N → f j < radix
  eq : ∀ j, j < N → f j = rowF (schoolT da db ub dg ix) (da ix) db ix iy j
  c_eq : c = combaW (rowCl (schoolT da db ub dg ix) (da ix) db ix) iy
  c_lt : c < radix

/-- After the inner loop (`pb = MP_MIN(b->used, digs - ix)` columns), before the last carry. -/
structure PH (da db : Nat → Nat) (ub dg N : Nat) (f : Nat → Nat) (ix c : Nat) : Prop where
  dig : ∀ j, j < N → f j < radix
  eq : ∀ j, j < N → f j = rowF (schoolT da db ub dg ix) (da ix) db ix (min ub (dg - ix)) j
  c_eq : c = combaW (rowCl (schoolT da db ub dg ix) (da ix) db ix) (min ub (dg - ix))
  c_lt : c < radix

section
variable {da db : Nat → Nat} {ub dg N : Nat} {f : Nat → Nat}

theorem eR : radix = 268435456 := rfl

theorem OH.zero : OH da db ub dg N (MpInt.zeroN N).digit 0 :=
  { dig := fun j _ => by rw [MpInt.zeroN_digit]; exact radix_pos
    eq := fun j _ => by rw [MpInt.zeroN_digit]; rfl }

theorem OH.cast {i j : Nat} (h : OH da db ub dg N f i) (e : i = j) : OH da db ub dg N f j := e ▸ h

/-- The inner loop's set-up (`o2`, `o3`). -/
theorem OH.start {ix : Nat} (h : OH da db ub dg N f ix) : IH da db ub dg N f ix 0 0 :=
  { dig := h.dig, c_lt := radix_pos, c_eq := rfl
    eq := fun j hj => by rw [h.eq j hj]; simp only [rowF]; rw [if_neg (by omega)] }

/-- No columns (`o0`: `digs ≤ ix`; `o1`: `b->used = 0`). -/
theorem OH.skip {ix : Nat} (h : OH da db ub dg N f ix) (hn : min ub (dg - ix) = 0) : PH da db ub dg N f ix 0 :=
  { dig := h.dig, c_lt := radix_pos, c_eq := by rw [hn]; rfl
    eq := fun j hj => by rw [h.eq j hj, hn]; simp only [rowF]; rw [if_neg (by omega)] }

/-- One column (`il`, `ilx`). -/
theorem IH.step {ix iy c : Nat} (h : IH da db ub dg N f ix iy c) (ha : ∀ j, da j < radix)
    (hb : ∀ j, db j < radix) (hk : ix + iy < N) :
    IH da db ub dg N (upd f (ix + iy) ((db iy * da ix + f (ix + iy) + c) % 268435456)) ix (iy + 1)
      ((db iy * da ix + f (ix + iy) + c) / 268435456) := by
  have hT := (schoolT_val (ub := ub) (digs := dg) ha hb ix).1
  have hf : f (ix + iy) = schoolT da db ub dg ix (ix + iy) := by
    rw [h.eq _ hk]; simp only [rowF]; rw [if_neg (by omega)]
  have hv : db iy * da ix + f (ix + iy) + c =
      combaW (rowCl (schoolT da db ub dg ix) (da ix) db ix) iy + rowCl (schoolT da db ub dg ix) (da ix) db ix iy := by
    rw [hf, ← h.c_eq]; simp only [rowCl]; rw [Nat.mul_comm (db iy)]; omega
  refine { dig := fun j hj => ?_, eq := fun j hj => ?_, c_eq := ?_, c_lt := ?_ }
  · unfold upd; split
    · exact Nat.mod_lt _ (by decide)
    · exact h.dig j hj
  · unfold upd; split
    · next he =>
      subst he; simp only [rowF]; rw [if_pos (by omega), show ix + iy - ix = iy by omega, hv]; rfl
    · next he =>
      rw [h.eq j hj]; simp only [rowF]
      by_cases h1 : ix ≤ j ∧ j < ix + iy
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]
  · rw [hv]; rfl
  · rw [hv]; exact rowW_lt hT (ha ix) hb (iy + 1)

/-- The row's last column done. -/
theorem IH.exit {ix iy c : Nat} (h : IH da db ub dg N f ix iy c) (hiy : iy = min ub (dg - ix)) :
    PH da db ub dg N f ix c := by
  subst hiy; exact ⟨h.dig, h.eq, h.c_eq, h.c_lt⟩

/-- The carry stored below `digs` (`s1`, `s2`): the next row. -/
theorem PH.store {ix c k : Nat} (h : PH da db ub dg N f ix c) (hk : k = ix + min ub (dg - ix)) (hlt : k < dg) :
    OH da db ub dg N (upd f k c) (ix + 1) := by
  refine { dig := fun j hj => ?_, eq := fun j hj => ?_ }
  · unfold upd; split
    · exact h.c_lt
    · exact h.dig j hj
  · show _ = rowStep (schoolT da db ub dg ix) (da ix) db ix (min ub (dg - ix)) dg j
    unfold upd rowStep; split
    · next he => subst he; rw [if_neg (by omega), if_pos ⟨hk, by omega⟩, h.c_eq]
    · next he =>
      rw [h.eq j hj]; simp only [rowF]
      by_cases h1 : ix ≤ j ∧ j < ix + min ub (dg - ix)
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1, if_neg (by omega)]

/-- The carry falls at or above `digs` (`s3`, `s4`): the next row. -/
theorem PH.skip {ix c k : Nat} (h : PH da db ub dg N f ix c) (hk : k = ix + min ub (dg - ix)) (hge : dg ≤ k) :
    OH da db ub dg N f (ix + 1) := by
  refine { dig := h.dig, eq := fun j hj => ?_ }
  show _ = rowStep (schoolT da db ub dg ix) (da ix) db ix (min ub (dg - ix)) dg j
  rw [h.eq j hj]; unfold rowStep; simp only [rowF]
  by_cases h1 : ix ≤ j ∧ j < ix + min ub (dg - ix)
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1, if_neg (by omega)]

end

/-! ## The result -/

/-- The temporary is zero from `digs` on. -/
theorem schoolT_hi (da db : Nat → Nat) (ub dg : Nat) : ∀ ix j, dg ≤ j → schoolT da db ub dg ix j = 0
  | 0, _, _ => rfl
  | ix + 1, j, hj => by
    show rowStep (schoolT da db ub dg ix) (da ix) db ix (min ub (dg - ix)) dg j = 0
    unfold rowStep
    rw [if_neg (by omega), if_neg (by omega)]
    exact schoolT_hi da db ub dg ix j hj

/-- `t` as `mp_clamp` is handed it: `used = digs`, the digits `f`. -/
def tOf (dg N : Nat) (f : Nat → Nat) : MpInt := MpInt.ofDigits dg N Layout.mpZpos f

theorem tOf_shape {da db : Nat → Nat} {ub dg N ix : Nat} {f : Nat → Nat} (h : OH da db ub dg N f ix)
    (hN : dg ≤ N) (hN' : N < 2 ^ 31) : (tOf dg N f).Shape :=
  ofDigits_shape hN hN' h.dig fun j h1 h2 => by rw [h.eq j h2]; exact schoolT_hi da db ub dg ix j h1

/-- **The truncated product**: after the last row and `mp_clamp`. -/
theorem mul_fin {a b t' : MpInt} {dg N : Nat} {f : Nat → Nat} (ha : a.ShapeU) (hb : b.ShapeU)
    (h : OH a.digit b.digit b.used dg N f a.used) (hN : dg ≤ N) (hN' : N < 2 ^ 31)
    (hc : ClampPost (tOf dg N f) t') :
    t'.Valid ∧ t'.mag = (a.mag * b.mag) % radix ^ dg ∧ t'.alloc = N ∧ t'.sign = Layout.mpZpos := by
  obtain ⟨hv, hm⟩ := hc.spec (tOf_shape h hN hN') (Or.inl rfl)
  have hmag : (tOf dg N f).mag = (a.mag * b.mag) % radix ^ dg := by
    show natUpTo (tOf dg N f).digit dg = _
    rw [natUpTo_congr dg (e := schoolT a.digit b.digit b.used dg a.used) (fun j hj => by
        show (MpInt.ofDigits _ N _ f).digit j = _
        rw [MpInt.ofDigits_digit, if_pos (by omega), h.eq j (by omega)])]
    exact (schoolT_val ha.digit_lt hb.digit_lt a.used).2.2
  refine ⟨hv, hm.trans hmag, hc.alloc, ?_⟩
  rw [hc.sign]; split <;> rfl

end Tom.MulDigsStep
